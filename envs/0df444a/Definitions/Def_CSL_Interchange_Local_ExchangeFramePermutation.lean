-- Prove2me | Definitions.Def_CSL_Interchange_Local_ExchangeFramePermutation
-- name    : CSL_Interchange_Local_ExchangeFramePermutation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:28:34.349816+00:00
-- url     : https://prove2.me/theorems/4f84ca9a-5eb8-4e0d-bca3-121d95665e17
-- title:
--   Coded sorting library: Interchange / Local / ExchangeFramePermutation
-- statement:
--   Module `CodedSorting.Interchange.Local.ExchangeFramePermutation` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Algebraic inverse identities used by the actual rank-partial-swap
--   machine. The decomposition supplies idempotence, so no extra projection
--   assumption is needed when converting the forward action to machine reads.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Local.ExchangeFramePermutation

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_CompatMatrix
import Definitions.Def_CSL_Circuit_Labels_ProjectionRankDecomposition
import Definitions.Def_CSL_Interchange_Local_PartialSwapExecution
open scoped Fin.NatCast Fin.IntCast Fin.CommRing

section RankPartialSwapAlgebra
/-! Algebraic inverse identities used by the actual rank-partial-swap
machine. The decomposition supplies idempotence, so no extra projection
assumption is needed when converting the forward action to machine reads. -/

set_option autoImplicit false

namespace CSL.Construction.RankPartialSwapAlgebra

open scoped BigOperators Matrix
open TriangularConjugacy ProjectionRankDecomposition

variable {I : Type*} [Fintype I] [LinearOrder I]

local instance doubledDecEq : DecidableEq (I ⊕ₗ I) :=
  (inferInstance : LinearOrder (I ⊕ₗ I)).toDecidableEq

theorem decomposition_idempotent {P : Matrix I I ℚ} (d : RankDecomposition P) :
    P * P = P := by
  calc
    P * P = (∑ i, lineProjection (d.vectors i)) *
        (∑ j, lineProjection (d.vectors j)) := by rw [d.sum_eq]
    _ = ∑ i, lineProjection (d.vectors i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      rw [Finset.sum_eq_single i]
      · exact lineProjection_idempotent _ (normSq_ne_zero _ (d.nonzero i))
      · intro j hj hji
        exact d.projection_orthogonal i j hji.symm
      · intro hn
        exact (hn (Finset.mem_univ i)).elim
    _ = P := d.sum_eq

theorem partialSwap_square (P : Matrix I I ℚ) (hp : P * P = P) :
    partialSwap P * partialSwap P = 1 := by
  unfold partialSwap
  change (Matrix.fromBlocks (1 - P) P P (1 - P) : Matrix (I ⊕ I) (I ⊕ I) ℚ) *
    Matrix.fromBlocks (1 - P) P P (1 - P) = (1 : Matrix (I ⊕ₗ I) (I ⊕ₗ I) ℚ)
  rw [Matrix.fromBlocks_multiply]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hp]
  have hz : (1 : Matrix I I ℚ) - P - P + P + P = 1 := by abel
  have hz' : (1 : Matrix I I ℚ) - P - (P - P) + P = 1 := by abel
  rw [← CSL.CompatMatrix.fromBlocks_one_lex]
  congr 1 <;> first | (simp only [hz, hz']) | abel | (simp; abel) | simp

theorem decomposition_partialSwap_square {P : Matrix I I ℚ} (d : RankDecomposition P) :
    partialSwap P * partialSwap P = 1 :=
  partialSwap_square P (decomposition_idempotent d)

end CSL.Construction.RankPartialSwapAlgebra

#print axioms CSL.Construction.RankPartialSwapAlgebra.decomposition_idempotent
#print axioms CSL.Construction.RankPartialSwapAlgebra.decomposition_partialSwap_square
end RankPartialSwapAlgebra

section RankPartialSwapExecution
/-! Exact-rank composition of concrete partial-swap scan programs. A single
joint rational family contains every line factor and the full target. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CSL.Construction.RankPartialSwapExecution

open MatrixFactorization ScanProgram ScanProgramLift CommonAddressLayout
open PartialSwapScan PartialSwapExecution ProjectionRankDecomposition

noncomputable section

section Products
variable {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
variable {A : K → Matrix I I ℚ}

theorem preserves_list_product (F : SpecializedFamily A) (l : List K) (target : K)
    (h : (l.map A).prod = A target) (f : ℕ) :
    (l.map (F.matrix f)).prod = F.matrix f target := by
  have hlocal : (l.map F.coefficients).prod = F.coefficients target := by
    apply F.rational_embedding_injective
    simpa only [map_list_prod,List.map_map,Function.comp_def,F.lift_correct] using h
  have hred := congrArg ((F.reduce f).mapMatrix) hlocal
  first
  | exact hred
  | (have h_sx := hred; simp only [map_list_prod,List.map_map,Function.comp_def,SpecializedFamily.matrix] at h_sx ⊢; exact h_sx)
  | (have h_sx := hred; simp only [map_list_prod,List.map_map,Function.comp_def,SpecializedFamily.matrix] at h_sx; exact h_sx)
  | (simp only [map_list_prod,List.map_map,Function.comp_def,SpecializedFamily.matrix]; exact hred)

end Products

section Flatten
variable {J : Type*} {m Q Pref G S : ℕ} [NeZero Q]
local instance doubledDecEqFlatten : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq

theorem matrixAddress_one (a : Addr (Fin m) Pref Q G S) : matrixAddress 1 a = a := by
  cases a
  simp only [matrixAddress,joinedVector]
  erw [CSL.CompatMatrix.one_mulVec_lex]
  rfl

theorem flatten_encoded
    (ps : J → List (Pass (Volume (Fin m) Pref Q G S)))
    (M : J → Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) (Fin Q))
    (hps : ∀ i (a : Addr (Fin m) Pref Q G S),
      destination (ps i) (longLayout a) = longLayout (matrixAddress (M i) a))
    (l : List J) (a : Addr (Fin m) Pref Q G S) :
    destination ((l.map ps).flatten) (longLayout a) =
      longLayout (matrixAddress ((l.reverse.map M).prod) a) := by
  induction l generalizing a with
  | nil => simp only [List.map_nil,List.flatten_nil,List.reverse_nil,List.prod_nil,
      destination,Equiv.refl_apply,matrixAddress_one]
  | cons i l ih =>
    rw [List.map_cons,List.flatten_cons,destination_append,Equiv.trans_apply,hps,ih]
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      List.prod_append,List.prod_cons,List.prod_nil,mul_one,matrixAddress_mul]

end Flatten

section FlattenExecution
variable {J Value : Type*} [Inhabited Value] {V block : ℕ} {hb : 0 < block}

theorem flatten_execution (ps : J → List (Pass V)) (charge : J → ℕ)
    (hps : ∀ i (input : Fin V → Value),
      ∃ cost, Execution block hb (ps i) input cost ∧ cost ≤ charge i)
    (l : List J) (input : Fin V → Value) :
    ∃ cost, Execution block hb ((l.map ps).flatten) input cost ∧ cost ≤ (l.map charge).sum := by
  induction l generalizing input with
  | nil => exact ⟨0,Execution.nil input,Nat.le_refl 0⟩
  | cons i l ih =>
    obtain ⟨headCost,hhead,hh⟩ := hps i input
    obtain ⟨tailCost,htail,ht⟩ := ih (eval (ps i) input)
    refine ⟨headCost+tailCost,?_,?_⟩
    · simpa only [List.map_cons,List.flatten_cons] using execution_append hhead htail
    · simpa only [List.map_cons,List.sum_cons] using Nat.add_le_add hh ht

end FlattenExecution

/-- A visible recursive call boundary. Both sides are ordinary scan lists;
the only recursive call in this block is the selected `childIndex`. -/
structure CallBlock (J : Type*) (V : ℕ) where
  before : List (Pass V)
  childIndex : J
  after : List (Pass V)

def CallBlock.compile {J : Type*} {V : ℕ} (children : J → List (Pass V))
    (b : CallBlock J V) : List (Pass V) := b.before ++ children b.childIndex ++ b.after

section Family
variable {m : ℕ}
local instance doubledDecEq : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq

structure Support (u : Fin m → ℚ) where
  first : Fin m
  last : Fin m
  first_nonzero : u first ≠ 0
  last_nonzero : u last ≠ 0
  before_zero : ∀ r, r < first → u r = 0
  after_zero : ∀ r, last < r → u r = 0

def support (u : Fin m → ℚ) (hu : u ≠ 0) : Support u := by
  apply Classical.choice
  obtain ⟨s,t,hs,ht,hbefore,hafter⟩ := TriangularConjugacy.exists_support_extremes u hu
  exact ⟨⟨s,t,hs,ht,hbefore,hafter⟩⟩

variable {P : Matrix (Fin m) (Fin m) ℚ} (d : RankDecomposition P)

abbrev supports (i : Fin P.rank) : Support (d.vectors i) := support (d.vectors i) (d.nonzero i)

abbrev FamilyIndex (P : Matrix (Fin m) (Fin m) ℚ) := Option (Fin P.rank × (Bool × Bool))

/-- `none` is the target. Every other entry belongs to a line's four-matrix
conjugacy family. All entries are reduced by one specialization. -/
def family : FamilyIndex P → Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) ℚ
  | none => TriangularConjugacy.partialSwap P
  | some (i,tag) => lineFamily (d.vectors i) (supports d i).first (supports d i).last tag

variable (F : SpecializedFamily (family d)) (f : ℕ)
local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

abbrev componentFamily (i : Fin P.rank) :
    SpecializedFamily (lineFamily (d.vectors i) (supports d i).first (supports d i).last) :=
  restrictFamily F (fun tag => some (i,tag)) (fun _ => id) (fun _ => id)

@[simp] theorem component_prime (i : Fin P.rank) : (componentFamily d F i).prime = F.prime := rfl

@[simp] theorem componentFullFinMatrix (i : Fin P.rank) (tag : Bool × Bool) :
    fullFinMatrix (componentFamily d F i) f tag = fullFinMatrix F f (some (i,tag)) := rfl

theorem rational_reverse_product :
    (((List.finRange P.rank).reverse).map (fun i => family d (some (i,(false,false))))).prod =
      family d none := by
  simpa only [family,lineFamily,RankDecomposition.factors,List.ofFn_eq_map,List.map_reverse] using
    d.factors_reverse_prod

theorem finite_reverse_product :
    (((List.finRange P.rank).reverse).map
      (fun i => fullFinMatrix F f (some (i,(false,false))))).prod = fullFinMatrix F f none := by
  have h := preserves_list_product F
    (((List.finRange P.rank).reverse).map (fun i => some (i,(false,false)))) none
    (by simpa only [List.map_map,Function.comp_def] using rational_reverse_product d) f
  have hfin := congrArg ((ZMod.finEquiv (F.prime^f)).symm.toRingHom.mapMatrix) h
  first
  | exact hfin
  | (have h_sx := hfin; simp only [map_list_prod,List.map_map,Function.comp_def,fullFinMatrix,
    RingHom.mapMatrix_apply,RingEquiv.coe_toRingHom] at h_sx ⊢; exact h_sx)
  | (have h_sx := hfin; simp only [map_list_prod,List.map_map,Function.comp_def,fullFinMatrix,
    RingHom.mapMatrix_apply,RingEquiv.coe_toRingHom] at h_sx; exact h_sx)
  | (simp only [map_list_prod,List.map_map,Function.comp_def,fullFinMatrix,
    RingHom.mapMatrix_apply,RingEquiv.coe_toRingHom]; exact hfin)

/-- The common specialization preserves the target partial swap's exact
involution identity, for every power of the chosen prime. -/
theorem finite_target_square :
    fullFinMatrix F f none * fullFinMatrix F f none = 1 := by
  have hred := F.preserves_product_one none none
    (RankPartialSwapAlgebra.decomposition_partialSwap_square d) f
  have hfin := congrArg ((ZMod.finEquiv (F.prime^f)).symm.toRingHom.mapMatrix) hred
  first
  | exact hfin
  | (have h_sx := hfin; simp only [map_mul, map_one, fullFinMatrix, RingHom.mapMatrix_apply,
    RingEquiv.coe_toRingHom] at h_sx ⊢; exact h_sx)
  | (have h_sx := hfin; simp only [map_mul, map_one, fullFinMatrix, RingHom.mapMatrix_apply,
    RingEquiv.coe_toRingHom] at h_sx; exact h_sx)
  | (simp only [map_mul, map_one, fullFinMatrix, RingHom.mapMatrix_apply,
    RingEquiv.coe_toRingHom]; exact hfin)

variable (Pref G S : ℕ) (hG : 0 < G) (hS : 0 < S)
variable (children : Fin P.rank → List (Pass (Volume (Fin m) Pref (F.prime^f) G S)))

def componentProgram (i : Fin P.rank) : List (Pass (Volume (Fin m) Pref (F.prime^f) G S)) :=
  lineProgram (d.vectors i) (supports d i).first (supports d i).last (componentFamily d F i) f
    (supports d i).first_nonzero (supports d i).last_nonzero
    (supports d i).before_zero (supports d i).after_zero Pref G S hG hS (children i)

def blocks : List (List (Pass (Volume (Fin m) Pref (F.prime^f) G S))) :=
  (List.finRange P.rank).map (componentProgram d F f Pref G S hG hS children)

/-- Every block contains its indexed supplied child once. There are exactly
`P.rank` blocks, with no auxiliary recursive calls in their scans. -/
def program : List (Pass (Volume (Fin m) Pref (F.prime^f) G S)) :=
  (blocks d F f Pref G S hG hS children).flatten

theorem blocks_length : (blocks d F f Pref G S hG hS children).length = P.rank := by
  simp only [blocks,List.length_map,List.length_finRange]

def componentPlan (i : Fin P.rank) : CallBlock (Fin P.rank) (Volume (Fin m) Pref (F.prime^f) G S) :=
  let h := lineFamily_properties (d.vectors i) (supports d i).first (supports d i).last
    (supports d i).first_nonzero (supports d i).last_nonzero
    (supports d i).before_zero (supports d i).after_zero
  ⟨lowerProgram (componentFamily d F i) f (true,true) h.2.2.1 h.2.2.2.1 Pref G S hG hS,
    i,lowerProgram (componentFamily d F i) f (false,true) h.1 h.2.1 Pref G S hG hS⟩

def plan : List (CallBlock (Fin P.rank) (Volume (Fin m) Pref (F.prime^f) G S)) :=
  (List.finRange P.rank).map (componentPlan d F f Pref G S hG hS)

theorem componentPlan_compile (i : Fin P.rank) :
    CallBlock.compile children (componentPlan d F f Pref G S hG hS i) =
      componentProgram d F f Pref G S hG hS children i := rfl

/-- The explicit call plan compiles to the very same concrete scan list used
in the semantic and execution theorems. -/
theorem plan_compile :
    ((plan d F f Pref G S hG hS).map (CallBlock.compile children)).flatten =
      program d F f Pref G S hG hS children := by
  simp only [plan,program,blocks,List.map_map,Function.comp_def,componentPlan_compile]

theorem plan_child_indices :
    (plan d F f Pref G S hG hS).map CallBlock.childIndex = List.finRange P.rank := by
  simp only [plan,List.map_map,Function.comp_def,componentPlan,List.map_id_fun]
  exact List.map_id _

theorem child_call_count :
    ((plan d F f Pref G S hG hS).map CallBlock.childIndex).length = P.rank := by
  rw [plan_child_indices,List.length_finRange]

theorem child_calls_nodup :
    ((plan d F f Pref G S hG hS).map CallBlock.childIndex).Nodup := by
  rw [plan_child_indices]
  exact List.nodup_finRange _

theorem componentProgram_encoded (i : Fin P.rank)
    (hc : ∀ a : Addr (Fin m) Pref (F.prime^f) G S,
      destination (children i) (longLayout a) =
        longLayout (SingleCoordinate.shortExchange (supports d i).first (supports d i).last a))
    (a : Addr (Fin m) Pref (F.prime^f) G S) :
    destination (componentProgram d F f Pref G S hG hS children i) (longLayout a) =
      longLayout (matrixAddress (fullFinMatrix F f (some (i,(false,false)))) a) :=
  lineProgram_encoded (d.vectors i) (supports d i).first (supports d i).last (componentFamily d F i) f
    (supports d i).first_nonzero (supports d i).last_nonzero
    (supports d i).before_zero (supports d i).after_zero Pref G S hG hS (children i) hc a

/-- Chronological application gives the reverse matrix product, which the
joint specialization proves is exactly the arbitrary-rank target `D_P`. -/
theorem program_encoded
    (hc : ∀ i (a : Addr (Fin m) Pref (F.prime^f) G S),
      destination (children i) (longLayout a) =
        longLayout (SingleCoordinate.shortExchange (supports d i).first (supports d i).last a))
    (a : Addr (Fin m) Pref (F.prime^f) G S) :
    destination (program d F f Pref G S hG hS children) (longLayout a) =
      longLayout (matrixAddress (fullFinMatrix F f none) a) := by
  rw [program,blocks,flatten_encoded
    (componentProgram d F f Pref G S hG hS children)
    (fun i => fullFinMatrix F f (some (i,(false,false))))
    (fun i => componentProgram_encoded d F f Pref G S hG hS children i (hc i)),
    finite_reverse_product]

def componentConstant (i : Fin P.rank) : ℕ :=
  lowerConstant (A := lineFamily (d.vectors i) (supports d i).first (supports d i).last) (true,true) +
    lowerConstant (A := lineFamily (d.vectors i) (supports d i).first (supports d i).last) (false,true)

def fixedConstant : ℕ := ∑ i : Fin P.rank, componentConstant d i

/-- A uniform bound for a concrete recursive child is consumed only at the
actual array delivered by its inverse-factor scans. -/
theorem componentProgram_execution {Value : Type*} [Inhabited Value]
    (i : Fin P.rank) (childCharge : ℕ) (block : ℕ) (hb : 0 < block)
    (hc : ∀ input : Fin (Volume (Fin m) Pref (F.prime^f) G S) → Value,
      ∃ cost, Execution block hb (children i) input cost ∧ cost ≤ childCharge)
    (input : Fin (Volume (Fin m) Pref (F.prime^f) G S) → Value) :
    ∃ cost, Execution block hb (componentProgram d F f Pref G S hG hS children i) input cost ∧
      cost ≤ componentConstant d i * (Volume (Fin m) Pref (F.prime^f) G S / block+1) +
        childCharge := by
  let h := lineFamily_properties (d.vectors i) (supports d i).first (supports d i).last
    (supports d i).first_nonzero (supports d i).last_nonzero
    (supports d i).before_zero (supports d i).after_zero
  obtain ⟨childCost,hchild,hcost⟩ := hc
    (eval (lowerProgram (componentFamily d F i) f (true,true) h.2.2.1 h.2.2.2.1
      Pref G S hG hS) input)
  obtain ⟨cost,he,hbound⟩ := lineProgram_execution (d.vectors i)
    (supports d i).first (supports d i).last (componentFamily d F i) f
    (supports d i).first_nonzero (supports d i).last_nonzero
    (supports d i).before_zero (supports d i).after_zero
    Pref G S hG hS (children i) input block hb childCost hchild
  exact ⟨cost,he,hbound.trans (Nat.add_le_add_left hcost _)⟩

/-- Real executions are chained through their actual intermediate arrays.
The recursive charge is the sum of exactly one charge for each rank index. -/
theorem program_execution {Value : Type*} [Inhabited Value]
    (childCharge : Fin P.rank → ℕ) (block : ℕ) (hb : 0 < block)
    (hc : ∀ i (input : Fin (Volume (Fin m) Pref (F.prime^f) G S) → Value),
      ∃ cost, Execution block hb (children i) input cost ∧ cost ≤ childCharge i)
    (input : Fin (Volume (Fin m) Pref (F.prime^f) G S) → Value) :
    ∃ cost, Execution block hb (program d F f Pref G S hG hS children) input cost ∧
      cost ≤ fixedConstant d * (Volume (Fin m) Pref (F.prime^f) G S / block+1) +
        ∑ i, childCharge i := by
  obtain ⟨cost,he,hbound⟩ := flatten_execution
    (componentProgram d F f Pref G S hG hS children)
    (fun i => componentConstant d i*(Volume (Fin m) Pref (F.prime^f) G S/block+1)+childCharge i)
    (fun i => componentProgram_execution d F f Pref G S hG hS children i (childCharge i) block hb (hc i))
    (List.finRange P.rank) input
  refine ⟨cost,he,?_⟩
  rw [←Fin.sum_univ_def,Finset.sum_add_distrib,←Finset.sum_mul] at hbound
  exact hbound

end Family

end
end CSL.Construction.RankPartialSwapExecution
end RankPartialSwapExecution

section ExchangeFramePermutation
/-! Involutive specialized matrices give literal address permutations.
These are the numerical file permutations used by the actual network
executor; their endpoint composition is the ordinary H/D exchange. -/
set_option autoImplicit false
namespace CSL.Construction.ExchangeFramePermutation
open PartialSwapScan PartialSwapExecution RankPartialSwapExecution
open CommonAddressLayout
noncomputable section
variable {m Q : Nat} [NeZero Q]
local instance doubledDecEq : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq

abbrev Mat (m Q : Nat) := Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) (Fin Q)

def addressPerm (M : Mat m Q) (hM : M*M=1) (Pref G S : Nat) :
    Equiv.Perm (Addr (Fin m) Pref Q G S) where
  toFun := matrixAddress M
  invFun := matrixAddress M
  left_inv a := by rw [← matrixAddress_mul, hM, matrixAddress_one]
  right_inv a := by rw [← matrixAddress_mul, hM, matrixAddress_one]

@[simp] theorem addressPerm_apply (M : Mat m Q) (hM : M*M=1) (Pref G S : Nat)
    (a : Addr (Fin m) Pref Q G S) : addressPerm M hM Pref G S a=matrixAddress M a := rfl

@[simp] theorem addressPerm_symm (M : Mat m Q) (hM : M*M=1) (Pref G S : Nat) :
    (addressPerm M hM Pref G S).symm=addressPerm M hM Pref G S := rfl

def numericPerm (M : Mat m Q) (hM : M*M=1) (Pref G S : Nat) :
    Equiv.Perm (Fin (Volume (Fin m) Pref Q G S)) :=
  longLayout.symm.trans ((addressPerm M hM Pref G S).trans longLayout)

@[simp] theorem numericPerm_encoded (M : Mat m Q) (hM : M*M=1) (Pref G S : Nat)
    (a : Addr (Fin m) Pref Q G S) :
    numericPerm M hM Pref G S (longLayout a)=longLayout (matrixAddress M a) := by
  simp only [numericPerm, Equiv.trans_apply, Equiv.symm_apply_apply, addressPerm_apply]

@[simp] theorem numericPerm_symm (M : Mat m Q) (hM : M*M=1) (Pref G S : Nat) :
    (numericPerm M hM Pref G S).symm=numericPerm M hM Pref G S := by
  apply Equiv.ext
  intro y
  rfl

/-- Composition order agrees with the output-to-input convention of the
machine network: decode at N and encode at M. -/
theorem numericPerm_transition (M N R : Mat m Q)
    (hM : M*M=1) (hN : N*N=1) (hR : R*R=1) (hprod : M*N=R)
    (Pref G S : Nat) :
    (numericPerm N hN Pref G S).symm.trans (numericPerm M hM Pref G S) =
      numericPerm R hR Pref G S := by
  apply Equiv.ext
  intro y
  obtain ⟨a, rfl⟩ := longLayout.surjective y
  rw [numericPerm_symm, Equiv.trans_apply, numericPerm_encoded, numericPerm_encoded,
    numericPerm_encoded, ← matrixAddress_mul, hprod]

def bankSwapMatrix : Mat m Q := Matrix.fromBlocks 0 1 1 0

theorem bankSwapMatrix_square : (bankSwapMatrix : Mat m Q)*bankSwapMatrix=1 := by
  have h : (Matrix.fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (Fin Q)) *
      Matrix.fromBlocks 0 1 1 0 = Matrix.fromBlocks 1 0 0 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp
  exact h.trans (CSL.CompatMatrix.fromBlocks_one_lex _)

theorem matrixAddress_bankSwap (Pref G S : Nat) (a : Addr (Fin m) Pref Q G S) :
    matrixAddress bankSwapMatrix a=Address.exchange a := by
  change Address.FullAddress.mk a.prefixCoord
    (fun i => (Matrix.fromBlocks 0 1 1 0).mulVec
      (Sum.elim a.high a.low) (Sum.inl i)) a.gap
    (fun i => (Matrix.fromBlocks 0 1 1 0).mulVec
      (Sum.elim a.high a.low) (Sum.inr i)) a.suffix = _
  simp only [Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
  rfl

def numericExchange (Pref G S : Nat) : Equiv.Perm (Fin (Volume (Fin m) Pref Q G S)) :=
  longLayout.symm.trans (Address.exchangeEquiv.trans longLayout)

@[simp] theorem numericExchange_encoded (Pref G S : Nat) (a : Addr (Fin m) Pref Q G S) :
    numericExchange Pref G S (longLayout a)=longLayout (Address.exchange a) := by
  simp only [numericExchange, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem numericPerm_bankSwap (Pref G S : Nat) :
    numericPerm (bankSwapMatrix : Mat m Q) bankSwapMatrix_square Pref G S =
      numericExchange Pref G S := by
  apply Equiv.ext
  intro y
  obtain ⟨a, rfl⟩ := longLayout.surjective y
  rw [numericPerm_encoded, numericExchange_encoded, matrixAddress_bankSwap]

theorem numericPerm_endpoint (M N : Mat m Q) (hM : M*M=1) (hN : N*N=1)
    (hprod : M*N=bankSwapMatrix) (Pref G S : Nat) :
    (numericPerm N hN Pref G S).symm.trans (numericPerm M hM Pref G S) =
      numericExchange Pref G S := by
  rw [numericPerm_transition M N bankSwapMatrix hM hN bankSwapMatrix_square hprod,
    numericPerm_bankSwap]

#print axioms numericPerm_transition
#print axioms numericPerm_endpoint
end
end CSL.Construction.ExchangeFramePermutation
end ExchangeFramePermutation


