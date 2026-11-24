-- Prove2me | Definitions.Def_CSL_Interchange_Local_PartialSwapExecution
-- name    : CSL_Interchange_Local_PartialSwapExecution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:15:22.357603+00:00
-- url     : https://prove2.me/theorems/1d9f1150-1b0a-482e-bdc6-0b8edaae330b
-- title:
--   Coded sorting library: Interchange / Local / PartialSwapExecution
-- statement:
--   Module `CodedSorting.Interchange.Local.PartialSwapExecution` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Concrete mixed-layout scans for jointly specialized rational lower factors.
--   All restrictions below retain the parent family's prime and reduction maps.
--   The address equalities are literal finite positions, not free permutations.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Local.PartialSwapExecution

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Local_PartialSwapScan
import Definitions.Def_CSL_Circuit_Local_TriangularConjugacy
import Definitions.Def_CSL_Circuit_Framework_TriangularProgramBounds
open scoped Fin.NatCast Fin.IntCast Fin.CommRing

/-! Concrete mixed-layout scans for jointly specialized rational lower factors.
All restrictions below retain the parent family's prime and reduction maps.
The address equalities are literal finite positions, not free permutations. -/

set_option autoImplicit false
namespace CSL.Construction.PartialSwapExecution

open MatrixFactorization ScanProgram ScanProgramLift TriangularStreams
open CommonAddressLayout PartialSwapScan

noncomputable section

section Restriction
variable {K I J T : Type*} [Fintype K] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype T]
variable {A : K → Matrix I I ℚ}

/-- Restriction never chooses another prime: even the coefficient lifts and
the maps to every prime power are exactly the parent family's data. -/
abbrev restrictFamily (F : SpecializedFamily A) (select : T → K)
    (row col : T → J → I) :
    SpecializedFamily (fun t => (A (select t)).submatrix (row t) (col t)) where
  denominator := F.denominator
  denominator_ne_zero := F.denominator_ne_zero
  prime := F.prime
  prime_is_prime := F.prime_is_prime
  prime_is_odd := F.prime_is_odd
  coefficients t := (F.coefficients (select t)).submatrix (row t) (col t)
  lift_correct t := by
    ext i j
    exact F.coefficient_spec (select t) (row t i) (col t j)
  inverse_coefficients t := (F.inverse_coefficients (select t)).submatrix (row t) (col t)
  inverse_lift_correct t i j := F.inverse_lift_correct (select t) (row t i) (col t j)
  reduce := F.reduce

omit [Fintype T] in
@[simp] theorem restrictFamily_matrix (F : SpecializedFamily A) (select : T → K)
    (row col : T → J → I) (f : ℕ) (t : T) :
    (restrictFamily F select row col).matrix f t =
      (F.matrix f (select t)).submatrix (row t) (col t) := rfl

end Restriction

section Layout
variable {m P Q G S : ℕ}

theorem vector_code_val (x : Fin m → Fin Q) :
    (lexLayout x).val = (LexBlocks.subvectorEncode x).val := by
  let e : Equiv.Perm (Fin (Q^m)) :=
    (finCongr (by simp : Q ^ Fintype.card (Fin m) = Q^m)).symm.trans
      (LexBlocks.subvectorEncode.symm.trans lexLayout)
  have hm : StrictMono e := by
    intro a b hab
    apply (lexLayout_lt _ _).mpr
    apply (LexBlocks.subvectorEncode_lt _ _).mp
    first
    | exact hab
    | (have h_sx := hab; simp only [Equiv.apply_symm_apply] at h_sx ⊢; exact h_sx)
    | (have h_sx := hab; simp only [Equiv.apply_symm_apply] at h_sx; exact h_sx)
    | (simp only [Equiv.apply_symm_apply]; exact hab)
  have he : (e : Fin (Q^m) → Fin (Q^m)) = id :=
    (hm.range_inj strictMono_id).mp (by simp only [Equiv.range_eq_univ,Set.range_id])
  have h := congrFun he (finCongr (by simp : Q ^ Fintype.card (Fin m) = Q^m)
    (LexBlocks.subvectorEncode x))
  try dsimp only [e] at h
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply,id_eq] at h
  change lexLayout x = finCongr _ (LexBlocks.subvectorEncode x) at h
  exact congrArg Fin.val h

def castProgram {V W : ℕ} (h : V = W) (ps : List (Pass V)) : List (Pass W) := h ▸ ps

theorem castProgram_destination {V W : ℕ} (h : V = W)
    (ps : List (Pass V)) (x : Fin V) :
    destination (castProgram h ps) (finCongr h x) = finCongr h (destination ps x) := by
  subst W
  rfl

@[simp] theorem castProgram_constant {V W : ℕ} (h : V = W) (ps : List (Pass V)) :
    totalConstant (castProgram h ps) = totalConstant ps := by
  subst W
  rfl

theorem highWholeVolume (m P Q G S : ℕ) :
    P*(Q^m*(G*(Q^m*S))) = Volume (Fin m) P Q G S := by
  simp only [Volume,FieldCount,Fintype.card_fin]
  ring

theorem lowWholeVolume (m P Q G S : ℕ) :
    (P*(Q^m*G))*(Q^m*S) = Volume (Fin m) P Q G S := by
  simp only [Volume,FieldCount,Fintype.card_fin]

theorem high_whole_layout (a : Addr (Fin m) P Q G S) :
    longLayout a = finCongr (highWholeVolume m P Q G S)
      (tripleEncode (a.prefixCoord,lexLayout a.high,
        tripleEncode (a.gap,lexLayout a.low,a.suffix))) := by
  apply Fin.ext
  simp only [longLayout_val,finCongr_apply_coe,tripleEncode_val,
    vector_code_val,FieldCount,Fintype.card_fin]
  ring

theorem low_whole_layout (a : Addr (Fin m) P Q G S) :
    longLayout a = finCongr (lowWholeVolume m P Q G S)
      (tripleEncode (tripleEncode (a.prefixCoord,lexLayout a.high,a.gap),
        lexLayout a.low,a.suffix)) := by
  apply Fin.ext
  simp only [longLayout_val,finCongr_apply_coe,tripleEncode_val,
    vector_code_val,FieldCount,Fintype.card_fin]

end Layout

section WholeScans
variable {K : Type*} [Fintype K] {m : ℕ}
variable {A : K → Matrix (Fin m) (Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ)

local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

def highProgram (k : K) (hdiag : ∀ i, A k i i ≠ 0)
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) :
    List (Pass (Volume (Fin m) P (F.prime^f) G S)) :=
  castProgram (highWholeVolume m P (F.prime^f) G S)
    (GlobalTriangular.program F f k hdiag P (G*((F.prime^f)^m*S))
      (Nat.mul_pos hG (Nat.mul_pos (pow_pos (pow_pos F.prime_is_prime.pos _) _) hS)))

def lowProgram (k : K) (hdiag : ∀ i, A k i i ≠ 0)
    (P G S : ℕ) (hS : 0 < S) :
    List (Pass (Volume (Fin m) P (F.prime^f) G S)) :=
  castProgram (lowWholeVolume m P (F.prime^f) G S)
    (GlobalTriangular.program F f k hdiag (P*((F.prime^f)^m*G)) S hS)

theorem highProgram_encoded (k : K) (hdiag : ∀ i, A k i i ≠ 0)
    (hA : MatrixFactorization.LowerTriangular (A k))
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (a : Addr (Fin m) P (F.prime^f) G S) :
    destination (highProgram F f k hdiag P G S hG hS) (longLayout a) =
      longLayout ⟨a.prefixCoord,(SpecializedTriangular.finMatrix F f k).mulVec a.high,
        a.gap,a.low,a.suffix⟩ := by
  rw [high_whole_layout,highProgram,castProgram_destination,
    GlobalTriangular.destination_encoded F f k hdiag hA,high_whole_layout]

theorem lowProgram_encoded (k : K) (hdiag : ∀ i, A k i i ≠ 0)
    (hA : MatrixFactorization.LowerTriangular (A k))
    (P G S : ℕ) (hS : 0 < S) (a : Addr (Fin m) P (F.prime^f) G S) :
    destination (lowProgram F f k hdiag P G S hS) (longLayout a) =
      longLayout ⟨a.prefixCoord,a.high,a.gap,
        (SpecializedTriangular.finMatrix F f k).mulVec a.low,a.suffix⟩ := by
  rw [low_whole_layout,lowProgram,castProgram_destination,
    GlobalTriangular.destination_encoded F f k hdiag hA,low_whole_layout]

theorem highProgram_constant (k : K) (hdiag : ∀ i, A k i i ≠ 0)
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) :
    totalConstant (highProgram F f k hdiag P G S hG hS) ≤
      2*SpecializedTriangular.fixedConstant (A := A) k := by
  rw [highProgram,castProgram_constant]
  apply GlobalTriangular.program_constant

theorem lowProgram_constant (k : K) (hdiag : ∀ i, A k i i ≠ 0)
    (P G S : ℕ) (hS : 0 < S) :
    totalConstant (lowProgram F f k hdiag P G S hS) ≤
      2*SpecializedTriangular.fixedConstant (A := A) k := by
  rw [lowProgram,castProgram_constant]
  apply GlobalTriangular.program_constant

end WholeScans

section LowerBlocks
variable {K : Type*} [Fintype K] {m : ℕ}
local instance doubledDecEq : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq
variable {A : K → Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ)

local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

abbrev highFamily : SpecializedFamily (fun k => TriangularConjugacy.highBlock (A k)) :=
  restrictFamily F id (fun _ => toLex ∘ Sum.inl) (fun _ => toLex ∘ Sum.inl)

abbrev lowFamily : SpecializedFamily (fun k => TriangularConjugacy.lowBlock (A k)) :=
  restrictFamily F id (fun _ => toLex ∘ Sum.inr) (fun _ => toLex ∘ Sum.inr)

def fullFinMatrix (k : K) :
    Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) (Fin (F.prime^f)) :=
  (F.matrix f k).map (ZMod.finEquiv (F.prime^f)).symm

def crossFinMatrix (k : K) : Matrix (Fin m) (Fin m) (Fin (F.prime^f)) :=
  (fullFinMatrix F f k).submatrix (toLex ∘ Sum.inr) (toLex ∘ Sum.inl)

theorem fullFinMatrix_blocks (k : K) (hA : TriangularConjugacy.LowerTriangular (A k)) :
    fullFinMatrix F f k = Matrix.fromBlocks
      (SpecializedTriangular.finMatrix (highFamily F) f k) 0
      (crossFinMatrix F f k) (SpecializedTriangular.finMatrix (lowFamily F) f k) := by
  apply Matrix.ext
  intro r c
  rcases r with r | r <;> rcases c with c | c
  · rfl
  · change (ZMod.finEquiv (F.prime^f)).symm
      (F.matrix f k (toLex (Sum.inl r)) (toLex (Sum.inr c))) = 0
    rw [F.preserves_entry_zero k _ _ (hA _ _ (Sum.Lex.inl_lt_inr _ _)) f,map_zero]
  · rfl
  · rfl

omit [Fintype K] in
theorem highDiagonal (k : K) (hA : TriangularConjugacy.LowerTriangular (A k))
    (hu : IsUnit (A k)) : ∀ i, TriangularConjugacy.highBlock (A k) i i ≠ 0 :=
  fun i => TriangularConjugacy.lower_diagonal_nonzero (A k) hA hu (toLex (Sum.inl i))

omit [Fintype K] in
theorem lowDiagonal (k : K) (hA : TriangularConjugacy.LowerTriangular (A k))
    (hu : IsUnit (A k)) : ∀ i, TriangularConjugacy.lowBlock (A k) i i ≠ 0 :=
  fun i => TriangularConjugacy.lower_diagonal_nonzero (A k) hA hu (toLex (Sum.inr i))

def lowerProgram (k : K) (hA : TriangularConjugacy.LowerTriangular (A k))
    (hu : IsUnit (A k)) (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) :
    List (Pass (Volume (Fin m) P (F.prime^f) G S)) :=
  lowProgram (lowFamily F) f k (lowDiagonal k hA hu) P G S hS ++
    crossProgram (crossFinMatrix F f k) m (Nat.le_refl m) ++
    highProgram (highFamily F) f k (highDiagonal k hA hu) P G S hG hS

def joinedVector {Q P G S : ℕ} (a : Addr (Fin m) P Q G S) :
    (Fin m ⊕ₗ Fin m) → Fin Q := Sum.elim a.high a.low

def matrixAddress {Q P G S : ℕ} [NeZero Q]
    (M : Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) (Fin Q))
    (a : Addr (Fin m) P Q G S) : Addr (Fin m) P Q G S :=
  ⟨a.prefixCoord,fun i => M.mulVec (joinedVector a) (toLex (Sum.inl i)),a.gap,
    fun i => M.mulVec (joinedVector a) (toLex (Sum.inr i)),a.suffix⟩

theorem lowerProgram_encoded (k : K) (hA : TriangularConjugacy.LowerTriangular (A k))
    (hu : IsUnit (A k)) (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (a : Addr (Fin m) P (F.prime^f) G S) :
    destination (lowerProgram F f k hA hu P G S hG hS) (longLayout a) =
      longLayout (matrixAddress (fullFinMatrix F f k) a) := by
  have hh := highProgram_encoded (highFamily F) f k (highDiagonal k hA hu)
    (TriangularConjugacy.lower_diagonalBlocks (A k) hA hu).1.1 P G S hG hS
  have hl := lowProgram_encoded (lowFamily F) f k (lowDiagonal k hA hu)
    (TriangularConjugacy.lower_diagonalBlocks (A k) hA hu).2.1 P G S hS
  rw [lowerProgram,lowerBlockProgram_complete _ _ _ _ _ hh hl]
  congr 1
  rw [matrixAddress,fullFinMatrix_blocks F f k hA]
  change Address.FullAddress.mk a.prefixCoord _ a.gap _ a.suffix =
    Address.FullAddress.mk a.prefixCoord
      (fun i => (Matrix.fromBlocks _ _ _ _).mulVec
        (Sum.elim a.high a.low) (Sum.inl i)) a.gap
      (fun i => (Matrix.fromBlocks _ _ _ _).mulVec
        (Sum.elim a.high a.low) (Sum.inr i)) a.suffix
  simp only [Matrix.fromBlocks_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Matrix.zero_mulVec,add_zero,Pi.add_apply,add_comm]
  rfl

def lowerConstant (k : K) : ℕ :=
  2*SpecializedTriangular.fixedConstant (A := fun k => TriangularConjugacy.lowBlock (A k)) k +
    10*m +
    2*SpecializedTriangular.fixedConstant (A := fun k => TriangularConjugacy.highBlock (A k)) k

theorem lowerProgram_constant (k : K) (hA : TriangularConjugacy.LowerTriangular (A k))
    (hu : IsUnit (A k)) (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) :
    totalConstant (lowerProgram F f k hA hu P G S hG hS) ≤ lowerConstant (A := A) k := by
  have hl := lowProgram_constant (lowFamily F) f k (lowDiagonal k hA hu) P G S hS
  have hh := highProgram_constant (highFamily F) f k (highDiagonal k hA hu) P G S hG hS
  have happ {V : ℕ} (xs ys : List (Pass V)) :
      totalConstant (xs ++ ys) = totalConstant xs + totalConstant ys := by
    simp only [totalConstant,List.map_append,List.sum_append]
  rw [lowerProgram,happ,happ,crossProgram_constant]
  exact Nat.add_le_add (Nat.add_le_add_right hl _) hh

theorem lowerProgram_execution {Value : Type*} [Inhabited Value]
    (k : K) (hA : TriangularConjugacy.LowerTriangular (A k)) (hu : IsUnit (A k))
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (input : Fin (Volume (Fin m) P (F.prime^f) G S) → Value) (block : ℕ) (hb : 0 < block) :
    ∃ cost, Execution block hb (lowerProgram F f k hA hu P G S hG hS) input cost ∧
      cost ≤ lowerConstant (A := A) k*(Volume (Fin m) P (F.prime^f) G S / block + 1) := by
  obtain ⟨cost,he,hc⟩ := program_correct (lowerProgram F f k hA hu P G S hG hS) input block hb
  exact ⟨cost,he,hc.trans (Nat.mul_le_mul_right _ (lowerProgram_constant F f k hA hu P G S hG hS))⟩

end LowerBlocks

section MatrixAction
variable {m Q P G S : ℕ} [NeZero Q]
local instance doubledDecEqAction : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq

theorem joined_matrixAddress
    (M : Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) (Fin Q))
    (a : Addr (Fin m) P Q G S) :
    joinedVector (matrixAddress M a) = M.mulVec (joinedVector a) := by
  funext i
  rcases i with i | i <;> rfl

theorem matrixAddress_mul
    (M N : Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) (Fin Q))
    (a : Addr (Fin m) P Q G S) :
    matrixAddress (M*N) a = matrixAddress M (matrixAddress N a) := by
  change Address.FullAddress.mk a.prefixCoord _ a.gap _ a.suffix =
    Address.FullAddress.mk a.prefixCoord
      (fun i => M.mulVec (joinedVector (matrixAddress N a)) (toLex (Sum.inl i))) a.gap
      (fun i => M.mulVec (joinedVector (matrixAddress N a)) (toLex (Sum.inr i))) a.suffix
  rw [joined_matrixAddress,Matrix.mulVec_mulVec]

def swapMatrixR {J R : Type*} [DecidableEq J] [Zero R] [One R]
    (i j : J) : Matrix J J R := fun r c => (1 : Matrix J J R) r (Equiv.swap i j c)

theorem swapMatrixR_mulVec {J R : Type*} [Fintype J] [DecidableEq J] [Semiring R]
    (i j : J) (x : J → R) : (swapMatrixR i j).mulVec x = fun r => x (Equiv.swap i j r) := by
  funext r
  simp only [Matrix.mulVec,dotProduct,swapMatrixR,Matrix.one_apply]
  have he (c : J) : (r = Equiv.swap i j c) ↔ (c = Equiv.swap i j r) := by
    rw [eq_comm,Equiv.swap_apply_eq_iff]
  simp_rw [he]
  simp

theorem matrixAddress_swap (s t : Fin m) (a : Addr (Fin m) P Q G S) :
    matrixAddress (swapMatrixR (toLex (Sum.inl s)) (toLex (Sum.inr t))) a =
      SingleCoordinate.shortExchange s t a := by
  unfold matrixAddress
  erw [swapMatrixR_mulVec]
  simp only [SingleCoordinate.shortExchange,Equiv.coe_fn_mk,SingleCoordinate.modifySelected]
  congr 1
  · funext i
    by_cases hi : i = s
    · subst i
      simp [Equiv.swap_apply_left,joinedVector,Function.update]
      rfl
    · have hni : (toLex (Sum.inl i) : Fin m ⊕ₗ Fin m) ≠ toLex (Sum.inl s) :=
        fun h => hi (Sum.inl.inj h)
      rw [Equiv.swap_apply_of_ne_of_ne hni (by intro h; cases h)]
      simp [joinedVector,Function.update,hi]
      rfl
  · funext i
    by_cases hi : i = t
    · subst i
      simp [Equiv.swap_apply_right,joinedVector,Function.update]
      rfl
    · have hni : (toLex (Sum.inr i) : Fin m ⊕ₗ Fin m) ≠ toLex (Sum.inr t) :=
        fun h => hi (Sum.inr.inj h)
      rw [Equiv.swap_apply_of_ne_of_ne (by intro h; cases h) hni]
      simp [joinedVector,Function.update,hi]
      rfl

end MatrixAction

section ExecutionComposition
variable {V block : ℕ} {Value : Type*} [Inhabited Value] {hb : 0 < block}

omit [Inhabited Value] in
theorem eval_append (ps qs : List (Pass V)) (input : Fin V → Value) :
    eval (ps++qs) input = eval qs (eval ps input) := by
  induction ps generalizing input with
  | nil => rfl
  | cons p ps ih => exact ih (moved p input)

theorem execution_append {ps qs : List (Pass V)} {input : Fin V → Value} {c d : ℕ}
    (hp : Execution block hb ps input c)
    (hq : Execution block hb qs (eval ps input) d) :
    Execution block hb (ps++qs) input (c+d) := by
  induction hp with
  | nil input => simpa only [List.nil_append,eval,Nat.zero_add] using hq
  | cons p ps input c e hh ht ih =>
    simpa only [List.cons_append,Nat.add_assoc] using
      Execution.cons p (ps++qs) input c (e+d) hh (ih hq)

end ExecutionComposition

section Conjugate
variable {K : Type*} [Fintype K] {m : ℕ}
local instance doubledDecEqConjugate : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq
variable {A : K → Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) ℚ}
variable (F : SpecializedFamily A) (f : ℕ)
local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

theorem fullFinMatrix_factorization (target left pivot right : K)
    (h : A target = A left*A pivot*A right) :
    fullFinMatrix F f target = fullFinMatrix F f left *
      fullFinMatrix F f pivot * fullFinMatrix F f right := by
  have hred := F.preserves_factorization target left pivot right h f
  exact congrArg ((ZMod.finEquiv (F.prime^f)).symm.toRingHom.mapMatrix) hred |>.trans
    (by simp only [map_mul]; rfl)

theorem fullFinMatrix_swap (pivot : K) (s t : Fin m)
    (hp : A pivot = TriangularConjugacy.swapMatrix (toLex (Sum.inl s)) (toLex (Sum.inr t))) :
    fullFinMatrix F f pivot = swapMatrixR (toLex (Sum.inl s)) (toLex (Sum.inr t)) := by
  apply Matrix.ext
  intro r c
  by_cases he : r = Equiv.swap (toLex (Sum.inl s)) (toLex (Sum.inr t)) c
  · have hentry : A pivot r c = 1 := by
      rw [hp]
      simp only [TriangularConjugacy.swapMatrix,Matrix.one_apply,if_pos he]
    change (ZMod.finEquiv (F.prime^f)).symm (F.matrix f pivot r c) = _
    rw [F.preserves_entry_one pivot r c hentry f,map_one]
    simp only [swapMatrixR,Matrix.one_apply,if_pos he]
  · have hentry : A pivot r c = 0 := by
      rw [hp]
      simp only [TriangularConjugacy.swapMatrix,Matrix.one_apply,if_neg he]
    change (ZMod.finEquiv (F.prime^f)).symm (F.matrix f pivot r c) = _
    rw [F.preserves_entry_zero pivot r c hentry f,map_zero]
    simp only [swapMatrixR,Matrix.one_apply,if_neg he]

/-- The child program is included once, between two actual lower-factor scans.
Its implementation and cost are supplied by the recursive caller. -/
def conjugateProgram (left right : K)
    (hl : TriangularConjugacy.LowerTriangular (A left)) (hul : IsUnit (A left))
    (hr : TriangularConjugacy.LowerTriangular (A right)) (hur : IsUnit (A right))
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (child : List (Pass (Volume (Fin m) P (F.prime^f) G S))) :
    List (Pass (Volume (Fin m) P (F.prime^f) G S)) :=
  lowerProgram F f right hr hur P G S hG hS ++ child ++
    lowerProgram F f left hl hul P G S hG hS

theorem conjugateProgram_encoded (target left pivot right : K)
    (hfactor : A target = A left*A pivot*A right) (s t : Fin m)
    (hp : A pivot = TriangularConjugacy.swapMatrix (toLex (Sum.inl s)) (toLex (Sum.inr t)))
    (hl : TriangularConjugacy.LowerTriangular (A left)) (hul : IsUnit (A left))
    (hr : TriangularConjugacy.LowerTriangular (A right)) (hur : IsUnit (A right))
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (child : List (Pass (Volume (Fin m) P (F.prime^f) G S)))
    (hc : ∀ a : Addr (Fin m) P (F.prime^f) G S,
      destination child (longLayout a) = longLayout (SingleCoordinate.shortExchange s t a))
    (a : Addr (Fin m) P (F.prime^f) G S) :
    destination (conjugateProgram F f left right hl hul hr hur P G S hG hS child)
      (longLayout a) = longLayout (matrixAddress (fullFinMatrix F f target) a) := by
  rw [conjugateProgram,destination_append,destination_append,Equiv.trans_apply,
    Equiv.trans_apply,lowerProgram_encoded,hc,lowerProgram_encoded,
    fullFinMatrix_factorization F f target left pivot right hfactor,
    matrixAddress_mul,matrixAddress_mul,fullFinMatrix_swap F f pivot s t hp,
    matrixAddress_swap]

/-- The supplied recursive execution is used once, on exactly the output of
the inverse-factor scans. Both surrounding execution witnesses are generated
from concrete pass lists; their fixed charge is independent of the prime power. -/
theorem conjugateProgram_execution {Value : Type*} [Inhabited Value]
    (left right : K)
    (hl : TriangularConjugacy.LowerTriangular (A left)) (hul : IsUnit (A left))
    (hr : TriangularConjugacy.LowerTriangular (A right)) (hur : IsUnit (A right))
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (child : List (Pass (Volume (Fin m) P (F.prime^f) G S)))
    (input : Fin (Volume (Fin m) P (F.prime^f) G S) → Value)
    (block : ℕ) (hb : 0 < block) (childCost : ℕ)
    (hc : Execution block hb child
      (eval (lowerProgram F f right hr hur P G S hG hS) input) childCost) :
    ∃ cost, Execution block hb
      (conjugateProgram F f left right hl hul hr hur P G S hG hS child) input cost ∧
      cost ≤ (lowerConstant (A := A) right+lowerConstant (A := A) left)*
        (Volume (Fin m) P (F.prime^f) G S / block+1) + childCost := by
  obtain ⟨beforeCost,hbefore,hbc⟩ :=
    lowerProgram_execution F f right hr hur P G S hG hS input block hb
  obtain ⟨afterCost,hafter,hac⟩ := lowerProgram_execution F f left hl hul P G S hG hS
    (eval child (eval (lowerProgram F f right hr hur P G S hG hS) input)) block hb
  have he := execution_append (execution_append hbefore hc)
    (by rw [eval_append]; exact hafter)
  refine ⟨(beforeCost+childCost)+afterCost,he,?_⟩
  rw [Nat.add_mul]
  omega

end Conjugate

section RankOne
variable {m : ℕ}
local instance doubledDecEqLine : DecidableEq (Fin m ⊕ₗ Fin m) :=
  (inferInstance : LinearOrder (Fin m ⊕ₗ Fin m)).toDecidableEq

/-- Four matrices are specialized together: the target partial swap, its
forward lower factor, the one selected transposition, and the inverse factor.
The two Boolean tags merely name matrices and never permute physical data. -/
def lineFamily (u : Fin m → ℚ) (s t : Fin m) :
    Bool × Bool → Matrix (Fin m ⊕ₗ Fin m) (Fin m ⊕ₗ Fin m) ℚ
  | (false,false) => TriangularConjugacy.partialSwap (TriangularConjugacy.lineProjection u)
  | (false,true) => TriangularConjugacy.factor (TriangularConjugacy.doubleVec u)
      (toLex (Sum.inl s)) (toLex (Sum.inr t))
  | (true,false) => TriangularConjugacy.swapMatrix (toLex (Sum.inl s)) (toLex (Sum.inr t))
  | (true,true) => (TriangularConjugacy.factor (TriangularConjugacy.doubleVec u)
      (toLex (Sum.inl s)) (toLex (Sum.inr t)))⁻¹

theorem lineFamily_properties (u : Fin m → ℚ) (s t : Fin m)
    (hs : u s ≠ 0) (ht : u t ≠ 0)
    (hbefore : ∀ r, r < s → u r = 0) (hafter : ∀ r, t < r → u r = 0) :
    TriangularConjugacy.LowerTriangular (lineFamily u s t (false,true)) ∧
    IsUnit (lineFamily u s t (false,true)) ∧
    TriangularConjugacy.LowerTriangular (lineFamily u s t (true,true)) ∧
    IsUnit (lineFamily u s t (true,true)) ∧
    lineFamily u s t (false,false) = lineFamily u s t (false,true) *
      lineFamily u s t (true,false) * lineFamily u s t (true,true) := by
  have h := TriangularConjugacy.partialSwap_factor_properties u s t hs ht hbefore hafter
  exact ⟨h.1,h.2.1,h.2.2,Matrix.isUnit_nonsing_inv_iff.mpr h.2.1,
    TriangularConjugacy.partialSwap_eq_conjugate u s t hs ht hbefore hafter⟩

variable (u : Fin m → ℚ) (s t : Fin m) (F : SpecializedFamily (lineFamily u s t)) (f : ℕ)
variable (hs : u s ≠ 0) (ht : u t ≠ 0)
  (hbefore : ∀ r, r < s → u r = 0) (hafter : ∀ r, t < r → u r = 0)

local instance : NeZero (F.prime^f) := ⟨pow_ne_zero _ F.prime_is_prime.ne_zero⟩

def lineProgram (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (child : List (Pass (Volume (Fin m) P (F.prime^f) G S))) :
    List (Pass (Volume (Fin m) P (F.prime^f) G S)) :=
  let h := lineFamily_properties u s t hs ht hbefore hafter
  conjugateProgram F f (false,true) (true,true) h.1 h.2.1 h.2.2.1 h.2.2.2.1
    P G S hG hS child

/-- This is the actual rational rank-one partial swap from the conjugacy
theorem, specialized once with both factors and the selected transposition. -/
theorem lineProgram_encoded (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (child : List (Pass (Volume (Fin m) P (F.prime^f) G S)))
    (hc : ∀ a : Addr (Fin m) P (F.prime^f) G S,
      destination child (longLayout a) = longLayout (SingleCoordinate.shortExchange s t a))
    (a : Addr (Fin m) P (F.prime^f) G S) :
    destination (lineProgram u s t F f hs ht hbefore hafter P G S hG hS child) (longLayout a) =
      longLayout (matrixAddress (fullFinMatrix F f (false,false)) a) := by
  have h := lineFamily_properties u s t hs ht hbefore hafter
  exact conjugateProgram_encoded F f (false,false) (false,true) (true,false) (true,true)
    h.2.2.2.2 s t rfl h.1 h.2.1 h.2.2.1 h.2.2.2.1 P G S hG hS child hc a

/-- Only the supplied scalar child carries a recursive charge. The forward
and inverse factors use the concrete scan implementation above. -/
theorem lineProgram_execution {Value : Type*} [Inhabited Value]
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (child : List (Pass (Volume (Fin m) P (F.prime^f) G S)))
    (input : Fin (Volume (Fin m) P (F.prime^f) G S) → Value)
    (block : ℕ) (hb : 0 < block) (childCost : ℕ)
    (hc : let h := lineFamily_properties u s t hs ht hbefore hafter
      Execution block hb child
        (eval (lowerProgram F f (true,true) h.2.2.1 h.2.2.2.1 P G S hG hS) input) childCost) :
    ∃ cost, Execution block hb
      (lineProgram u s t F f hs ht hbefore hafter P G S hG hS child) input cost ∧
      cost ≤ (lowerConstant (A := lineFamily u s t) (true,true) +
        lowerConstant (A := lineFamily u s t) (false,true)) *
        (Volume (Fin m) P (F.prime^f) G S / block+1) + childCost := by
  have h := lineFamily_properties u s t hs ht hbefore hafter
  exact conjugateProgram_execution F f (false,true) (true,true)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 P G S hG hS child input block hb childCost hc

end RankOne

end
end CSL.Construction.PartialSwapExecution


