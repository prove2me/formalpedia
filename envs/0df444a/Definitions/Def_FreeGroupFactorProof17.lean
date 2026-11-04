-- Prove2me | Definitions.Def_FreeGroupFactorProof17
-- name    : FreeGroupFactorProof17
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T02:48:41.650609+00:00
-- url     : https://prove2.me/theorems/1d7ee47f-141a-4b27-8981-966adab5c18a
-- title:
--   Free group factors: supporting development, part 17
-- statement:
--   Part 17 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof16

set_option linter.all false

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45 u_46 u_47 u_48
universe u_49

open Filter Topology

namespace FreeFock
open Filter Topology
open scoped ENNReal
variable {α : Type u_6} [DecidableEq α]

end FreeFock
open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace CyclicSpectral
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
end CyclicSpectral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

namespace CyclicSpectral

section
open MeasureTheory
variable {H : Type u_19} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory Filter
variable {H : Type u_20} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Filter
variable {H : Type u_21} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end CyclicSpectral
namespace FreeFock

section
open MeasureTheory
variable {α : Type u_22} [DecidableEq α]

end
open MeasureTheory
variable {α : Type u_23} [DecidableEq α]

end FreeFock
open Filter Topology
open scoped ENNReal

namespace FreeFock

section
open Filter Topology Set MeasureTheory
variable {α : Type u_25} [DecidableEq α]

 theorem semicircular_mem_haar_bicommutant (i : α) :
    semicircular i ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ ({(CyclicSpectral.haarUnitary (semicircular i)
        (semicircular_selfAdjoint i) vacuum : Operator α)} : Set (Operator α)) : Set (Operator α)) := by
  let : Nontrivial (Fock α) := ⟨⟨vacuum,0,by
    intro h
    have he := congrArg (fun v : Fock α => v []) h
    simp [vacuum,lp.single_apply] at he⟩⟩
  have hb (n : ℕ) := CyclicSpectral.bounded_haar_approx (semicircular i)
    (semicircular_selfAdjoint i) vacuum (1/((n:ℝ)+1)) (by positivity)
  choose T hmem hnorm herr using hb
  have hS : semicircular i ∈ gaussianAlgebra α :=
    StarAlgebra.adjoin_le_centralizer_centralizer ℂ _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))
  have hG : IsClosed (gaussianAlgebra α : Set (Operator α)) := by
    rw [gaussianAlgebra,StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  have hT (n : ℕ) : T n ∈ gaussianAlgebra α :=
    StarAlgebra.elemental.le_of_mem hG (spectralHaar_mem i) (hmem n)
  have hv : Tendsto (fun n => T n vacuum) atTop (𝓝 (semicircular i vacuum)) := by
    have h := squeeze_zero_norm (fun n => (herr n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hh := h.add_const (semicircular i vacuum)
    simpa only [sub_add_cancel,zero_add] using hh
  have hstrong : ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (semicircular i ξ)) := by
    apply lp_strong_limit_of_bounded_basis T (semicircular i) ‖semicircular i‖ hnorm
    intro w
    have he (D : Operator α) (hD : D ∈ gaussianAlgebra α) :
        D (lp.single 2 w 1)=rightWick w.reverse (D vacuum) := by
      have h := DFunLike.congr_fun (gaussian_commute_rightWick ⟨D,hD⟩ w.reverse) vacuum
      simpa only [mul_apply_eq_comp,rightWick_vacuum,List.reverse_reverse] using h.symm
    simpa only [he _ (hT _),he _ hS,Function.comp_def] using (rightWick w.reverse).continuous.continuousAt.tendsto.comp hv
  let B := StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ ({(CyclicSpectral.haarUnitary (semicircular i)
        (semicircular_selfAdjoint i) vacuum : Operator α)} : Set (Operator α)) : Set (Operator α))
  have hB : IsClosed (B : Set (Operator α)) := by
    dsimp [B]
    exact Set.isClosed_centralizer _
  have hU : (CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum : Operator α) ∈ B :=
    StarAlgebra.adjoin_le_centralizer_centralizer ℂ _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_singleton _))
  have hTB (n : ℕ) : T n ∈ B := StarAlgebra.elemental.le_of_mem hB hU (hmem n)
  rw [StarSubalgebra.mem_centralizer_iff]
  intro C hC
  have hl (D : Operator α) (hD : D ∈ StarSubalgebra.centralizer ℂ
      ({(CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum : Operator α)} : Set (Operator α))) :
      D*semicircular i=semicircular i*D := by
    apply ContinuousLinearMap.ext
    intro ξ
    have he n := congrArg (fun Q : Operator α => Q ξ)
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hTB n) D hD).1
    exact tendsto_nhds_unique ((D.continuous.continuousAt.tendsto.comp (hstrong ξ)).congr
      (fun n => he n)) (hstrong (D ξ))
  exact ⟨hl C hC,hl (star C) (star_mem hC)⟩
end
section
open Set
variable {α : Type u_26} [DecidableEq α]

def spectralHaarOperator (i : α) : Operator α :=
  CyclicSpectral.haarUnitary (semicircular i) (semicircular_selfAdjoint i) vacuum

theorem haar_gaussian_commutant :
    StarSubalgebra.centralizer ℂ (Set.range (spectralHaarOperator : α → Operator α))=gaussianCommutant α := by
  ext C
  constructor
  · intro hC
    rw [gaussianCommutant,StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨i,rfl⟩
    have hi : C ∈ StarSubalgebra.centralizer ℂ ({spectralHaarOperator i} : Set (Operator α)) :=
      StarSubalgebra.centralizer_le ℂ _ _ (Set.singleton_subset_iff.mpr (Set.mem_range_self i)) hC
    have hh := ((StarSubalgebra.mem_centralizer_iff ℂ).mp (semicircular_mem_haar_bicommutant i) C hi).1
    exact ⟨hh.symm,by rw [(semicircular_selfAdjoint i).star_eq]; exact hh.symm⟩
  · intro hC
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨i,rfl⟩
    have hi : spectralHaarOperator i ∈ gaussianAlgebra α := spectralHaar_mem i
    exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hi C hC).1.symm,
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (show star (spectralHaarOperator i) ∈ gaussianAlgebra α from star_mem hi) C hC).1.symm⟩

theorem haar_generated_gaussian :
    StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (Set.range (spectralHaarOperator : α → Operator α)) : Set (Operator α))=
    gaussianAlgebra α := by
  rw [haar_gaussian_commutant]
  rfl
end

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_28} [DecidableEq α]

 theorem spectralHaar_cyclic_total :
    (algebraCyclic (StarAlgebra.adjoin ℂ (Set.range (spectralHaarOperator : α → Operator α)))
      vacuum).topologicalClosure=⊤ := by
  let A := StarAlgebra.adjoin ℂ (Set.range (spectralHaarOperator : α → Operator α))
  let K := (algebraCyclic A vacuum).topologicalClosure
  have hδ (w : List α) : lp.single 2 w (1:ℂ) ∈ K := by
    have hw : wick w ∈ gaussianAlgebra α := wick_mem_any _
      (fun i => StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
        (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))) w
    rw [← haar_generated_gaussian] at hw
    have hh := bicommutant_vector_mem_cyclic (Set.range (spectralHaarOperator : α → Operator α))
      vacuum (wick w) hw
    simpa only [wick_vacuum] using hh
  apply top_unique
  intro ξ _
  apply (algebraCyclic A vacuum).isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) ξ)
  filter_upwards [] with s
  apply K.sum_mem
  intro w _
  have he : lp.single (E := fun _ : List α => ℂ) 2 w (ξ w)=(ξ w) • lp.single 2 w 1 := by
    ext v
    simp [lp.single_apply,Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hδ w)

end
section
open scoped ComplexConjugate
variable {α : Type u_29} [DecidableEq α]

 theorem vacuumTrace_star (T : Operator α) : vacuumTrace (star T)=conj (vacuumTrace T) := by
  unfold vacuumTrace
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (T vacuum) vacuum).symm

 theorem spectralHaar_integer_moment (i : α) (k : ℤ) :
    vacuumTrace (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)=
      if k=0 then 1 else 0 := by
  cases k with
  | ofNat n =>
    simpa using spectralHaar_moment i n
  | negSucc n =>
    rw [ite_eq_right (Int.negSucc_ne_zero n),zpow_negSucc,← Unitary.star_eq_inv]
    change vacuumTrace (star ((((spectralHaar i : gaussianAlgebra α) : Operator α)^(n+1))))=0
    rw [vacuumTrace_star,spectralHaar_moment]
    simp

end
section
variable {α : Type u_30} [DecidableEq α]

 theorem wick_replicate_boundary (i j : α) (hij : i≠j) (w : List α) (n : ℕ) :
    wick (List.replicate n i)*wick (j::w)=wick (List.replicate n i++j::w) := by
  suffices ∀ n, (wick (List.replicate n i)*wick (j::w)=wick (List.replicate n i++j::w)) ∧
      (wick (List.replicate (n+1) i)*wick (j::w)=wick (List.replicate (n+1) i++j::w)) from (this n).1
  intro n
  induction n with
  | zero =>
    constructor
    · simp
    · simp only [Nat.zero_add,List.replicate_one,List.cons_append,List.nil_append]
      rw [wick_semicircular_cons i [],wick_nil,mul_one,sub_zero,
        wick_semicircular_cons i (j::w)]
      simp only [hij,ite_false,sub_zero]
  | succ n ih =>
    refine ⟨ih.2,?_⟩
    have hleft : wick (List.replicate (n+1+1) i)=
        semicircular i*wick (List.replicate (n+1) i)-wick (List.replicate n i) := by
      conv_lhs => rw [List.replicate_succ,wick_semicircular_cons]
      simp only [List.replicate_succ,ite_true]
    have hright : wick (List.replicate (n+1+1) i++j::w)=
        semicircular i*wick (List.replicate (n+1) i++j::w)-wick (List.replicate n i++j::w) := by
      conv_lhs => rw [List.replicate_succ,List.cons_append,wick_semicircular_cons]
      simp only [List.replicate_succ,List.cons_append,ite_true]
    rw [hleft,sub_mul,mul_assoc,ih.1,ih.2,hright]
end
variable {α : Type u_31} [DecidableEq α]

def blockLetters (L : List (α × ℕ)) : List α :=
  L.flatMap (fun p => List.replicate p.2 p.1)

def blockProduct : List (α × ℕ) → Operator α
  | [] => 1
  | (i,n)::L => wick (List.replicate n i)*blockProduct L

def blocksReduced : List (α × ℕ) → Prop
  | [] => True
  | (i,n)::L => 0 < n ∧ blocksReduced L ∧
    match L with | [] => True | (j,_)::_ => i≠j

 theorem wick_blocks_concatenate (L : List (α × ℕ)) (hL : blocksReduced L) :
    blockProduct L=wick (blockLetters L) := by
  induction L with
  | nil => simp [blockProduct,blockLetters]
  | cons p L ih =>
    rcases p with ⟨i,n⟩
    obtain ⟨hn,hL,hsep⟩ := hL
    cases L with
    | nil => simp [blockProduct,blockLetters]
    | cons q L =>
      rcases q with ⟨j,m⟩
      have hm : 0 < m := hL.1
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      rw [blockProduct,ih hL]
      change wick (List.replicate n i)*wick ((List.replicate (k+1) j)++blockLetters L)=
        wick (List.replicate n i++(List.replicate (k+1) j++blockLetters L))
      simpa only [List.replicate_succ,List.cons_append] using
        wick_replicate_boundary i j hsep (List.replicate k j++blockLetters L) n

 omit [DecidableEq α] in
 theorem blockLetters_nonempty {L : List (α × ℕ)} (hL : blocksReduced L) (h : L≠[]) :
    blockLetters L≠[] := by
  cases L with
  | nil => exact False.elim (h rfl)
  | cons p L =>
    rcases p with ⟨i,n⟩
    have hn : 0 < n := hL.1
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simp [blockLetters,List.replicate_succ]

 theorem wick_blocks_centered_moment (L : List (α × ℕ)) (hL : blocksReduced L) (h : L≠[]) :
    vacuumTrace (blockProduct L)=0 := by
  rw [wick_blocks_concatenate L hL]
  have hne := blockLetters_nonempty hL h
  unfold vacuumTrace
  rw [wick_vacuum]
  simp [vacuum,lp.inner_single_left,lp.single_apply,hne]
end FreeFock
section

variable {A : Type u_32} [NormedRing A] [NormedAlgebra ℂ A]

theorem mul_mem_closed_span_image2 (s t : Set A) (x y : A)
    (hx : x∈(Submodule.span ℂ s).topologicalClosure)
    (hy : y∈(Submodule.span ℂ t).topologicalClosure) :
    x*y∈(Submodule.span ℂ (Set.image2 (·*·) s t)).topologicalClosure := by
  let K := (Submodule.span ℂ (Set.image2 (·*·) s t)).topologicalClosure
  have hbase (b : A) (hb : b∈t) : x*b∈K := by
    have hc : IsClosed {a : A | a*b∈K} :=
      (Submodule.isClosed_topologicalClosure _).preimage (continuous_id.mul continuous_const)
    apply closure_minimal (t := {a : A | a*b∈K}) ?_ hc hx
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      exact Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨a,ha,b,hb,rfl⟩)
    | zero => simp
    | add a c _ _ ha hc => simpa only [Set.mem_ofPred_eq,add_mul] using K.add_mem ha hc
    | smul z a _ ha => simpa only [Set.mem_ofPred_eq,smul_mul_assoc] using K.smul_mem z ha
  have hc : IsClosed {b : A | x*b∈K} :=
    (Submodule.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)
  apply closure_minimal (t := {b : A | x*b∈K}) ?_ hc hy
  intro b hb
  induction hb using Submodule.span_induction with
  | mem b hb => exact hbase b hb
  | zero => simp
  | add b c _ _ hb hc => simpa only [Set.mem_ofPred_eq,mul_add] using K.add_mem hb hc
  | smul z b _ hb => simpa only [Set.mem_ofPred_eq,mul_smul_comm] using K.smul_mem z hb

end
namespace FreeFock

section
variable {α : Type u_33} [DecidableEq α]

 theorem center_run_mem (i : α) (x : Operator α) (hx : x∈runSpan i) :
    x-vacuumTrace x • 1∈positiveRunSpan i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,rfl⟩ := hx
    cases n with
    | zero => simp [vacuumTrace_one]
    | succ n =>
      rw [vacuumTrace_run,ite_eq_right (Nat.succ_ne_zero n),zero_smul ℂ (A := Operator α),sub_zero]
      exact Submodule.subset_span (Set.mem_range_self n)
  | zero => simpa only [vacuumTrace_linear.map_zero,zero_smul ℂ (A := Operator α),sub_self] using (positiveRunSpan i).zero_mem
  | add x y _ _ hx hy =>
    rw [vacuumTrace_linear.map_add,add_smul (R := ℂ) (M := Operator α),add_sub_add_comm]
    exact (positiveRunSpan i).add_mem hx hy
  | smul c x _ hx =>
    rw [vacuumTrace_linear.map_smul,smul_eq_mul,← smul_smul,← smul_sub]
    exact (positiveRunSpan i).smul_mem c hx

 theorem center_run_closure (i : α) (x : Operator α)
    (hx : x∈(runSpan i).topologicalClosure) :
    x-vacuumTrace x • 1∈(positiveRunSpan i).topologicalClosure := by
  have hc : Continuous (fun x : Operator α => x-vacuumTrace x • 1) :=
    continuous_id.sub (vacuumTrace_continuous.smul continuous_const)
  apply closure_minimal (t := {x | x-vacuumTrace x • 1∈(positiveRunSpan i).topologicalClosure}) ?_ ?_ hx
  · intro a ha
    exact (positiveRunSpan i).le_topologicalClosure (center_run_mem i a ha)
  · exact (positiveRunSpan i).isClosed_topologicalClosure.preimage hc

 theorem spectralHaar_run_closure (i : α) :
    spectralHaarOperator i ∈ (runSpan i).topologicalClosure := by
  change spectralHaarOperator i ∈ (runAlgebra i).topologicalClosure
  apply CyclicSpectral.complexHom_mem
  · exact StarSubalgebra.isClosed_topologicalClosure _
  · apply StarSubalgebra.le_topologicalClosure
    change semicircular i∈runSpan i
    simpa [wick_semicircular_cons] using run_mem i 1

 theorem spectralHaar_power_positive_run_closure (i : α) (k : ℤ) (hk : k≠0) :
    ((((spectralHaar i)^k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) ∈
      (positiveRunSpan i).topologicalClosure := by
  have hrun : ((((spectralHaar i)^k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α) ∈
      (runSpan i).topologicalClosure := by
    change ((↑((spectralHaar i)^k) : gaussianAlgebra α) : Operator α) ∈
      (runAlgebra i).topologicalClosure
    have hh : spectralHaarOperator i∈(runAlgebra i).topologicalClosure := spectralHaar_run_closure i
    cases k with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast,zpow_natCast]
      change spectralHaarOperator i^n ∈ (runAlgebra i).topologicalClosure
      exact pow_mem hh n
    | negSucc n =>
      rw [zpow_negSucc,← Unitary.star_eq_inv]
      change star (spectralHaarOperator i^(n+1))∈(runAlgebra i).topologicalClosure
      exact star_mem (pow_mem hh (n+1))
  have hc := center_run_closure i _ hrun
  rw [spectralHaar_integer_moment,ite_eq_right hk,zero_smul ℂ (A := Operator α),sub_zero] at hc
  exact hc

end
variable {α : Type u_34} [DecidableEq α]

def colorsReduced : List α → Prop
  | [] => True
  | i::L => colorsReduced L ∧ (match L with | [] => True | j::_ => i≠j)

def runProducts : List α → Set (Operator α)
  | [] => {1}
  | i::L => Set.image2 (·*·) (Set.range (fun n : ℕ => wick (List.replicate (n+1) i))) (runProducts L)

 theorem runProducts_blocks (L : List α) (X : Operator α) (hX : X∈runProducts L) :
    ∃ K : List (α×ℕ), K.map Prod.fst=L ∧ (∀ p∈K,0<p.2) ∧ X=blockProduct K := by
  induction L generalizing X with
  | nil => exact ⟨[],rfl,by simp,by simpa [runProducts,blockProduct] using hX⟩
  | cons i L ih =>
    obtain ⟨a,⟨n,rfl⟩,b,hb,rfl⟩ := hX
    obtain ⟨K,hK,hpos,rfl⟩ := ih b hb
    refine ⟨(i,n+1)::K,by simp [hK],?_,rfl⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.succ_pos n
    · exact hpos p hp

 omit [DecidableEq α] in
 theorem blocksReduced_of_colors (K : List (α×ℕ))
    (h : colorsReduced (K.map Prod.fst)) (hpos : ∀ p∈K,0<p.2) : blocksReduced K := by
  induction K with
  | nil => trivial
  | cons p K ih =>
    rcases p with ⟨i,n⟩
    refine ⟨hpos (i,n) (by simp),ih h.1 (fun p hp => hpos p (by simp [hp])),?_⟩
    cases K with
    | nil => trivial
    | cons q K => exact h.2

 theorem runProducts_trace_zero (L : List α) (h : colorsReduced L) (hne : L≠[])
    (X : Operator α) (hX : X∈runProducts L) : vacuumTrace X=0 := by
  obtain ⟨K,hK,hpos,rfl⟩ := runProducts_blocks L X hX
  apply wick_blocks_centered_moment
  · apply blocksReduced_of_colors K
    · simpa only [hK] using h
    · exact hpos
  · intro he
    apply hne
    simpa only [he,List.map_nil] using hK.symm

 theorem vacuumTrace_span_zero (S : Set (Operator α)) (hS : ∀ X∈S,vacuumTrace X=0)
    (X : Operator α) (hX : X∈(Submodule.span ℂ S).topologicalClosure) : vacuumTrace X=0 := by
  apply closure_minimal (t := {X : Operator α | vacuumTrace X=0}) ?_
    (isClosed_eq vacuumTrace_continuous continuous_const) hX
  intro X hX
  induction hX using Submodule.span_induction with
  | mem X hX => exact hS X hX
  | zero => exact vacuumTrace_linear.map_zero
  | add X Y _ _ hX hY =>
    change vacuumTrace X=0 at hX
    change vacuumTrace Y=0 at hY
    simp only [Set.mem_ofPred_eq,vacuumTrace_linear.map_add,hX,hY,add_zero]
  | smul c X _ hX =>
    change vacuumTrace X=0 at hX
    simp only [Set.mem_ofPred_eq,vacuumTrace_linear.map_smul,hX,smul_zero]

def haarProduct : List (α×ℤ) → Operator α
  | [] => 1
  | (i,k)::L => (((spectralHaar i ^ k : unitary (gaussianAlgebra α)) : gaussianAlgebra α) : Operator α)*haarProduct L

 theorem haarProduct_mem_runProducts (L : List (α×ℤ)) (hL : ∀ p∈L,p.2≠0) :
    haarProduct L∈(Submodule.span ℂ (runProducts (L.map Prod.fst))).topologicalClosure := by
  induction L with
  | nil =>
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (by simp [runProducts,haarProduct]))
  | cons p L ih =>
    rcases p with ⟨i,k⟩
    exact mul_mem_closed_span_image2 _ _ _ _
      (spectralHaar_power_positive_run_closure i k (hL (i,k) (by simp)))
      (ih (fun p hp => hL p (by simp [hp])))

 theorem spectralHaar_mixed_moment (L : List (α×ℤ))
    (hL : ∀ p∈L,p.2≠0) (hred : colorsReduced (L.map Prod.fst)) (hne : L≠[]) :
    vacuumTrace (haarProduct L)=0 := by
  apply vacuumTrace_span_zero (runProducts (L.map Prod.fst))
  · exact runProducts_trace_zero _ hred (by simpa using hne)
  · exact haarProduct_mem_runProducts L hL

end FreeFock

section
variable {α : Type u_35}

def adjacentDistinct : List α → Prop
  | [] => True
  | i::L => adjacentDistinct L ∧ (match L with | [] => True | j::_ => i≠j)

def expandSignedRuns (R : List ((α×Bool)×ℕ)) : List (α×Bool) :=
  R.flatMap (fun p => List.replicate p.2 p.1)

theorem reduced_signed_runs (L : List (α×Bool)) (hL : FreeGroup.IsReduced L) :
    ∃ R : List ((α×Bool)×ℕ), L=expandSignedRuns R ∧
      (∀ p∈R,0<p.2) ∧ adjacentDistinct (R.map (fun p => p.1.1)) := by
  classical
  induction L with
  | nil => exact ⟨[],rfl,by simp,by trivial⟩
  | cons x L ih =>
    have ht : FreeGroup.IsReduced L := hL.tail
    obtain ⟨R,hR,hpos,hred⟩ := ih ht
    rcases x with ⟨i,b⟩
    cases R with
    | nil =>
      have hnil : L=[] := hR
      subst L
      exact ⟨[((i,b),1)],by simp [expandSignedRuns],by simp,by trivial⟩
    | cons p R =>
      rcases p with ⟨⟨j,c⟩,m⟩
      have hm := hpos ((j,c),m) (by simp)
      obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      have he : L=(j,c)::(List.replicate n (j,c)++expandSignedRuns R) := by
        simpa [expandSignedRuns,List.replicate_succ] using hR
      by_cases hij : i=j
      · subst j
        have hpair : FreeGroup.IsReduced ((i,b)::(i,c)::(List.replicate n (i,c)++expandSignedRuns R)) := by
          simpa only [he] using hL
        have hbc : b=c := (FreeGroup.isReduced_cons_cons.mp hpair).1 rfl
        subst c
        refine ⟨((i,b),n+2)::R,?_,?_,hred⟩
        · simp only [expandSignedRuns,List.flatMap_cons,List.replicate_succ,List.cons_append,he]
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · omega
          · exact hpos p (List.mem_cons_of_mem _ hp)
      · refine ⟨((i,b),1)::((j,c),n+1)::R,?_,?_,?_⟩
        · simpa [expandSignedRuns] using congrArg (List.cons (i,b)) hR
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Nat.zero_lt_one
          · exact hpos p hp
        · exact ⟨hred,hij⟩

end
section
variable {α : Type u_36} {G : Type u_37} [Group G]

def signedExponent (b : Bool) (n : ℕ) : ℤ := bif b then (n : ℤ) else -(n : ℤ)

theorem signedExponent_ne_zero (b : Bool) (n : ℕ) (hn : 0<n) : signedExponent b n≠0 := by
  cases b <;> simp [signedExponent,ne_of_gt hn]

theorem signedPower (b : Bool) (n : ℕ) (x : G) :
    x^signedExponent b n = (bif b then x else x⁻¹)^n := by
  cases b <;> simp [signedExponent]

def signedRunBlocks (R : List ((α×Bool)×ℕ)) : List (α×ℤ) :=
  R.map (fun p => (p.1.1,signedExponent p.1.2 p.2))

theorem lift_expandSignedRuns (f : α→G) (R : List ((α×Bool)×ℕ)) :
    FreeGroup.lift f (FreeGroup.mk (expandSignedRuns R))=
      ((signedRunBlocks R).map (fun p => f p.1^p.2)).prod := by
  rw [FreeGroup.lift_mk]
  induction R with
  | nil => rfl
  | cons p R ih =>
    rcases p with ⟨⟨i,b⟩,n⟩
    simpa only [expandSignedRuns,List.flatMap_cons,List.map_append,List.prod_append,
      List.map_replicate,List.prod_replicate,signedRunBlocks,List.map_cons,List.prod_cons,
      signedPower] using congrArg (fun x : G => (bif b then f i else (f i)⁻¹)^n*x) ih

end
namespace FreeFock
variable {α : Type u_38} [DecidableEq α]

def haarRepresentation : FreeGroup α →* unitary (gaussianAlgebra α) :=
  FreeGroup.lift spectralHaar

end FreeFock

namespace CyclicUnitary
open scoped ENNReal
variable {G : Type u_42} {E : Type u_43} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (ρ : G →* (E →L[ℂ] E)) (hstar : ∀ g,star (ρ g)=ρ g⁻¹) (ξ : E)

end CyclicUnitary
namespace FreeFock
variable {α : Type u_44} [DecidableEq α]

end FreeFock

section

variable {A : Type u_45} {B : Type u_46} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

end
open scoped ENNReal
variable {G : Type u_47} [Group G] [DecidableEq G]

namespace FreeFock
variable {α : Type u_48} [DecidableEq α]

end FreeFock

end FreeGroupFactorMain

end

end OAI
end


