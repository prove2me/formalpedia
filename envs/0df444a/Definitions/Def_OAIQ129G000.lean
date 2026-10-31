-- Prove2me | Definitions.Def_OAIQ129G000
-- name    : OAIQ129G000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:12:11.641364+00:00
-- url     : https://prove2.me/theorems/a523acab-b021-4dc5-af4d-2777ced47059
-- title:
--   Definitions bundle OAIQ129G000 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 157 declarations of OpenAI's Lean: 57 definitions, 4 inductive types or structures, 11 instances and 85 theorems. The definitions and types are `OAI.FreeGroupFactorMain.GroupHilbert`, `OAI.FreeGroupFactorMain.GroupOperator`, `OAI.FreeGroupFactorMain.hilbertReindex`, `OAI.FreeGroupFactorMain.leftRegular`, `OAI.FreeGroupFactorMain.ultraweakOperatorTopology`, `OAI.Generator.Bell.leftEntry`, `OAI.Generator.Bell.projection`, `OAI.Generator.CommutingProjectionEncoding.tail`, `OAI.Generator.CommutingProjectionEncoding.weight`, `OAI.Generator.FactorTraceUnitary`, `OAI.Generator.FactorTraceUnitary.algebra`, `OAI.Generator.FiniteHilbert`, `OAI.Generator.Tracial.AlgebraProjection`, `OAI.Generator.Tracial.AlgebraProjection.Subequivalent`, `OAI.Generator.Tracial.AlgebraProjection.finsetSum`, `OAI.Generator.Tracial.CornerPartition`, `OAI.Generator.Tracial.CornerPartition.pinch`, `OAI.Generator.Tracial.CornerPartition.single`, `OAI.Generator.Tracial.DyadicIndex`, `OAI.Generator.Tracial.EquivalentPartition`, `OAI.Generator.Tracial.EquivalentPartition.matrixVectorFunctional`, `OAI.Generator.Tracial.EquivalentPartition.ofHalving`, `OAI.Generator.Tracial.EquivalentPartition.refine`, `OAI.Generator.Tracial.EquivalentPartition.singleton`, `OAI.Generator.Tracial.EquivalentPartition.stateCoefficient`, `OAI.Generator.Tracial.EquivalentPartition.subset`, `OAI.Generator.Tracial.PartialIsometry`, `OAI.Generator.Tracial.PartialIsometry.Extends`, `OAI.Generator.Tracial.PartialIsometry.adjoint`, `OAI.Generator.Tracial.PartialIsometry.compose`, `OAI.Generator.Tracial.PartialIsometry.onProjection`, `OAI.Generator.Tracial.PartialIsometry.patch`, `OAI.Generator.Tracial.PartialIsometry.target`, `OAI.Generator.Tracial.PartialIsometry.zero`, `OAI.Generator.Tracial.TraceFreePreHilbert`, `OAI.Generator.Tracial.approxTraceCStar`, `OAI.Generator.Tracial.approxTraceLE`, `OAI.Generator.Tracial.cornerStateCStar`, `OAI.Generator.Tracial.cornerStateLE`, `OAI.Generator.Tracial.cornerStateOrder` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Bicommutant`, `FactorGeneration_Coefficients`, `FactorGeneration_Dimension`, `FactorGeneration_DyadicComparison`, `FactorGeneration_FiniteComparison`, `FactorGeneration_HilbertProjections`, `FactorGeneration_LocalizedStates`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_NormalTrace`, `FactorGeneration_OperatorLimits`, `FactorGeneration_PartialIsometries`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionEncoding`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_Supports`, `FactorGeneration_TraceHilbert`, `FreeGroupFactor_Model`, `FreeGroupFactor_Operators`, `RelativeGeneration_OriginalUnitary`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ129G003`, `OAIQ129G004` and `OAIQ129G005`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_FactorGeneration

section
-- module Solutions.OAIQ129_RG2.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Bicommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

abbrev FiniteHilbert (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

def diagonalOperator (T : H →L[ℂ] H) : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_apply (T : H →L[ℂ] H) (x : FiniteHilbert ι H) (i : ι) :
    diagonalOperator T x i=T (x i) := rfl

theorem diagonalOperator_star (T : H →L[ℂ] H) :
    diagonalOperator (ι := ι) (star T)=star (diagonalOperator (ι := ι) T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply,diagonalOperator_apply,
    ContinuousLinearMap.adjoint_inner_right]

def tupleOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    S →ₗ[ℂ] FiniteHilbert ι H where
  toFun a := diagonalOperator a.val x
  map_add' a b := by ext i; rfl
  map_smul' c a := by ext i; rfl

def tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    Submodule ℂ (FiniteHilbert ι H) := (tupleOrbitMap S x).range.topologicalClosure

instance tupleOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : CompleteSpace (tupleOrbitClosure S x) :=
  inferInstanceAs (CompleteSpace (tupleOrbitMap S x).range.topologicalClosure)

theorem mem_tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : x ∈ tupleOrbitClosure S x := by
  apply Submodule.le_topologicalClosure
  refine ⟨1,?_⟩
  ext i
  rfl

theorem tupleOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) {y : FiniteHilbert ι H}
    (hy : y ∈ tupleOrbitClosure S x) : diagonalOperator a.val y ∈ tupleOrbitClosure S x := by
  have h : (tupleOrbitMap S x).range.topologicalClosure ≤
      (tupleOrbitClosure S x).comap (diagonalOperator a.val).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨a*b,?_⟩
      ext i
      rfl
    · exact (Submodule.isClosed_topologicalClosure _).preimage (diagonalOperator a.val).continuous
  exact h hy

theorem starProjection_commutes_of_invariant (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hT : ∀ x ∈ K,T x ∈ K) (hstar : ∀ x ∈ K,star T x ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext x
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (K.starProjection_apply_mem x)
  · intro y hy
    change inner ℂ (T x-T (K.starProjection x)) y=0
    rw [← map_sub]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact K.starProjection_inner_eq_zero x _ (hstar y hy)

theorem tupleOrbitProjection_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) :
    (tupleOrbitClosure S x).starProjection*diagonalOperator a.val=
      diagonalOperator a.val*(tupleOrbitClosure S x).starProjection := by
  apply starProjection_commutes_of_invariant
  · exact fun y hy => tupleOrbitClosure_invariant S x a hy
  · rw [← diagonalOperator_star]
    exact fun y hy => tupleOrbitClosure_invariant S x (star a) hy

variable [DecidableEq ι]

def tupleSingle (i : ι) : H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem tupleSingle_apply (i j : ι) (x : H) :
    tupleSingle i x j=(Pi.single i x : ι → H) j := rfl

omit [CompleteSpace H] in
theorem tuple_eq_sum_single (x : FiniteHilbert ι H) :
    x=∑ i,tupleSingle i (x i) := by
  ext j
  simp [WithLp.ofLp_sum,tupleSingle_apply,Pi.single_apply]

omit [CompleteSpace H] [Fintype ι] in
theorem diagonalOperator_single (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonalOperator T (tupleSingle i x)=tupleSingle i (T x) := by
  ext j
  by_cases h : j=i <;> simp [h]

def operatorEntry (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (Q.comp (tupleSingle j))

omit [Fintype ι] in
theorem operatorEntry_mem_centralizer (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (hQ : ∀ a : S,Q*diagonalOperator a.val=diagonalOperator a.val*Q) (i j : ι) :
    operatorEntry Q i j ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  ext z
  change a (Q (tupleSingle j z) i)=Q (tupleSingle j (a z)) i
  have h := congrArg (fun T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H =>
    T (tupleSingle j z) i) (hQ ⟨a,ha⟩)
  simpa only [mul_apply_eq_comp,diagonalOperator_apply,
    diagonalOperator_single] using h.symm

omit [CompleteSpace H] in
theorem diagonalOperator_commutes_of_entries (T : H →L[ℂ] H)
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (h : ∀ i j,operatorEntry Q i j*T=T*operatorEntry Q i j) :
    Q*diagonalOperator T=diagonalOperator T*Q := by
  ext x i
  rw [tuple_eq_sum_single x]
  simp only [map_sum,mul_apply_eq_comp,diagonalOperator_single]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,diagonalOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : H →L[ℂ] H => a (x j)) (h i j)

theorem bicommutant_tuple_mem_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : FiniteHilbert ι H) : diagonalOperator T x ∈ tupleOrbitClosure S x := by
  let Q := (tupleOrbitClosure S x).starProjection
  have hcomm : Q*diagonalOperator T=diagonalOperator T*Q :=
    diagonalOperator_commutes_of_entries T Q (fun i j => hT _
      (operatorEntry_mem_centralizer S Q (tupleOrbitProjection_commutes S x) i j))
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun a : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H => a x) hcomm
  change Q (diagonalOperator T x)=diagonalOperator T (Q x) at h
  rw [show Q x=x from Submodule.starProjection_eq_self_iff.mpr (mem_tupleOrbitClosure S x)] at h
  exact h

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bicommutant_finite_strong_approximation (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : S,∀ x ∈ s,‖T x-a.val x‖ < ε := by
  classical
  let x : FiniteHilbert s H := WithLp.toLp 2 (fun i : s => i.val)
  have h := bicommutant_tuple_mem_closure S T hT x
  obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp h ε hε
  refine ⟨a,?_⟩
  intro y hy
  have hb := PiLp.norm_apply_le (diagonalOperator T x-tupleOrbitMap S x a) (⟨y,hy⟩ : s)
  exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

theorem bicommutant_exists_strong_net (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ∃ a : Finset H × ℕ → S,∀ x : H,
      Tendsto (fun d => (a d).val x) atTop (𝓝 (T x)) := by
  classical
  have hex (d : Finset H × ℕ) := bicommutant_finite_strong_approximation S T hT d.1
    (1/((d.2 : ℝ)+1)) (by positivity)
  choose a ha using hex
  refine ⟨a,?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun d : Finset H × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun d => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H),0)] with d hd
  rw [dist_comm,dist_eq_norm]
  exact (ha d x (hd.1 (Finset.mem_singleton_self x))).le

theorem wotClosed_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))=S := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨a,ha⟩ := bicommutant_exists_strong_net S T hT
    have hw : Tendsto (fun d => ContinuousLinearMapWOT.ofCLM (a d).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
      apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
      intro x y
      exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha x)
    exact hS.mem_of_tendsto hw (Eventually.of_forall (fun d => (a d).property))
  · intro T hT a ha
    exact (ha T hT).symm

end

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Coefficientwise absolute-value product comparison, retaining all convolution terms contributing to the same group element. -/
section
open scoped BigOperators
variable {G : Type*} [Monoid G]

def normCoefficients (f : MonoidAlgebra ℂ G) : MonoidAlgebra ℝ G :=
  .ofCoeff (f.coeff.mapRange (fun z => ‖z‖) norm_zero)

omit [Monoid G] in
@[simp] theorem normCoefficients_apply (f : MonoidAlgebra ℂ G) (g : G) :
    (normCoefficients f).coeff g = ‖f.coeff g‖ := rfl

end

/-! The coefficientwise ordered ring of real finite group-ring sums.
The multiplication is actual collected convolution. -/
open scoped BigOperators
namespace CoefficientOrder
variable {G : Type*} [Monoid G]

instance coefficientPartialOrder : PartialOrder (MonoidAlgebra ℝ G) :=
  PartialOrder.lift MonoidAlgebra.coeff MonoidAlgebra.coeff_injective

omit [Monoid G] in
@[simp] theorem le_iff (f g : MonoidAlgebra ℝ G) : f ≤ g ↔ ∀ w, f.coeff w ≤ g.coeff w := Iff.rfl

instance coefficientOrderedAdd : IsOrderedAddMonoid (MonoidAlgebra ℝ G) where
  add_le_add_left _f _g h _a w := add_le_add (h w) le_rfl

instance coefficientZeroLEOne : ZeroLEOneClass (MonoidAlgebra ℝ G) where
  zero_le_one := by
    intro w
    classical
    simp only [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> norm_num

end CoefficientOrder

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem base_norm_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

instance baseCompleteSpace (M : VonNeumannAlgebra H) : CompleteSpace M.toStarSubalgebra :=
  (base_norm_closed M).completeSpace_coe

end

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_weak_vector_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (v : ι → H) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    ∃ z : H, ‖z‖ ≤ C ∧ ∀ y : H,
      Tendsto (fun i => inner ℂ y (v i)) (ω : Filter ι) (𝓝 (inner ℂ y z)) := by
  let f : ι → WeakDual ℂ H := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (v i))
  obtain ⟨d, hd, ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) C).ultrafilter_le_nhds
    (ω.map f) (by
      apply le_principal_iff.mpr
      change ∀ᶠ i in (ω : Filter ι), f i ∈ _
      exact Eventually.of_forall fun i => by
        simpa [f, Metric.mem_closedBall, dist_zero_right] using hv i)
  let z := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual d)
  refine ⟨z, ?_, ?_⟩
  · have hd' : ‖WeakDual.toStrongDual d‖ ≤ C := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hd
    simpa only [z, LinearIsometryEquiv.norm_map] using hd'
  · intro y
    have he : Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι)
        (𝓝 (inner ℂ z y)) := by
      have h := (WeakBilin.eval_continuous _ y).continuousAt.tendsto.comp ht
      change Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι) (𝓝 (d y)) at h
      rw [show inner ℂ z y = d y from InnerProductSpace.toDual_symm_apply]
      exact h
    have hs := he.star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ (v i) y)) (ω : Filter ι)
      (𝓝 ((starRingEnd ℂ) (inner ℂ z y))) at hs
    simpa only [inner_conj_symm] using hs

theorem exists_weak_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (a : ι → H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ C ∧ ∀ x y : H,
      Tendsto (fun i => inner ℂ y (a i x)) (ω : Filter ι) (𝓝 (inner ℂ y (T x))) := by
  have h (x : H) := exists_weak_vector_ultralimit ω (fun i => a i x) (C * ‖x‖)
    (fun i => (a i).le_of_opNorm_le (ha i) x)
  choose v hv ht using h
  have hadd (x z : H) : v (x+z) = v x + v z := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x+z) y)
    simpa only [map_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : H) : v (c • x) = c • v x := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, inner_smul_right] using (ht x y).const_mul c
  let T : H →L[ℂ] H := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨T, T.opNorm_le_bound hC hv, ht⟩

/-- The double-commutant property retains the weak limit in the actual algebra. -/
theorem weak_operator_limit_mem (M : VonNeumannAlgebra H)
    {ι : Type*} {l : Filter ι} [l.NeBot] (a : ι → M.toStarSubalgebra)
    (T : H →L[ℂ] H)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i : H →L[ℂ] H) x)) l
      (𝓝 (inner ℂ y (T x)))) : T ∈ M := by
  change T ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro S hS
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have he (i : ι) : inner ℂ y ((a i : H →L[ℂ] H) (S x)) =
      inner ℂ (star S y) ((a i : H →L[ℂ] H) x) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun R : H →L[ℂ] H => inner ℂ y (R x)) (hS (a i) (a i).property)
  have hh := (ht (S x) y).congr he
  have heq := tendsto_nhds_unique hh (ht x (star S y))
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp] using heq.symm

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FreeGroupFactor_Model
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u uG

open scoped ENNReal

abbrev GroupHilbert (G : Type u) := lp (fun _ : G => ℂ) 2
abbrev GroupOperator (G : Type u) := GroupHilbert G →L[ℂ] GroupHilbert G

@[instance_reducible] def ultraweakOperatorTopology (G : Type u) : TopologicalSpace (GroupOperator G) :=
  ⨅ (ξ : lp (fun _ : ℕ => GroupHilbert G) 2)
    (η : lp (fun _ : ℕ => GroupHilbert G) 2),
    TopologicalSpace.induced
      (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (T (ξ k)))
      inferInstance

end FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_42 u_43

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FreeGroupFactor_Operators
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def hilbertReindex {G : Type uG} {H : Type uH} (e : G ≃ H) :
    GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H where
  toFun ξ := ⟨fun h => ξ (e.symm h), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun η := ⟨fun g => η (e g), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp η).summable (by norm_num))⟩
  left_inv ξ := by ext g; simp
  right_inv η := by ext h; simp
  map_add' ξ η := by rfl
  map_smul' c ξ := by rfl
  norm_map' ξ := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change (∑' h : H, ‖ξ (e.symm h)‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) =
      (∑' g : G, ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal))

@[simp] theorem hilbertReindex_apply {G : Type uG} {H : Type uH} (e : G ≃ H)
    (ξ : GroupHilbert G) (h : H) : hilbertReindex e ξ h = ξ (e.symm h) := rfl

def leftRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulLeft g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : leftRegular g ξ h = ξ (g⁻¹ * h) := rfl

@[simp] theorem leftRegular_one {G : Type uG} [Group G] :
    leftRegular (1 : G) = 1 := by
  ext ξ h
  simp

@[simp] theorem leftRegular_mul {G : Type uG} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext ξ b
  simp [mul_assoc]

@[simp] theorem leftRegular_star {G : Type uG} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulLeft g)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (g * b) = ξ ((g⁻¹)⁻¹ * b)
  simp

end FreeGroupFactorMain

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Projections with their algebraic range-inclusion order. -/
def AlgebraProjection (M : VonNeumannAlgebra H) :=
  {p : M.toStarSubalgebra // IsStarProjection p}

instance algebraProjectionPartialOrder : PartialOrder (AlgebraProjection M) where
  le p q := q.val * p.val = p.val
  le_refl p := p.property.isIdempotentElem.eq
  le_trans a b c hab hbc := by
    calc c.val * a.val = c.val * (b.val * a.val) := by rw [hab]
         _ = (c.val * b.val) * a.val := (mul_assoc _ _ _).symm
         _ = a.val := by rw [hbc, hab]
  le_antisymm a b hab hba := by
    apply Subtype.ext
    have h := congrArg star hab
    simp only [star_mul, a.property.isSelfAdjoint.star_eq,
      b.property.isSelfAdjoint.star_eq] at h
    exact h.symm.trans hba

theorem projection_mul_of_le {p q : AlgebraProjection M} (h : p ≤ q) :
    p.val * q.val = p.val := by
  have he := congrArg star h
  simpa only [star_mul, p.property.isSelfAdjoint.star_eq,
    q.property.isSelfAdjoint.star_eq] using he

end

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- At depth n there are 2^n indices; a successor appends a binary branch. -/
def DyadicIndex : ℕ → Type
  | 0 => Unit
  | n+1 => DyadicIndex n × Bool

instance dyadicIndexFintype : (n : ℕ) → Fintype (DyadicIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd _ _ (dyadicIndexFintype n) inferInstance

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

structure PartialIsometry (M : VonNeumannAlgebra H) where
  support : AlgebraProjection M
  val : M.toStarSubalgebra
  initial : star val*val=support.val

namespace PartialIsometry

theorem mul_support (v : PartialIsometry M) : v.val*v.support.val=v.val := by
  have htr : star v.val*(v.val*v.support.val)=v.support.val := by
    rw [← mul_assoc,v.initial,v.support.property.isIdempotentElem.eq]
  have he : star (v.val-v.val*v.support.val)*(v.val-v.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub,
      mul_assoc,v.initial,htr,v.support.property.isIdempotentElem.eq,sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp he)).symm

def target (v : PartialIsometry M) : AlgebraProjection M :=
  ⟨v.val*star v.val,⟨by
    change (v.val*star v.val)*(v.val*star v.val)=v.val*star v.val
    calc _ = (v.val*(star v.val*v.val))*star v.val := by simp only [mul_assoc]
         _ = v.val*star v.val := by rw [v.initial,v.mul_support],
    IsSelfAdjoint.mul_star_self _⟩⟩

theorem target_mul (v : PartialIsometry M) : v.target.val*v.val=v.val := by
  change (v.val*star v.val)*v.val=v.val
  rw [mul_assoc,v.initial,v.mul_support]

def adjoint (v : PartialIsometry M) : PartialIsometry M :=
  ⟨v.target,star v.val,by simp only [star_star]; rfl⟩

theorem norm_le_one (v : PartialIsometry M) : ‖v.val‖ ≤ 1 := by
  have he : ‖v.val‖*‖v.val‖=‖v.support.val‖ := by
    rw [← CStarRing.norm_star_mul_self,v.initial]
  have hp := v.support.property.norm_le
  nlinarith [norm_nonneg v.val]

def Extends (v w : PartialIsometry M) : Prop := w.val*v.support.val=v.val

theorem support_le_of_extends {v w : PartialIsometry M} (h : Extends v w) :
    v.support ≤ w.support := by
  have hh := congrArg (fun z : M.toStarSubalgebra => star z*z) h
  have hcomp : v.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(star w.val*w.val)*v.support.val := by rw [w.initial]
         _ = star (w.val*v.support.val)*(w.val*v.support.val) := by
           simp only [star_mul,v.support.property.isSelfAdjoint.star_eq,mul_assoc]
         _ = v.support.val := hh.trans v.initial
  have hdouble : v.support.val*w.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(w.support.val*w.support.val)*v.support.val := by
           simp only [mul_assoc]
         _ = v.support.val := by rw [w.support.property.isIdempotentElem.eq,hcomp]
  have hz : star (v.support.val-w.support.val*v.support.val)*
      (v.support.val-w.support.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,
      w.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub]
    simp only [← mul_assoc,v.support.property.isIdempotentElem.eq,hcomp,hdouble,
      sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)).symm

theorem cross_initial {v w : PartialIsometry M} (h : Extends v w) :
    star w.val*v.val=v.support.val := by
  calc star w.val*v.val = star w.val*(w.val*v.support.val) := by rw [h]
       _ = v.support.val := by rw [← mul_assoc,w.initial]; exact support_le_of_extends h

theorem cross_initial_rev {v w : PartialIsometry M} (h : Extends v w) :
    star v.val*w.val=v.support.val := by
  simpa only [star_mul,star_star,v.support.property.isSelfAdjoint.star_eq]
    using congrArg star (cross_initial h)

theorem extends_refl (v : PartialIsometry M) : Extends v v := v.mul_support

theorem extends_trans {u v w : PartialIsometry M} (huv : Extends u v) (hvw : Extends v w) :
    Extends u w := by
  change w.val*u.support.val=u.val
  calc w.val*u.support.val = w.val*(v.support.val*u.support.val) := by
         rw [show v.support.val*u.support.val=u.support.val from support_le_of_extends huv]
       _ = u.val := by rw [← mul_assoc,hvw,huv]

@[ext] theorem ext {v w : PartialIsometry M} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by
    apply Subtype.ext
    calc v.support.val = star v.val*v.val := v.initial.symm
         _ = star w.val*w.val := by rw [h]
         _ = w.support.val := w.initial
  cases v
  cases w
  cases hp
  cases h
  rfl

instance instPartialOrder : PartialOrder (PartialIsometry M) where
  le := Extends
  le_refl := extends_refl
  le_trans _ _ _ := extends_trans
  le_antisymm v w hvw hwv := by
    apply ext
    have hs := le_antisymm (support_le_of_extends hvw) (support_le_of_extends hwv)
    change w.val*v.support.val=v.val at hvw
    rw [hs,w.mul_support] at hvw
    exact hvw.symm

theorem support_mono {v w : PartialIsometry M} (h : v ≤ w) : v.support ≤ w.support :=
  support_le_of_extends h

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Orthogonal patching with distinct source and target supports. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

def zero : PartialIsometry M := ⟨⟨0,IsStarProjection.zero _⟩,0,by simp⟩

theorem support_le_iff_mul (v : PartialIsometry M) (p : AlgebraProjection M) :
    v.support ≤ p ↔ v.val*p.val=v.val := by
  constructor
  · intro h
    calc _ = (v.val*v.support.val)*p.val := by rw [v.mul_support]
         _ = v.val := by rw [mul_assoc,projection_mul_of_le h,v.mul_support]
  · intro h
    have he : v.support.val*p.val=v.support.val := by
      rw [← v.initial,mul_assoc,h]
    change p.val*v.support.val=v.support.val
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
      v.support.property.isSelfAdjoint.star_eq] using congrArg star he

theorem target_le_iff_mul (v : PartialIsometry M) (q : AlgebraProjection M) :
    v.target ≤ q ↔ q.val*v.val=v.val := by
  constructor
  · intro h
    calc _ = q.val*(v.target.val*v.val) := by rw [v.target_mul]
         _ = v.val := by rw [← mul_assoc,h,v.target_mul]
  · intro h
    change q.val*(v.val*star v.val)=v.val*star v.val
    rw [← mul_assoc,h]

theorem mul_eq_zero (v w : PartialIsometry M) (h : v.support.val*w.target.val=0) :
    v.val*w.val=0 := by
  calc _ = (v.val*v.support.val)*(w.target.val*w.val) := by
         rw [v.mul_support,w.target_mul]
       _ = v.val*(v.support.val*w.target.val)*w.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

theorem orthogonal_reverse (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q.val*p.val=0 := by
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    q.property.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    PartialIsometry M where
  support := ⟨v.support.val+w.support.val,v.support.property.add w.support.property hp⟩
  val := v.val+w.val
  initial := by
    have h₁ : star v.val*w.val=0 := v.adjoint.mul_eq_zero w hq
    have h₂ : star w.val*v.val=0 :=
      w.adjoint.mul_eq_zero v (orthogonal_reverse _ _ hq)
    simp only [star_add,add_mul,mul_add,v.initial,w.initial,h₁,h₂,add_zero,zero_add]

theorem patch_target (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    (patch v w hp hq).target.val=v.target.val+w.target.val := by
  have hwt : w.adjoint.target=w.support := Subtype.ext (by
    change star w.val*star (star w.val)=w.support.val
    rw [star_star,w.initial])
  have hvt : v.adjoint.target=v.support := Subtype.ext (by
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial])
  have h₁ : v.val*star w.val=0 := v.mul_eq_zero w.adjoint (by rw [hwt]; exact hp)
  have h₂ : w.val*star v.val=0 := w.mul_eq_zero v.adjoint (by
    rw [hvt]; exact orthogonal_reverse _ _ hp)
  change (v.val+w.val)*star (v.val+w.val)=v.val*star v.val+w.val*star w.val
  simp only [star_add,add_mul,mul_add,h₁,h₂,add_zero,zero_add]

theorem le_patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    v ≤ patch v w hp hq := by
  have hw : w.val*v.support.val=0 := by
    calc _ = (w.val*w.support.val)*v.support.val := by rw [w.mul_support]
         _ = 0 := by rw [mul_assoc,orthogonal_reverse _ _ hp,mul_zero]
  change (v.val+w.val)*v.support.val=v.val
  rw [add_mul,v.mul_support,hw,add_zero]

theorem patch_ne (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0)
    (hw : w.support.val≠0) : patch v w hp hq ≠ v := by
  intro he
  have hh := congrArg (fun z : PartialIsometry M => z.support.val) he
  change v.support.val+w.support.val=v.support.val at hh
  exact hw (add_left_cancel (hh.trans (add_zero _).symm))

end PartialIsometry

end

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Supports
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.tupleOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The orthogonal projection onto an operator's kernel belongs to its
von Neumann algebra. This uses the actual double-commutant definition. -/
theorem kernelProjection_mem (x : M.toStarSubalgebra) :
    (x.val.ker).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro y hy
  rw [Submodule.range_starProjection]
  intro ξ hξ
  change x.val (y ξ)=0
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hy) x.val x.property
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) hc
  change x.val (y ξ)=y (x.val ξ) at he
  rw [he,show x.val ξ=0 from hξ,map_zero]

def kernelProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨⟨x.val.ker.starProjection,kernelProjection_mem x⟩,by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isSelfAdjoint.star_eq⟩

/-- The projection onto the closed range of x, expressed via ker(x*). -/
def rangeProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨1-(kernelProjection (star x)).val,(kernelProjection (star x)).property.one_sub⟩

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_isometric_range_factor (a x : H →L[ℂ] H)
    (hnorm : ∀ ξ, ‖x ξ‖ = ‖a ξ‖) :
    ∃ v : H →L[ℂ] H, v * a = x ∧
      star v * v = a.range.topologicalClosure.starProjection ∧
      v * a.range.topologicalClosure.starProjection = v := by
  let K := a.range.topologicalClosure
  let e : a.range →L[ℂ] K :=
    ⟨Submodule.inclusion a.range.le_topologicalClosure,
      continuous_inclusion a.range.le_topologicalClosure⟩
  have hd : DenseRange e :=
    (denseRange_inclusion_iff a.range.le_topologicalClosure).mpr (by rfl)
  have he : IsUniformInducing e :=
    (show Isometry e from fun _ _ => rfl).isUniformInducing
  let f : a.range →L[ℂ] H := x.toLinearMap.compLeftInverse a.toLinearMap
  have hf (ξ : H) : f ⟨a ξ, ⟨ξ, rfl⟩⟩ = x ξ :=
    LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨1, by simp [hnorm]⟩ _ _ rfl
  let g : K →L[ℂ] H := f.extend e
  have hg (ξ : H) : g (e ⟨a ξ, ⟨ξ, rfl⟩⟩) = x ξ :=
    (ContinuousLinearMap.extend_eq f hd he _).trans (hf ξ)
  have hgNorm : ∀ ξ : K, ‖g ξ‖ = ‖ξ‖ := by
    intro ξ
    refine hd.induction_on (p := fun ζ : K => ‖g ζ‖=‖ζ‖) ξ
      (isClosed_eq (g.continuous.norm) continuous_norm) ?_
    rintro ⟨_, ζ, rfl⟩
    exact (congrArg norm (hg ζ)).trans (hnorm ζ)
  let v : H →L[ℂ] H := g.comp K.orthogonalProjectionOnto
  have hva : v * a = x := by
    ext ξ
    change g (K.orthogonalProjectionOnto (a ξ)) = x ξ
    have hh : K.orthogonalProjectionOnto (a ξ) = e ⟨a ξ, ⟨ξ,rfl⟩⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr
        (a.range.le_topologicalClosure ⟨ξ,rfl⟩)
    rw [hh,hg]
  have hvs : v * K.starProjection = v := by
    ext ξ
    change g (K.orthogonalProjectionOnto (K.starProjection ξ)) =
      g (K.orthogonalProjectionOnto ξ)
    congr 1
    exact K.orthogonalProjectionOnto_mem_subspace_eq_self _
  refine ⟨v,hva,?_,hvs⟩
  have heq : (star v * v).toLinearMap = K.starProjection.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro ξ
    change inner ℂ ((star v) (v ξ)) ξ = inner ℂ (K.starProjection ξ) ξ
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K]
    change (‖g (K.orthogonalProjectionOnto ξ)‖ : ℂ)^2 = _
    rw [hgNorm]
    have hh := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (𝕜 := ℂ) (K.orthogonalProjectionOnto ξ) ξ
    rw [inner_self_eq_norm_sq_to_K] at hh
    rw [Submodule.starProjection_apply]
    exact hh
  ext ξ
  exact congrArg (fun t : H →ₗ[ℂ] H => t ξ) heq

end

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance polarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance polarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem mul_closure_range_projection_eq_zero (a b : H →L[ℂ] H) (h : b*a=0) :
    b*a.range.topologicalClosure.starProjection=0 := by
  have hr : a.range ≤ b.ker := by
    rintro _ ⟨ξ,rfl⟩
    exact congrArg (fun t : H →L[ℂ] H => t ξ) h
  have hc : a.range.topologicalClosure ≤ b.ker :=
    a.range.topologicalClosure_minimal hr b.isClosed_ker
  ext ξ
  exact hc (Submodule.starProjection_apply_mem _ ξ)

end

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarSupportsCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance polarSupportsOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FiniteComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/
namespace Tracial

/-! Trace-free upper bounds of arbitrary directed nets of partial isometries.
A weak operator ultralimit suffices: extension identities with each fixed net
member force the limit to satisfy b b* b = b. No trace or countability is used. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Left multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_left {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((c*a i).val x)) l
      (𝓝 (inner ℂ y ((c*b).val x))) := by
  intro x y
  change Tendsto (fun i => inner ℂ y (c.val ((a i).val x))) l
    (𝓝 (inner ℂ y (c.val (b.val x))))
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    using ht x (star c.val y)

/-- Right multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_right {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i*c).val x)) l
      (𝓝 (inner ℂ y ((b*c).val x))) := fun x y => ht (c.val x) y

/-- Matrix coefficients determine an element of the concrete algebra. -/
theorem wot_limit_unique {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x))))
    (hc : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (c.val x)))) : b=c := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact ext_inner_left ℂ (fun y => tendsto_nhds_unique (hb x y) (hc x y))

end

/-! Trace-free chain upper bounds and maximal partial isometries, with prescribed
initial and final projection bounds. The index set may be uncountable. -/

/-! Projection comparison from scalar center, without a supplied trace.
The maximal partial isometry, central support and polar linking are constructed. -/

end Tracial

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- The identity partial isometry on a projection. -/
def onProjection (p : AlgebraProjection M) : PartialIsometry M :=
  ⟨p, p.val, by rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]⟩

theorem onProjection_target (p : AlgebraProjection M) : (onProjection p).target=p := by
  apply Subtype.ext
  change p.val*star p.val=p.val
  rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]

end PartialIsometry
end Tracial

end

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Orthogonality passes to subprojections in both variables. -/
theorem projection_orthogonal_of_le {p q r s : AlgebraProjection M}
    (h : p.val*q.val=0) (hr : r ≤ p) (hs : s ≤ q) : r.val*s.val=0 := by
  calc _ = (r.val*p.val)*(q.val*s.val) := by rw [projection_mul_of_le hr,hs]
       _ = r.val*(p.val*q.val)*s.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

namespace PartialIsometry

theorem target_mono {v w : PartialIsometry M} (h : v ≤ w) : v.target ≤ w.target := by
  apply (v.target_le_iff_mul w.target).mpr
  calc _ = w.target.val*(w.val*v.support.val) := by rw [h]
       _ = v.val := by rw [← mul_assoc,w.target_mul,h]

/-- A directed increasing family of square-zero partial isometries has an
upper bound with orthogonal initial/final projections inside p. -/
theorem traceFree_orthogonal_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ p)
    (ho : ∀ i, (a i).support.val*(a i).target.val=0) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  have hcross (i j : ι) : (a i).val*(a j).val=0 := by
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    exact (a i).mul_eq_zero (a j)
      (projection_orthogonal_of_le (ho k) (support_mono (ha hik)) (target_mono (ha hjk)))
  have hbi (i : ι) : b*(a i).val=0 := by
    apply wot_limit_unique (fun j => (a j).val*(a i).val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [hcross] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  have hbb : b*b=0 := by
    apply wot_limit_unique (fun i => b*(a i).val) _ _ (wot_limit_mul_left _ _ _ hb)
    simpa only [hbi] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  refine ⟨v, hbp, ?_, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => p.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul p).mp (hq i)] using hb
  · change (star b*b)*(b*star b)=0
    calc _ = star b*(b*b)*star b := by simp only [mul_assoc]
         _ = 0 := by rw [hbb,mul_zero,zero_mul]

theorem traceFree_orthogonal_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ p)
    (ho : ∀ v ∈ c, v.support.val*v.target.val=0) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨v,hv,hvp,hvq,hvo⟩ := traceFree_orthogonal_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
    (fun w => ho w.val w.property)
  exact ⟨v,fun w hw => hv ⟨w,hw⟩,hvp,hvq,hvo⟩

theorem traceFree_exists_maximal_orthogonal (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ p →
        w.support.val*w.target.val=0 → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) :=
    {v | v.support ≤ p ∧ v.target ≤ p ∧ v.support.val*v.target.val=0}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v,hcv,hvp,hvq,hvo⟩ := traceFree_orthogonal_chain_upper_bound c hchain hne p
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2.1) (fun w hw => (hc hw).2.2)
      exact ⟨v,⟨hvp,hvq,hvo⟩,hcv⟩
    · refine ⟨zero,⟨?_,?_,?_⟩,?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul p).mpr
        exact mul_zero _
      · exact zero_mul _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2.1,hv.1.2.2,fun w hp hq ho h => hv.2 ⟨hp,hq,ho⟩ h⟩

/-! Simultaneous least initial and final support bounds for arbitrary directed
partial-isometry nets. The actual ultralimit is chosen once for all bounds. -/

end PartialIsometry
end Tracial

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance unitaryPolarCStar : CStarAlgebra M.toStarSubalgebra := {}

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- The sum of two orthogonal projections, in the original algebra. -/
def orthogonalSum (p q : AlgebraProjection M) (h : p.val*q.val=0) : AlgebraProjection M :=
  ⟨p.val+q.val,p.property.add q.property h⟩

theorem le_orthogonalSum_left (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    p ≤ orthogonalSum p q h := by
  change (p.val+q.val)*p.val=p.val
  rw [add_mul,p.property.isIdempotentElem.eq,PartialIsometry.orthogonal_reverse _ _ h,add_zero]

theorem le_orthogonalSum_right (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q ≤ orthogonalSum p q h := by
  change (p.val+q.val)*q.val=q.val
  rw [add_mul,h,q.property.isIdempotentElem.eq,zero_add]

theorem orthogonalSum_le {p q r : AlgebraProjection M} (h : p.val*q.val=0)
    (hp : p ≤ r) (hq : q ≤ r) : orthogonalSum p q h ≤ r := by
  change r.val*(p.val+q.val)=p.val+q.val
  rw [mul_add,hp,hq]

end Tracial

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- Composition with range contained in the initial projection. -/
def compose (v w : PartialIsometry M) (h : w.target ≤ v.support) : PartialIsometry M where
  support := w.support
  val := v.val*w.val
  initial := by
    calc star (v.val*w.val)*(v.val*w.val) = star w.val*(star v.val*v.val)*w.val := by
           simp only [star_mul,mul_assoc]
         _ = star w.val*w.val := by
           rw [v.initial,mul_assoc,(w.target_le_iff_mul v.support).mp h]
         _ = w.support.val := w.initial

theorem compose_target (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target.val=v.val*w.target.val*star v.val := by
  change (v.val*w.val)*star (v.val*w.val)=v.val*(w.val*star w.val)*star v.val
  simp only [star_mul,mul_assoc]

theorem compose_target_le (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target ≤ v.target := by
  apply ((compose v w h).target_le_iff_mul v.target).mpr
  change v.target.val*(v.val*w.val)=v.val*w.val
  rw [← mul_assoc,v.target_mul]

end PartialIsometry

/-- A partition of p with actual partial isometries from a common projection.
The cross identities encode orthogonality. This structure is constructed below. -/
structure EquivalentPartition (p : AlgebraProjection M) (ι : Type*) [Fintype ι] where
  base : AlgebraProjection M
  leg : ι → PartialIsometry M
  initial : ∀ i, (leg i).support=base
  cross : ∀ i j, i≠j → star (leg i).val*(leg j).val=0
  total : ∑ i, (leg i).target.val=p.val
  bound : ∀ i, (leg i).target ≤ p

namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem orthogonal (E : EquivalentPartition p ι) (i j : ι) (hij : i≠j) :
    (E.leg i).target.val*(E.leg j).target.val=0 := by
  change ((E.leg i).val*star (E.leg i).val)*((E.leg j).val*star (E.leg j).val)=0
  calc _ = (E.leg i).val*(star (E.leg i).val*(E.leg j).val)*star (E.leg j).val := by
           simp only [mul_assoc]
       _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]

/-- Refinement is performed on the common initial corner and transported. -/
def refine (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) :
    EquivalentPartition p (ι × κ) where
  base := F.base
  leg a := (E.leg a.1).compose (F.leg a.2) (by rw [E.initial]; exact F.bound a.2)
  initial a := F.initial a.2
  cross a b hab := by
    change star ((E.leg a.1).val*(F.leg a.2).val)*
      ((E.leg b.1).val*(F.leg b.2).val)=0
    rw [star_mul]
    have hr : (star (F.leg a.2).val*star (E.leg a.1).val)*
        ((E.leg b.1).val*(F.leg b.2).val)=
        star (F.leg a.2).val*(star (E.leg a.1).val*(E.leg b.1).val)*(F.leg b.2).val := by
      simp only [mul_assoc]
    rw [hr]
    by_cases h : a.1=b.1
    · rw [h,(E.leg b.1).initial,E.initial,mul_assoc,
        ((F.leg b.2).target_le_iff_mul E.base).mp (F.bound b.2)]
      exact F.cross a.2 b.2 (fun hh => hab (Prod.ext h hh))
    · rw [E.cross a.1 b.1 h,mul_zero,zero_mul]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
    have h (i : ι) : (E.leg i).val*E.base.val=(E.leg i).val := by
      rw [← E.initial i,(E.leg i).mul_support]
    simp only [h]
    exact E.total
  bound a := ((E.leg a.1).compose_target_le (F.leg a.2) _).trans (E.bound a.1)

/-- Depth zero consists of the original projection itself. -/
def singleton (p : AlgebraProjection M) : EquivalentPartition p Unit where
  base := p
  leg _ := PartialIsometry.onProjection p
  initial _ := rfl
  cross i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp only [PartialIsometry.onProjection_target,Fintype.sum_unique]
  bound _ := by rw [PartialIsometry.onProjection_target]

/-- Two equivalent orthogonal halves, as a family with a common initial corner. -/
def ofHalving (v : PartialIsometry M) (ho : v.support.val*v.target.val=0)
    (hp : v.support.val+v.target.val=p.val) : EquivalentPartition p Bool where
  base := v.support
  leg b := if b then v else PartialIsometry.onProjection v.support
  initial b := by cases b <;> rfl
  cross b c hbc := by
    have h : v.support.val*v.val=0 := by
      calc _ = v.support.val*(v.target.val*v.val) := by rw [v.target_mul]
           _ = 0 := by rw [← mul_assoc,ho,zero_mul]
    cases b <;> cases c
    · exact (hbc rfl).elim
    · simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,PartialIsometry.onProjection,
        v.support.property.isSelfAdjoint.star_eq] using h
    · simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,PartialIsometry.onProjection,
        star_mul,star_zero,v.support.property.isSelfAdjoint.star_eq] using congrArg star h
    · exact (hbc rfl).elim
  total := by
    simp only [Fintype.sum_bool,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,
      PartialIsometry.onProjection_target]
    exact (add_comm _ _).trans hp
  bound b := by
    have he : orthogonalSum v.support v.target ho=p := Subtype.ext hp
    cases b
    · simpa only [Bool.false_eq_true,ite_false, if_false,PartialIsometry.onProjection_target,he]
        using le_orthogonalSum_left v.support v.target ho
    · simpa only [ite_true, if_true,he] using le_orthogonalSum_right v.support v.target ho

end EquivalentPartition
end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace AlgebraProjection

def Subequivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target ≤ q

end AlgebraProjection

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem exists_finsetSum {ι : Type*} (a : ι → PartialIsometry M) (s : Finset ι)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).support.val*(a j).support.val=0)
    (hq : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).target.val*(a j).target.val=0) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ s, (a i).val ∧
      v.support.val=∑ i ∈ s, (a i).support.val ∧
      v.target.val=∑ i ∈ s, (a i).target.val := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨zero,by simp [zero],by simp [zero],by simp [zero,target]⟩
  | @insert i s hi ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
      (fun j hj k hk => hp j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj k hk => hq j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
    have ho₁ : (a i).support.val*v.support.val=0 := by
      rw [hs,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hp i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    have ho₂ : (a i).target.val*v.target.val=0 := by
      rw [ht,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hq i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    refine ⟨(a i).patch v ho₁ ho₂,?_,?_,?_⟩
    · change (a i).val+v.val=_
      rw [hv,Finset.sum_insert hi]
    · change (a i).support.val+v.support.val=_
      rw [hs,Finset.sum_insert hi]
    · rw [patch_target,ht,Finset.sum_insert hi]

end PartialIsometry
namespace AlgebraProjection

theorem isStarProjection_sum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) :
    IsStarProjection (∑ i ∈ s, (a i).val) := by
  obtain ⟨v,_,hs,_⟩ := PartialIsometry.exists_finsetSum
    (fun i => PartialIsometry.onProjection (a i)) s ho
    (by simpa only [PartialIsometry.onProjection_target] using ho)
  change v.support.val=(∑ i ∈ s, (a i).val) at hs
  exact hs ▸ v.support.property

def finsetSum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) : AlgebraProjection M :=
  ⟨∑ i ∈ s, (a i).val,isStarProjection_sum a s ho⟩

end AlgebraProjection
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

def subset (E : EquivalentPartition p ι) (s : Finset ι) : AlgebraProjection M :=
  AlgebraProjection.finsetSum (fun i => (E.leg i).target) s
    (fun i _ j _ => E.orthogonal i j)

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

end EquivalentPartition
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

def dyadicWeight (n : ℕ) (s : Finset (DyadicIndex n)) : ℝ := (s.card : ℝ)/2^n

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertProjections
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Baire continuity points from rational sublevel boundaries, without a global boundedness assumption. -/

/-! Hilbert-space projection and correlation identities. The inner product is conjugate-linear in its first argument, so `inner ℂ ξ W` represents τ(ξ* W). -/

/-! Lower semicontinuity from a continuous family dense in each projected subspace. -/
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def normalizedCorrelation (ξ w : E) : ℝ := ‖inner ℂ ξ w‖ / ‖w‖

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- A finite projection partition of a corner, allowing zero pieces. -/
structure CornerPartition (p : AlgebraProjection M) where
  size : ℕ
  piece : Fin size → AlgebraProjection M
  orthogonal : ∀ i j, i ≠ j → (piece i).val * (piece j).val = 0
  total : ∑ i, (piece i).val = p.val

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

def pinch (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  ∑ i, (Q.piece i).val * x * (Q.piece i).val

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

/-- The partition with its corner as its only piece. -/
def single (p : AlgebraProjection M) : CornerPartition p where
  size := 1
  piece _ := p
  orthogonal i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp

@[simp] theorem single_pinch (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    (single p).pinch x = p.val*x*p.val := by
  change (∑ _ : Fin 1, p.val*x*p.val) = _
  simp

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerValueCStar : CStarAlgebra M.toStarSubalgebra := {}

local instance cornerValueOrder_r616f41_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerValuePreorder_r616f41_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerValueLE_r616f41_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerValueStarOrder_r616f41_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
/-- The actual bounded complex-linear vector functional on the original algebra. -/
def vectorFunctional (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => inner ℂ ξ (x.val ξ)
      map_add' := fun x y => inner_add_right _ _ _
      map_smul' := fun c x => inner_smul_right _ _ _ }
    (‖ξ‖^2) (fun x => by
      calc ‖inner ℂ ξ (x.val ξ)‖ ≤ ‖ξ‖*‖x.val ξ‖ := norm_inner_le_norm _ _
           _ ≤ ‖ξ‖*(‖x.val‖*‖ξ‖) := mul_le_mul_of_nonneg_left (x.val.le_opNorm ξ) (norm_nonneg _)
           _ = ‖ξ‖^2*‖x‖ := by change ‖ξ‖*(‖x‖*‖ξ‖)=_; ring)

theorem vectorFunctional_apply (ξ : H) (x : M.toStarSubalgebra) :
    vectorFunctional ξ x=inner ℂ ξ (x.val ξ) := rfl

theorem vectorFunctional_norm_le (ξ : H) : ‖vectorFunctional (M := M) ξ‖ ≤ ‖ξ‖^2 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance cornerStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance cornerStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance cornerStatePreorder_r616f41_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance cornerStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance cornerStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

/-- Matrix coefficient in the common initial corner. -/
def stateCoefficient (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    M.toStarSubalgebra := star (Q.leg i).val*x*(Q.leg j).val

theorem stateCoefficient_left (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.base.val*Q.stateCoefficient x i j=Q.stateCoefficient x i j := by
  have hs : Q.base.val*star (Q.leg i).val=star (Q.leg i).val := by
    have h := congrArg star (Q.leg i).mul_support
    simpa only [star_mul,Q.initial,Q.base.property.isSelfAdjoint.star_eq] using h
  change Q.base.val*(star (Q.leg i).val*x*(Q.leg j).val)=_
  rw [← mul_assoc,← mul_assoc,hs]
  rfl

theorem stateCoefficient_right (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient x i j*Q.base.val=Q.stateCoefficient x i j := by
  change (star (Q.leg i).val*x*(Q.leg j).val)*Q.base.val=_
  rw [mul_assoc,← Q.initial j,(Q.leg j).mul_support]
  rfl

theorem stateCoefficient_star (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    star (Q.stateCoefficient x i j)=Q.stateCoefficient (star x) j i := by
  simp only [stateCoefficient,star_mul,star_star,mul_assoc]

theorem stateCoefficient_mul (Q : EquivalentPartition p ι) (hp : p.val=1)
    (x y : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient (x*y) i j=∑ k, Q.stateCoefficient x i k*Q.stateCoefficient y k j := by
  have he (k : ι) : Q.stateCoefficient x i k*Q.stateCoefficient y k j=
      star (Q.leg i).val*x*(Q.leg k).target.val*y*(Q.leg j).val := by
    simp only [stateCoefficient,PartialIsometry.target,mul_assoc]
  simp only [he]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,Q.total,hp,mul_one]
  simp only [stateCoefficient,mul_assoc]

/-- An actual finite sum of bounded vector functionals. -/
def matrixVectorFunctional (Q : EquivalentPartition p ι) (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  ∑ i, vectorFunctional ((Q.leg i).val.val ξ)

theorem matrixVectorFunctional_apply (Q : EquivalentPartition p ι) (ξ : H) (x : M.toStarSubalgebra) :
    Q.matrixVectorFunctional ξ x=∑ i, vectorFunctional ξ (Q.stateCoefficient x i i) := by
  change (∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x=_
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))=
    inner ℂ ξ (star (Q.leg i).val.val (x.val ((Q.leg i).val.val ξ)))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem matrixVectorFunctional_one (Q : EquivalentPartition p ι) (ξ : H) :
    Q.matrixVectorFunctional ξ 1=(∑ i, ‖(Q.leg i).val.val ξ‖^2 : ℝ) := by
  simp only [matrixVectorFunctional,sum_apply,vectorFunctional_apply]
  change (∑ i, inner ℂ ((Q.leg i).val.val ξ) ((Q.leg i).val.val ξ))=_
  simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_sum,Complex.ofReal_pow]
  norm_cast

theorem matrixVectorFunctional_norm_le (Q : EquivalentPartition p ι) (ξ : H) :
    ‖Q.matrixVectorFunctional ξ‖ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 := by
  change ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤ _
  calc ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤
      ∑ i, ‖vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ :=
        norm_sum_le Finset.univ (fun i : ι => vectorFunctional (M := M) ((Q.leg i).val.val ξ))
    _ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 :=
      Finset.sum_le_sum (fun i _ => vectorFunctional_norm_le (M := M) ((Q.leg i).val.val ξ))

theorem matrixVectorFunctional_nearly_cyclic (Q : EquivalentPartition p ι) (hp : p.val=1)
    (ξ : H) (ε : ℝ)
    (hcorner : ∀ x : M.toStarSubalgebra, Q.base.val*x=x → x*Q.base.val=x →
      (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re)
    (x : M.toStarSubalgebra) :
    (Q.matrixVectorFunctional ξ (star x*x)).re ≤
      (1+ε)*(Q.matrixVectorFunctional ξ (x*star x)).re := by
  have hl : (Q.matrixVectorFunctional ξ (star x*x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (star (Q.stateCoefficient x j i)*Q.stateCoefficient x j i)).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Q.stateCoefficient_star]
  have hr : (Q.matrixVectorFunctional ξ (x*star x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (Q.stateCoefficient x j i*star (Q.stateCoefficient x j i))).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    simp_rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_star]
  rw [hl,hr,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => hcorner (Q.stateCoefficient x j i)
    (Q.stateCoefficient_left x j i) (Q.stateCoefficient_right x j i))

end EquivalentPartition
end

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance approxTraceCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance approxTraceOrder_r616f41_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approxTracePreorder_r616f41_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approxTraceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators
namespace Bell
variable {n : ℕ} [NeZero n]

theorem char_sum (t : ZMod n) :
    (∑ i : ZMod n, ZMod.stdAddChar (t*i)) = if t=0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

theorem char_star (t : ZMod n) : star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle t)).symm

def projection (s f : ZMod n) : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ :=
  fun a b => if a.2=a.1+s ∧ b.2=b.1+s then
    (n : ℂ)⁻¹ * ZMod.stdAddChar (f*(a.1-b.1)) else 0

theorem projection_star (s f : ZMod n) : star (projection s f) = projection s f := by
  ext a b
  change star (projection s f b a)=projection s f a b
  simp only [projection, apply_ite star, star_mul, char_star, star_zero]
  rw [show -(f*(b.1-a.1))=f*(a.1-b.1) by ring]
  simp [and_comm, mul_comm]

theorem projection_mul (s f t g : ZMod n) :
    projection s f * projection t g = if s=t ∧ f=g then projection s f else 0 := by
  ext a b
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, projection]
  have hterm (i j : ZMod n) :
      (if a.2=a.1+s ∧ j=i+s then (n : ℂ)⁻¹*ZMod.stdAddChar (f*(a.1-i)) else 0) *
      (if j=i+t ∧ b.2=b.1+t then (n : ℂ)⁻¹*ZMod.stdAddChar (g*(i-b.1)) else 0) =
      if a.2=a.1+s ∧ b.2=b.1+t ∧ s=t then
        if j=i+s then (n : ℂ)⁻¹^2 *
          ZMod.stdAddChar (f*a.1-g*b.1) * ZMod.stdAddChar ((g-f)*i) else 0
      else 0 := by
    by_cases ha : a.2=a.1+s
    · by_cases hb : b.2=b.1+t
      · by_cases hs : s=t
        · subst t
          by_cases hj : j=i+s
          · simp only [ha,hb,hj,and_self,ite_true, if_true]
            calc
              _ = (n : ℂ)⁻¹^2 * (ZMod.stdAddChar (f*(a.1-i)) *
                    ZMod.stdAddChar (g*(i-b.1))) := by ring
              _ = _ := by
                rw [← AddChar.map_add_eq_mul,
                  show f*(a.1-i)+g*(i-b.1)=(f*a.1-g*b.1)+(g-f)*i by ring,
                  AddChar.map_add_eq_mul]
                ring
          · simp [ha,hb,hj]
        · by_cases hj : j=i+s
          · simp [ha,hb,hs,hj]
          · simp [ha,hb,hs,hj]
      · simp [hb]
    · simp [ha]
  simp_rw [hterm]
  by_cases hs : s=t
  · subst t
    by_cases ha : a.2=a.1+s ∧ b.2=b.1+s
    · simp only [ha.1,ha.2,and_self,ite_true, if_true,Finset.sum_ite_eq',Finset.mem_univ]
      rw [← Finset.mul_sum, char_sum]
      by_cases hf : f=g
      · subst g
        simp only [sub_self,ite_true, if_true,Matrix.ite_apply,Matrix.zero_apply, and_self, projection, ha, ite_true]
        rw [show f*a.1-f*b.1=f*(a.1-b.1) by ring]
        field_simp
      · simp [sub_eq_zero,Ne.symm hf,hf]
    · simp [ha,Matrix.ite_apply,projection]
  · simp [hs]

theorem projection_total : (∑ s : ZMod n, ∑ f : ZMod n, projection s f) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.one_apply]
  have hf (s : ZMod n) : (∑ f : ZMod n, projection s f a b) =
      if a.2=a.1+s ∧ b.2=b.1+s ∧ a.1=b.1 then 1 else 0 := by
    simp only [projection]
    by_cases h : a.2=a.1+s ∧ b.2=b.1+s
    · simp only [h.1,h.2,and_self,true_and,ite_true, if_true]
      rw [← Finset.mul_sum]
      simp_rw [mul_comm _ (a.1-b.1)]
      rw [char_sum]
      by_cases hab : a.1=b.1
      · simp [hab]
      · simp [hab,sub_eq_zero]
    · simp [h,show ¬(a.2=a.1+s ∧ b.2=b.1+s ∧ a.1=b.1) by tauto]
  simp_rw [hf]
  by_cases hab : a.1=b.1
  · have hs (s : ZMod n) : a.2=a.1+s ↔ s=a.2-a.1 := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; abel
    simp_rw [hs]
    simp only [hab, and_true]
    simp_rw [ite_and]
    simp [Prod.ext_iff,hab,eq_comm]
  · simp [hab,show a≠b by exact fun h => hab (congrArg Prod.fst h)]

/-- The matrix unit in the first tensor factor, with identity on the second. -/
def leftEntry (i j : ZMod n) : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ :=
  fun a b => if a.1=i ∧ b.1=j ∧ a.2=b.2 then 1 else 0

end Bell

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceCStar : CStarAlgebra M.toStarSubalgebra := {}

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A separated idempotent is recovered from commutation with a norm-small
perturbation. This is an elementary substitute for the spectral-cut step. -/

/-! Countably many commuting projections have one self-adjoint generator.
We use coefficients 3*4^(-(n+1)), whose strict gap admits direct norm recovery
through the double commutant. No trace, tensor model, or uniqueness is used. -/
namespace CommutingProjectionEncoding
open scoped BigOperators Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weight (n : ℕ) : ℝ := (3/4)*(1/4)^n

def tail (e : ℕ → (H →L[ℂ] H)) (n : ℕ) : (H →L[ℂ] H) := ∑' k, weight (n+k) • e (n+k)

end CommutingProjectionEncoding

/-! The spectral separation step as an exact membership theorem for literal W*. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Algebraic type copy indexed by the original factor hypotheses. -/
def TraceFreePreHilbert
(_hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
(_hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
(_hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
(_hunit : (1 : M.toStarSubalgebra) ≠ 0)
    : Type _ := M.toStarSubalgebra

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit

instance traceFreePreHilbertRing : Ring E := inferInstanceAs (Ring M.toStarSubalgebra)
instance traceFreePreHilbertAlgebra : Algebra ℂ E :=
  inferInstanceAs (Algebra ℂ M.toStarSubalgebra)
instance traceFreePreHilbertStarRing : StarRing E :=
  inferInstanceAs (StarRing M.toStarSubalgebra)

/-- Algebraic identification only: it does not identify the two norms. -/
def traceFreeCopy : M.toStarSubalgebra ≃⋆ₐ[ℂ] E :=
  _root_.StarAlgEquiv.refl ℂ M.toStarSubalgebra

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_OriginalUnitary
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- Normalized trace-two topology on actual unitaries of the original factor.
   The wrapper avoids Mathlib's existing operator-norm topology on unitary S. -/
open scoped Topology
namespace Generator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}

abbrev factorVonNeumann (hS : IsII1Factor S) : VonNeumannAlgebra H where
  toStarSubalgebra := S
  centralizer_centralizer' := wotClosed_bicommutant S hS.weaklyClosed

theorem IsII1Factor.factor_smul (hS : IsII1Factor S) :
    ∀ c : (factorVonNeumann hS).toStarSubalgebra,
      (∀ a : (factorVonNeumann hS).toStarSubalgebra, a*c=c*a) →
      ∃ z : ℂ,c=z • (1 : (factorVonNeumann hS).toStarSubalgebra) := by
  intro c hc
  obtain ⟨z,hz⟩ := hS.factor c hc
  exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩

theorem IsII1Factor.one_ne_zero (hS : IsII1Factor S) :
    (1 : (factorVonNeumann hS).toStarSubalgebra) ≠ 0 := by
  intro h
  exact hS.nonzero (congrArg Subtype.val h).symm

open Tracial
variable (S) (hS : IsII1Factor S)
local notation "hf" => hS.factor_smul
local notation "hu" => hS.one_ne_zero

/-- Same unitaries, with trace topology rather than the operator-norm topology. -/
structure FactorTraceUnitary (S : StarSubalgebra ℂ (H →L[ℂ] H)) (_hS : IsII1Factor S) where
  toUnitary : unitary S

namespace FactorTraceUnitary

def algebra (u : FactorTraceUnitary S hS) : S := u.toUnitary

end FactorTraceUnitary
end Generator

end

end OAI
end


