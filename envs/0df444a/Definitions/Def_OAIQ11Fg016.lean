-- Prove2me | Definitions.Def_OAIQ11Fg016
-- name    : OAIQ11Fg016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:27:40.097008+00:00
-- url     : https://prove2.me/theorems/4322399b-e6e5-463c-881c-3450010c3dd6
-- title:
--   Definitions bundle OAIQ11Fg016 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 6 definitions and 12 theorems. The definitions and types are `OAI.Generator.Tracial.boundedPartialResidual`, `OAI.Generator.Tracial.conjugateEnd`, `OAI.Generator.Tracial.conjugateGaps`, `OAI.Generator.Tracial.constantQuotientUnitary`, `OAI.Generator.Tracial.dimensionSpectralValue`, `OAI.Generator.Tracial.sequenceUnitaryQuotient`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_CoordinatePerturbation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean), [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_FreeGroupMoments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/FreeGroupMoments.lean), [`FactorGeneration_ResidualCompletion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean), [`FactorGeneration_SpectralStates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/SpectralStates.lean).
--
--   **Imports.** It imports the bundles `OAIQ11Fg021` and `OAIQ11Fg014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg023` and `OAIQ11Fg024`; the statements `OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateConjugates_quotient`, `OAI.Generator.Tracial.coordinateGroupRing_orthonormal`, `OAI.Generator.Tracial.exists_exact_residual_patch`, `OAI.Generator.Tracial.exists_residual_quotient_increment` and `OAI_Generator_Tracial_relative_generation_at_continuity`; the proofs of `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinateConjugates_quotient`, `OAI.Generator.Tracial.coordinateGroupRing_orthonormal`, `OAI.Generator.Tracial.exists_exact_residual_patch`, `OAI.Generator.Tracial.exists_residual_quotient_increment`, `OAI_Generator_Tracial_exists_scalar_pinching_for_matrixUnits`, `OAI_Generator_Tracial_relative_generation_at_continuity` and `OAI_Generator_Tracial_represented_two_selfAdjoint_generators`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg021
import Definitions.Def_OAIQ11Fg014

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def boundedPartialResidual (v : ℕ → PartialUnitary M) : Bounded M :=
  1-boundedPartialSupport v

end

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeGroupMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/

/-! The actual free-group representation furnished by successive Haar variables. -/

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {A : Type*}

def conjugateGaps (p : A → unitary (Q τ ω)) (a : A × Bool) :
    List (A × Bool) → List (Q τ ω × Bool)
  | [] => []
  | b::w => ((↑(star (p a.1)*p b.1) : Q τ ω),!b.2)::conjugateGaps p b w

def conjugateEnd (p : A → unitary (Q τ ω)) (a : A × Bool) : List (A × Bool) → Q τ ω
  | [] => ↑(star (p a.1))
  | b::w => conjugateEnd p b w

end

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def sequenceUnitaryQuotient : unitary (Sequences M) →* unitary (Q τ ω) where
  toFun u := ⟨sequenceQuotient τ ω (u : Sequences M),Unitary.map_mem (sequenceQuotient τ ω) u.property⟩
  map_one' := Subtype.ext (map_one (sequenceQuotient τ ω))
  map_mul' a b := Subtype.ext (map_mul (sequenceQuotient τ ω) (a : Sequences M) (b : Sequences M))

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def constantQuotientUnitary (u : unitary M.toStarSubalgebra) : unitary (Q τ ω) :=
  sequenceUnitaryQuotient τ ω (constantSequenceUnitary u)

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Archimedean comparison makes the supremum strictly positive on nonzero projections. -/
theorem traceFreeDyadicSup_pos
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (p q : AlgebraProjection M) (hq : q.val≠0) :
    0 < traceFreeDyadicSup hfactor hdiff p q := by
  obtain ⟨n,hn⟩ := traceFree_eventually_dyadic_subequivalent hfactor hdiff hfinite p q hq
  have h := hn n le_rfl
  have he : ((traceFreeDyadicPartition hfactor hdiff p n).subset {dyadicFalseIndex n}).Subequivalent q := by
    rw [EquivalentPartition.subset_singleton]
    exact h
  apply lt_of_lt_of_le ?_ (traceFreeDyadicSup_lower_bound hfactor hdiff p q n _ he)
  simp only [dyadicWeight,Finset.card_singleton,Nat.cast_one]
  exact div_pos zero_lt_one (pow_pos (by norm_num) _)

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
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/
section
open Filter
open scoped BigOperators Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Actual finite spectral approximants are Cauchy in their dimension values,
and their real limit controls every commuting spectral approximation. -/
theorem traceFreeDimension_exists_spectral_value
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ t : ℂ, t.im=0 ∧ IsDimensionSpectralValue hfactor hdiff x t := by
  classical
  have happrox (n : ℕ) :
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℝ),
        (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
        ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < 1/2^n := by
    obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
      ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
    exact ⟨Q,c,fun y hy => hQ y hy (Commute.one_left y),by simpa only [one_mul,mul_one] using herr⟩
  choose Q c hQ herr using happrox
  let f (n : ℕ) : ℂ := ∑ i, (c n i : ℂ)*(traceFreeDimension hfactor hdiff ((Q n).piece i) : ℂ)
  let a (n : ℕ) : M.toStarSubalgebra := ∑ i, (c n i : ℂ) • ((Q n).piece i).val
  have hbound (n : ℕ) (R : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (d : Fin R.size → ℂ) (hR : ∀ j, Commute (R.piece j).val x) :
      ‖f n-∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)‖ ≤
        1/2^n+‖x-∑ j, d j • (R.piece j).val‖ := by
    have hc (i : Fin (Q n).size) (j : Fin R.size) :
        Commute ((Q n).piece i).val (R.piece j).val := hQ n _ (hR j).symm i
    have h := (Q n).dimension_weight_cross_norm_le hfactor hdiff hfinite R hc hunit
      (fun i => (c n i : ℂ)) d
    refine h.trans ?_
    have htri := dist_triangle (a n) x (∑ j, d j • (R.piece j).val)
    simp only [dist_eq_norm] at htri
    rw [norm_sub_rev (a n) x] at htri
    exact htri.trans (add_le_add (herr n).le le_rfl)
  have heps : Tendsto (fun n : ℕ => (1 : ℝ)/2^n) atTop (𝓝 0) := by
    simpa only [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1)
  have hf : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N,?_⟩
    intro m hm n hn
    rw [dist_eq_norm]
    have h := hbound m (Q n) (fun i => (c n i : ℂ)) (hQ n x (Commute.refl x))
    have he := herr n
    have hm' := hN m hm
    have hn' := hN n hn
    change ‖f m-f n‖ ≤ _ at h
    linarith
  obtain ⟨t,ht⟩ := cauchySeq_tendsto_of_complete hf
  have him (n : ℕ) : (f n).im=0 := by simp [f]
  refine ⟨t,?_,?_⟩
  · have hi := Complex.continuous_im.tendsto t |>.comp ht
    exact tendsto_nhds_unique hi (by
      change Tendsto (fun n => (f n).im) atTop (𝓝 0)
      simpa only [him] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  · intro R d hR
    apply le_of_tendsto_of_tendsto' ((ht.sub_const _).norm)
      (by simpa only [zero_add] using heps.add_const ‖x-∑ j, d j • (R.piece j).val‖)
    exact fun n => hbound n R d hR

/-- This is a constructed scalar value on self-adjoint operators; it is not
yet packaged as a linear functional. -/
def dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) : ℂ :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose

theorem dimensionSpectralValue_spec (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).im=0 ∧
      IsDimensionSpectralValue hfactor hdiff x
        (dimensionSpectralValue hfactor hdiff hfinite hunit x hx) :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose_spec

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_projection (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) :
    dimensionSpectralValue hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint=
      (traceFreeDimension hfactor hdiff p : ℂ) :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint).2.on_projection
    hfactor hdiff p

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_eq_of_approximants
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℂ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℂ),
        (∀ i, Commute (Q.piece i).val x) ∧
        ‖x-∑ i, c i • (Q.piece i).val‖ < ε ∧
        ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ < ε) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hxerr,hterr⟩ := h (ε/2) (half_pos hε)
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2 Q c hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
    (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t] at htri
  linarith

theorem dimensionSpectralValue_real_smul
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (r : ℝ) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (r • x) ((IsSelfAdjoint.all r).smul hx)=
      (r : ℂ)*dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  apply dimensionSpectralValue_eq_of_approximants hfactor hdiff hfinite hunit
  intro ε hε
  have hr : 0 < ‖r‖+1 := by positivity
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/(‖r‖+1)) (div_pos hε hr)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have hb : ‖r‖*(ε/(‖r‖+1)) < ε := by
    have hh := (div_pos hε hr)
    have he : (‖r‖+1)*(ε/(‖r‖+1))=ε := mul_div_cancel₀ _ (ne_of_gt hr)
    nlinarith
  refine ⟨Q,fun i => (r : ℂ)*(c i : ℂ),?_,?_,?_⟩
  · intro i
    show (Q.piece i).val*(r • x)=(r • x)*(Q.piece i).val
    rw [mul_smul_comm,smul_mul_assoc,(hc i).eq]
  · have he : (r • x)-∑ i, ((r : ℂ)*(c i : ℂ)) • (Q.piece i).val=
        r • (x-∑ i, (c i : ℂ) • (Q.piece i).val) := by
      simp only [smul_sub,Finset.smul_sum,← smul_assoc,Complex.real_smul]
    rw [he,norm_smul]
    exact (mul_le_mul_of_nonneg_left herr.le (norm_nonneg r)).trans_lt hb
  · rw [show (∑ i, ((r : ℂ)*(c i : ℂ))*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
        (r : ℂ)*(∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) by
          rw [Finset.mul_sum]; simp only [mul_assoc],← mul_sub,norm_mul,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (hval.trans herr.le) (norm_nonneg r)).trans_lt hb

theorem dimensionSpectralValue_neg (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (-x) hx.neg=
      -dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  simpa only [neg_one_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
    dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit (-1) x hx

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_add_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx+
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  classical
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herrQ⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/4) (by positivity)
  obtain ⟨R,d,_,hR,herrR⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ y hy (ε/4) (by positivity)
  simp only [one_mul,mul_one] at herrQ herrR
  have hQx := hQ x (Commute.refl x) (Commute.one_left x)
  have hQy := hQ y hxy (Commute.one_left y)
  have hRx := hR x hxy.symm (Commute.one_left x)
  have hRy := hR y (Commute.refl y) (Commute.one_left y)
  have hc (i : Fin Q.size) (j : Fin R.size) :
      Commute (Q.piece i).val (R.piece j).val :=
    (hR _ (hQy i).symm (Commute.one_left _) j).symm
  let q := Q.jointPiece R hc
  let b (a : Fin Q.size × Fin R.size) : ℂ := (c a.1 : ℂ)+(d a.2 : ℂ)
  let sx : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
  let sy : M.toStarSubalgebra := ∑ j, (d j : ℂ) • (R.piece j).val
  let wx : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  let wy : ℂ := ∑ j, (d j : ℂ)*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)
  have hsum : (∑ a, b a • (q a).val)=sx+sy := by
    simp only [b,add_smul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (Q.joint_sum_left R hc (fun i => (c i : ℂ)))
      (Q.joint_sum_right R hc (fun j => (d j : ℂ)))
  have hweight : (∑ a, b a*(traceFreeDimension hfactor hdiff (q a) : ℂ))=wx+wy := by
    simp only [b,add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·)
      (Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit (fun i => (c i : ℂ)))
      (Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit (fun j => (d j : ℂ)))
  have hcomm (a : Fin Q.size × Fin R.size) : Commute (q a).val (x+y) :=
    ((hQx a.1).mul_left (hRx a.2)).add_right ((hQy a.1).mul_left (hRy a.2))
  have hz := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (x+y) (hx.add hy)).2.family_bound
    hfactor hdiff q (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc) b hcomm
  rw [hsum,hweight] at hz
  have he : ‖(x+y)-(sx+sy)‖ ≤ ‖x-sx‖+‖y-sy‖ := by
    rw [show (x+y)-(sx+sy)=(x-sx)+(y-sy) by abel]
    exact norm_add_le _ _
  have hxv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hQx
  have hyv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit y hy).2
    R (fun j => (d j : ℂ)) hRy
  let vx := dimensionSpectralValue hfactor hdiff hfinite hunit x hx
  let vy := dimensionSpectralValue hfactor hdiff hfinite hunit y hy
  have hv : ‖(vx+vy)-(wx+wy)‖ ≤ ‖vx-wx‖+‖vy-wy‖ := by
    rw [show (vx+vy)-(wx+wy)=(vx-wx)+(vy-wy) by abel]
    exact norm_add_le _ _
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)) (wx+wy) (vx+vy)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (wx+wy) (vx+vy)] at htri
  change ‖vx-wx‖ ≤ ‖x-sx‖ at hxv
  change ‖vy-wy‖ ≤ ‖y-sy‖ at hyv
  change ‖x-sx‖ < ε/4 at herrQ
  change ‖y-sy‖ < ε/4 at herrR
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)-(vx+vy)‖ ≤ 0+ε
  linarith

theorem dimensionSpectralValue_sub_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x-y) (hx.sub hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx-
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  simpa only [sub_eq_add_neg,dimensionSpectralValue_neg hfactor hdiff hfinite hunit y hy] using
    dimensionSpectralValue_add_of_commute hfactor hdiff hfinite hunit x (-y) hx hy.neg hxy.neg_right

end

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralValueCStar
attribute [local instance] OAI.Generator.Tracial.spectralValueOrder
attribute [local instance] OAI.Generator.Tracial.spectralValuePreorder
attribute [local instance] OAI.Generator.Tracial.spectralValueLE
attribute [local instance] OAI.Generator.Tracial.spectralValueStarOrder
theorem dimensionSpectralValue_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_spectral_approximation x hx ε hε
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2
    Q (fun i => (c i : ℂ)) (hQ x (Commute.refl x))
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
  have hw : 0 ≤ w := Finset.sum_nonneg (fun i _ => mul_nonneg (hc i)
    (traceFreeDimension_nonneg hfactor hdiff _))
  have he : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
  have hb : ‖t-(w : ℂ)‖ < ε := by rw [he]; exact hval.trans_lt herr
  have hre := Complex.re_le_norm ((w : ℂ)-t)
  rw [Complex.sub_re,Complex.ofReal_re,norm_sub_rev (w : ℂ) t] at hre
  change 0 ≤ t.re+ε
  linarith

theorem dimensionSpectralValue_mono_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) (hle : x ≤ y) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).re ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit y hy).re := by
  have h := dimensionSpectralValue_nonneg hfactor hdiff hfinite hunit (y-x) (sub_nonneg.mpr hle)
  rw [dimensionSpectralValue_sub_of_commute hfactor hdiff hfinite hunit y x hy hx hxy.symm,
    Complex.sub_re] at h
  exact sub_nonneg.mp h

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralFaithfulCStar
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulOrder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulPreorder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulLE
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulStarOrder
theorem dimensionSpectralValue_spectral_cut_lower
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    t*traceFreeDimension hfactor hdiff (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t) ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x t
  have hq : Commute q.val x := by
    show q.val*x=x*q.val
    simpa only [one_mul,mul_one] using cornerSpectralCut_commutes
      ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  have htq : Commute (t • q.val) x := by
    show (t • q.val)*x=x*(t • q.val)
    rw [smul_mul_assoc,mul_smul_comm,hq.eq]
  have hle : t • q.val ≤ x := by
    simpa only [Complex.coe_smul] using positive_spectral_cut_domination x hx t
  have h := dimensionSpectralValue_mono_of_commute hfactor hdiff hfinite hunit
    (t • q.val) x ((IsSelfAdjoint.all t).smul q.property.isSelfAdjoint) hx.isSelfAdjoint htq hle
  rw [dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit t q.val q.property.isSelfAdjoint,
    dimensionSpectralValue_projection hfactor hdiff hfinite hunit q,
    ← Complex.ofReal_mul,Complex.ofReal_re] at h
  exact h

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end


