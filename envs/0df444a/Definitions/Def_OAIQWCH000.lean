-- Prove2me | Definitions.Def_OAIQWCH000
-- name    : OAIQWCH000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T00:37:06.497454+00:00
-- url     : https://prove2.me/theorems/97808021-0cc2-4a56-b6f5-7c319a8dd40a
-- title:
--   OpenAI complete Crouzeix split (Hilbert space form): definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of the complete Crouzeix theorem for bounded operators on Hilbert space (`OAI.CrouzeixHilbert.hilbert`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/Crouzeix` (OpenAI, *The complete Crouzeix theorem: optimal similarity and a common positive boundary representation*, OpenAI Math Release, September 23, 2026, result family 325, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the finite compressions and amplifications (`compression`, `iterateSpan`, `amplificationMap`, `conjugateOperator`, `FiniteMatrixPolynomialBound`), the contour and holomorphic calculus data (`SmoothContour.trace`, `SmoothContour.integral`, `matrixContourEval`, `radialContour`), the conformal collars of a convex domain (`DiskEmbedding`, `BoundaryChart`, `InteriorCollar`, `ExteriorCollar` and its boundary kernel `ExteriorCollar.boundaryKernel`), the Poisson, Schwarz and Dirichlet extensions and the harmonic reflection (`poissonExtension`, `schwarzExtension`, `dirichletExtension`, `oddReflection`), the boundary spaces and operators on the circle (`CircleSpace`, `circleMeasure`, `BoundaryL2`, `matrixFourier`, `fourierProjC`, `boundaryCauchy`, `boundaryCauchyAdjoint`, `kernelOperator`), the boundary densities and partial traces (`crossPartialTrace`, `weightedPartialTrace`, `densityLp`, `vectorization`, `matrixOperatorMap`), the Stein metric and its extremal data (`steinSeries`, `Feasible`, `Endpoint.unit`, `Endpoint.slacks`, the colligations of `Realization`), and the physical Laurent channels and representatives. It also contains the lemmas those definitions use in their bodies, for example the bounds that build the kernel operators on $L^2$ and the facts in the proof fields of the collar structures.
--
--   The definitions of the published statement (`Operator`, `Coeff`, `numericalRange`, `numericalClosure`, `supNorm`, `Amplification`, `tensorOperator`, `matrixPolynomial`, `polynomialEval`, `SmoothContour`, `SmoothContour.index`, `CalculusContour`, `contourEval`, `holomorphicEval`, `matrixHolomorphicEval`, `EntrywiseHolomorphic`, `RationalMatrix`, `PolesOutside`, `matrixRationalFunction`, `rationalEval`, `matrixRationalEval`, `NonzeroConclusion`, `ZeroConclusion`, `SharpConstant`) are not repeated: the bundle imports them from the published bundle `Def_CrouzeixHilbert`.
--
--   **A theorem the definitions need.** The proof fields of `ExteriorCollar.boundaryKernel` use that the derivative of an injective holomorphic function never vanishes (`deriv_ne_zero_of_injOn`), which OpenAI proves from Hurwitz's theorem. Hurwitz's theorem is not proved again in this bundle. The bundle imports the published, Proved statement `hurwitz_nonvanishing_limit` (62b01429), and `deriv_ne_zero_of_injOn` uses it in place of OpenAI's `zero_or_ne_of_tendstoLocallyUniformlyOn`. The difference quotients there converge uniformly on a ball, and a case split on whether the derivative vanishes somewhere on it gives OpenAI's dichotomy.
--
--   **Compatibility lemmas.** OpenAI's code was written for a newer Lean core. Three lemmas it uses under names this environment lacks (`ite_eq_left`, `ite_eq_right`, `dite_eq_left`, each the corresponding `if_pos`, `if_neg` or `dif_pos`) are declared at the top of the bundle inside namespace `OAI`, so they are visible to OpenAI's code and add no root-level names to the environment.
--
--   Modules: `Amplification.lean`, `AngularMeasure.lean`, `AngularTransport.lean`, `BlockPolynomial.lean`, `BoundaryChart.lean`, `BoundaryFibers.lean`, `BoundaryForms.lean`, `BoundaryKernel.lean`, `BoundaryMoments.lean`, `BoundaryOperators.lean`, `CauchyProjection.lean`, `CircleAnalytic.lean`, `CircleCoordinate.lean`, `Compression.lean`, `ContourExistence.lean`, `ContourHomotopy.lean`, `Density.lean`, `DensityCompatibility.lean`, `DiskAutomorphism.lean`, `DiskBoundaryChart.lean`, `DiskCalculus.lean`, `DiskHolomorphic.lean`, `Endpoint.lean`, `ExteriorCollar.lean`, `ExteriorContour.lean`, `ExteriorKernel.lean`, `ExteriorNormal.lean`, `ExteriorRiemann.lean`, `Faber.lean`, `FiniteCompression.lean`, `Fourier.lean`, `HarmonicReflection.lean`, `HomologicalCauchy.lean`, `InteriorCollar.lean`, `MatrixContours.lean`, `MatrixEndpoint.lean`, `NumericalRange.lean`, `PhysicalCalculus.lean`, `PhysicalDensity.lean`, `PhysicalFourier.lean`, `PhysicalModule.lean`, `PhysicalProjection.lean`, `PoissonExtension.lean`, `PolynomialApproximation.lean`, `RationalEvaluation.lean`, `RationalTransfer.lean`, `Realization.lean`, `Resolvent.lean`, `ResolventBounds.lean`, `ResolventMoments.lean`, `Riemann.lean`, `SeparateHolomorphic.lean`, `Sharpness.lean`, `SimilarityRepresentation.lean`, `SteinMetric.lean`, `TensorDensity.lean`, `Univalent.lean`, `Vectorization.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the sixteen solutions of this split. Five prove the published classical statements, each stated with Mathlib's definitions or the published bundle `Def_CrouzeixHilbert` only: the Riemann mapping theorem for bounded simply connected open sets (`OAI.CrouzeixHilbert.Conformal.riemann_biholomorphic_bounded`), Hurwitz's theorem and its corollary for injective functions, both for limits along any filter (`OAI.CrouzeixHilbert.Conformal.zero_or_ne_of_tendstoLocallyUniformlyOn`, `OAI.CrouzeixHilbert.Conformal.injOn_of_tendstoLocallyUniformlyOn`), the homology form of Cauchy's theorem (`OAI.CrouzeixHilbert.sum_integral_eq_zero_of_null_homology`) and uniform polynomial approximation on compact convex sets (`OAI.CrouzeixHilbert.exists_polynomial_uniform_approx`). Montel's theorem is not published again: the solutions that need it derive OpenAI's form in a few lines from the published, Proved `MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform` (9827712e). Ten solutions prove intermediate statements of OpenAI's argument, and the last proves `OAI.CrouzeixHilbert.hilbert` from them.
-- source:
--   OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Crouzeix at commit adc7f12

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Theorems.Thm_hurwitz_nonvanishing_limit

section
-- module Solutions.OAIQW_CrouzeixHilbert.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.NumericalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact numerical closure, supremum norms, and spectral containment. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp]
theorem numericalRange_eq_empty [Subsingleton H] (A : Operator H) :
    numericalRange A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨x, hx, _⟩
  have : x = 0 := Subsingleton.elim _ _
  simp [this] at hx

@[simp]
theorem supNorm_empty {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) :
    supNorm ∅ F = 0 := by simp [supNorm]

instance amplificationSubsingleton [Subsingleton H] (m : ℕ) :
    Subsingleton (Amplification H m) := by
  have hz (x : Amplification H m) : x = 0 := by
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq continuous_id continuous_const) ?_
    intro a
    rw [Subsingleton.elim a 0, UniformSpace.Completion.coe_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem operator_lower_bound_of_inner (T : Operator H) {δ : ℝ}
    (hδ : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖⟪x, T x⟫_ℂ‖) (x : H) :
    δ * ‖x‖ ≤ ‖T x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let v : H := (‖x‖ : ℂ)⁻¹ • x
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hn]
  have hb : δ ≤ ‖T v‖ := by
    calc
      δ ≤ ‖⟪v, T v⟫_ℂ‖ := hδ v hv
      _ ≤ ‖v‖ * ‖T v‖ := norm_inner_le_norm _ _
      _ = ‖T v‖ := by rw [hv, one_mul]
  calc
    δ * ‖x‖ ≤ ‖T v‖ * ‖x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = ‖T x‖ := by
      simp only [v, map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm]
      rw [mul_right_comm, inv_mul_cancel₀ hn, one_mul]

theorem isUnit_of_inner_lower_bound [CompleteSpace H] (T : Operator H)
    {δ : ℝ} (hδpos : 0 < δ) (hb : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖⟪x, T x⟫_ℂ‖) :
    IsUnit T := by
  have lower := operator_lower_bound_of_inner T hb
  have lowerAdj : ∀ y, δ * ‖y‖ ≤ ‖(ContinuousLinearMap.adjoint T) y‖ := by
    apply operator_lower_bound_of_inner
    intro y hy
    rw [T.adjoint_inner_right, norm_inner_symm]
    exact hb y hy
  let C : NNReal := ⟨δ⁻¹, inv_nonneg.mpr hδpos.le⟩
  have anti : AntilipschitzWith C T := by
    apply T.antilipschitz_of_bound
    intro x
    have hh := mul_le_mul_of_nonneg_left (lower x) (inv_nonneg.mpr hδpos.le)
    change ‖x‖ ≤ δ⁻¹ * ‖T x‖
    simpa only [← mul_assoc, inv_mul_cancel₀ hδpos.ne', one_mul] using hh
  have hclosed : IsClosed (T.range : Set H) :=
    anti.isClosed_range T.uniformContinuous
  have hak : (ContinuousLinearMap.adjoint T).ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    change (ContinuousLinearMap.adjoint T) x = (ContinuousLinearMap.adjoint T) y at hxy
    have hnorm := lowerAdj (x - y)
    have hz : (ContinuousLinearMap.adjoint T) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [hz, norm_zero] at hnorm
    have : ‖x - y‖ ≤ 0 := by nlinarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hr : T.range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, T.orthogonal_range, hak]
  rw [hclosed.submodule_topologicalClosure_eq] at hr
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨anti.injective, LinearMap.range_eq_top.mp hr⟩

theorem spectrum_subset_numericalClosure [CompleteSpace H] (A : Operator H) :
    spectrum ℂ A ⊆ numericalClosure A := by
  intro lam hspec
  by_contra hlam
  have hopen : IsOpen (numericalClosure A)ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen lam hlam
  have hsep : ∀ z ∈ numericalRange A, δ ≤ ‖lam - z‖ := by
    intro z hz
    by_contra hlt
    have hb : z ∈ Metric.ball lam δ := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using lt_of_not_ge hlt
    exact hball hb (subset_closure hz)
  have hu : IsUnit (algebraMap ℂ (Operator H) lam - A) := by
    apply isUnit_of_inner_lower_bound _ hδ
    intro x hx
    have he : ⟪x, (algebraMap ℂ (Operator H) lam - A) x⟫_ℂ = lam - ⟪x, A x⟫_ℂ := by
      simp [ContinuousLinearMap.algebraMap_apply, inner_self_eq_norm_sq_to_K, hx]
    rw [he]
    exact hsep _ ⟨x, hx, rfl⟩
  exact (spectrum.mem_iff.mp hspec) hu

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.FiniteCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact polynomial compression on spans of finitely many operator iterates. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def compression (A : Operator H) (E : Submodule ℂ H) [E.HasOrthogonalProjection] :
    Operator E := E.orthogonalProjectionOnto.comp (A.comp E.subtypeL)

def iterateSpan (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range (fun p : Fin (d + 1) × Fin l => (A ^ (p.1 : ℕ)) (ξ p.2)))

instance iterateSpanFiniteDimensional (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H) :
    FiniteDimensional ℂ (iterateSpan A d ξ) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

def amplificationInclusion (E : Submodule ℂ H) (m : ℕ) :
    Amplification E m →L[ℂ] Amplification H m :=
  (TensorProduct.mapL E.subtypeL (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)))).completion

@[simp]
theorem amplificationInclusion_tmul (E : Submodule ℂ H) {m : ℕ}
    (x : E) (y : EuclideanSpace ℂ (Fin m)) :
    amplificationInclusion E m (↑(x ⊗ₜ[ℂ] y)) =
      (↑((x : H) ⊗ₜ[ℂ] y) : Amplification H m) := by
  simp [amplificationInclusion, ContinuousLinearMap.completion_apply_coe]

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

def amplificationMap (e : H →ₗᵢ[ℂ] G) (m : ℕ) :
    Amplification H m →L[ℂ] Amplification G m :=
  (TensorProduct.mapL e.toContinuousLinearMap
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)))).completion

@[simp]
theorem amplificationMap_tmul (e : H →ₗᵢ[ℂ] G) {m : ℕ}
    (x : H) (y : EuclideanSpace ℂ (Fin m)) :
    amplificationMap e m (↑(x ⊗ₜ[ℂ] y)) =
      (↑(e x ⊗ₜ[ℂ] y) : Amplification G m) := by
  simp [amplificationMap]

def conjugateOperator (e : H ≃ₗᵢ[ℂ] G) : Operator H ≃A[ℂ] Operator G :=
  e.toContinuousLinearEquiv.conjContinuousAlgEquiv

@[simp]
theorem conjugateOperator_apply (e : H ≃ₗᵢ[ℂ] G) (A : Operator H) (x : G) :
    conjugateOperator e A x = e (A (e.symm x)) := rfl

@[simp]
theorem conjugateOperator_pow_apply (e : H ≃ₗᵢ[ℂ] G) (A : Operator H) (k : ℕ) (x : H) :
    (conjugateOperator e A ^ k) (e x) = e ((A ^ k) x) := by
  rw [← map_pow (conjugateOperator e) A k, conjugateOperator_apply, e.symm_apply_apply]

open scoped Kronecker

def matrixAmplificationCoordinates (n m : ℕ) :
    Amplification (EuclideanSpace ℂ (Fin n)) m →L[ℂ]
      EuclideanSpace ℂ (Fin n × Fin m) :=
  (((EuclideanSpace.basisFun (Fin n) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin m) ℂ)).repr.toContinuousLinearEquiv.toContinuousLinearMap).fromCompletion

@[simp]
theorem matrixAmplificationCoordinates_tmul {n m : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) (y : EuclideanSpace ℂ (Fin m)) (i : Fin n) (j : Fin m) :
    matrixAmplificationCoordinates n m (↑(x ⊗ₜ[ℂ] y)) (i, j) = y j * x i := by
  simp only [matrixAmplificationCoordinates, ContinuousLinearMap.fromCompletion_apply_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr]

def FiniteMatrixPolynomialBound : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (M : Coeff n) (m : ℕ), 0 < m →
    ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
    ‖polynomialEval (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B‖ ≤
      2 * supNorm (numericalRange (Matrix.toEuclideanCLM (𝕜 := ℂ) M)) (matrixPolynomial B)

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Existence. -/

noncomputable section

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

open Set Filter Metric

namespace CrouzeixHilbert

def unitCirclePath (t : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * t)

theorem unitCirclePath_norm (t : ℝ) : ‖unitCirclePath t‖ = 1 := by
  simp only [unitCirclePath, norm_circleMap_zero, abs_one]

theorem unitCirclePath_smooth : ContDiff ℝ 1 unitCirclePath :=
  (contDiff_circleMap 0 1).comp (contDiff_const.mul contDiff_id)

theorem unitCirclePath_closed : unitCirclePath 0 = unitCirclePath 1 := by
  simpa only [unitCirclePath, mul_zero, mul_one, zero_add] using
    ((periodic_circleMap 0 1) 0).symm

def radialContour (a : ℂ) (q : ℂ → ℝ) (hq : ContDiff ℝ 1 q) : SmoothContour where
  path := fun t => a + q (unitCirclePath t) • unitCirclePath t
  smooth := contDiff_const.add ((hq.comp unitCirclePath_smooth).smul unitCirclePath_smooth)
  closed := by rw [unitCirclePath_closed]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic continuity, pole-free rational evaluation, and tensor norm bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem EntrywiseHolomorphic.continuousOn {m : ℕ} {U : Set ℂ} {F : ℂ → Coeff m}
    (hF : EntrywiseHolomorphic U F) : ContinuousOn F U := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (hF i j).continuousOn

theorem norm_tensorOperator_le (A : Operator H) {m : ℕ} (B : Coeff m) :
    ‖tensorOperator A B‖ ≤ ‖A‖ * ‖B‖ := by
  apply (tensorOperator A B).opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (tensorOperator A B).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro a
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe]
  exact ((TensorProduct.mapL A (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) B)).le_opNorm a).trans
    (mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le A (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) B))
      (norm_nonneg _))

@[simp]
theorem tensorOperator_zero_right (A : Operator H) (m : ℕ) :
    tensorOperator A (0 : Coeff m) = 0 := by
  apply norm_le_zero_iff.mp
  simpa using norm_tensorOperator_le A (0 : Coeff m)

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_resolvent [CompleteSpace H] (A : Operator H) :
    ContinuousOn (fun z : ℂ => Ring.inverse (algebraMap ℂ (Operator H) z - A))
      (numericalClosure A)ᶜ := by
  intro z hz
  have hr : z ∈ resolventSet ℂ A := by
    by_contra h
    exact hz (spectrum_subset_numericalClosure A h)
  exact (spectrum.hasDerivAt_resolvent_const_left hr).continuousAt.continuousWithinAt

def SmoothContour.trace (Γ : SmoothContour) : Set ℂ := Γ.path '' Icc (0 : ℝ) 1

def contourKernel (A : Operator H) (Γ : SmoothContour) (t : ℝ) : Operator H :=
  deriv Γ.path t • Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)

def tensorOperatorCLM {m : ℕ} (B : Coeff m) :
    Operator H →L[ℂ] Operator (Amplification H m) := by
  let L : Operator H →ₗ[ℂ] Operator (Amplification H m) :=
    { toFun := fun A => tensorOperator A B
      map_add' := by
        intro A D
        apply ContinuousLinearMap.ext
        intro x
        refine UniformSpace.Completion.induction_on x
          (isClosed_eq (tensorOperator (A + D) B).continuous
            ((tensorOperator A B).continuous.add (tensorOperator D B).continuous)) ?_
        intro a
        simp only [tensorOperator, TensorProduct.mapL_add_left,
          ContinuousLinearMap.completion_apply_coe, add_apply,
          UniformSpace.Completion.coe_add]
      map_smul' := by
        intro c A
        apply ContinuousLinearMap.ext
        intro x
        refine UniformSpace.Completion.induction_on x
          (isClosed_eq (tensorOperator (c • A) B).continuous
            ((tensorOperator A B).continuous.const_smul c)) ?_
        intro a
        simp only [tensorOperator, TensorProduct.mapL_smul_left,
          ContinuousLinearMap.completion_apply_coe, smul_apply,
          UniformSpace.Completion.coe_smul, RingHom.id_apply] }
  exact L.mkContinuous ‖B‖ (fun A => (norm_tensorOperator_le A B).trans_eq (mul_comm _ _))

@[simp]
theorem tensorOperatorCLM_apply {m : ℕ} (A : Operator H) (B : Coeff m) :
    tensorOperatorCLM B A = tensorOperator A B := rfl

def matrixEntryCLM {m : ℕ} (i j : Fin m) : Coeff m →L[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

def matrixContourEval (A : Operator H) {m : ℕ} (Γ : SmoothContour)
    (F : ℂ → Coeff m) : Operator (Amplification H m) :=
  ∑ i, ∑ j, tensorOperator (contourEval A Γ (fun z => F z i j)) (Matrix.single i j 1)

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HomologicalCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homological Cauchy. -/

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology

namespace CrouzeixHilbert

def extendCompactFunction {K : Set ℂ} {E : Type*} [TopologicalSpace E] [Zero E]
    (f : C(K, E)) (z : ℂ) : E := by
  classical
  exact if hz : z ∈ K then f ⟨z, hz⟩ else 0

@[simp]
theorem extendCompactFunction_apply {K : Set ℂ} {E : Type*}
    [TopologicalSpace E] [Zero E] (f : C(K, E)) {z : ℂ} (hz : z ∈ K) :
    (extendCompactFunction f) z = f ⟨z, hz⟩ := by
  classical
  simp only [extendCompactFunction, dite_eq_left hz]

def holomorphicContinuousFunctions (K : Set ℂ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : Submodule ℂ C(K, E) where
  carrier := {f | DifferentiableOn ℂ (extendCompactFunction f) (interior K)}
  zero_mem' := by
    apply (differentiableOn_const (c := (0 : E))).congr
    intro z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz), ContinuousMap.zero_apply]
  add_mem' := by
    intro f g hf hg
    apply (hf.add hg).congr
    intro z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz), ContinuousMap.add_apply, Pi.add_apply]
  smul_mem' := by
    intro c f hf
    apply (hf.const_smul c).congr
    intro z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz), ContinuousMap.smul_apply, Pi.smul_apply]

theorem isClosed_holomorphicContinuousFunctions {K : Set ℂ} [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] :
    IsClosed (holomorphicContinuousFunctions K E : Set C(K, E)) := by
  apply IsSeqClosed.isClosed
  intro fs f hfs hf
  have ht : TendstoUniformlyOn (fun n => (extendCompactFunction (fs n))) (extendCompactFunction f) atTop (interior K) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hf ε hε] with n hn z hz
    simp only [extendCompactFunction_apply _ (interior_subset hz)]
    exact (ContinuousMap.dist_apply_le_dist (f := f) (g := fs n) (⟨z, interior_subset hz⟩ : K)).trans_lt (by simpa [dist_comm] using hn)
  exact ht.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall hfs) isOpen_interior

theorem differentiableOn_parameter_intervalIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => f z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, f z t) U := by
  classical
  intro z hz
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  let K := closedBall z r
  have hKc : IsCompact K := isCompact_closedBall z r
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let g : ℝ → C(K, E) := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then
    ⟨fun w => f w t, ((hd t ht).continuousOn.mono hrU).domRestrict⟩ else 0
  have hga (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (w : K) : g t w = f w t := by
    simp only [g, dite_eq_left ht]
    rfl
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hc : Continuous (fun p : ↥(Icc (0 : ℝ) 1) × K =>
        f p.2 p.1) := hf.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
      (fun p => ⟨hrU p.2.property, p.1.property⟩)
    convert! hc using 1
    funext p
    exact hga p.1 p.1.property p.2
  have hgi : IntervalIntegrable g volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hg
  let S := holomorphicContinuousFunctions K E
  have hgm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t ∈ S := by
    change DifferentiableOn ℂ (extendCompactFunction (g t)) (interior K)
    apply ((hd t ht).mono (interior_subset.trans hrU)).congr
    intro w hw
    rw [extendCompactFunction_apply _ (interior_subset hw), hga t ht]
  have hmi : (∫ t in (0 : ℝ)..1, g t) ∈ S := by
    have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact (S.restrictScalars ℝ).convex.integral_mem isClosed_holomorphicContinuousFunctions
      ((ae_restrict_mem measurableSet_Ioc).mono
        (fun t ht => hgm t (Ioc_subset_Icc_self ht))) hgi.1
  have hdint : DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, f w t) (interior K) := by
    apply hmi.congr
    intro w hw
    rw [extendCompactFunction_apply _ (interior_subset hw)]
    change _ = ContinuousMap.evalCLM ℂ ⟨w, interior_subset hw⟩ (∫ t in (0 : ℝ)..1, g t)
    rw [← (ContinuousMap.evalCLM ℂ ⟨w, interior_subset hw⟩).intervalIntegral_comp_comm hgi]
    apply intervalIntegral.integral_congr
    intro t ht
    change f w t = g t ⟨w, interior_subset hw⟩
    exact (hga t (by simpa only [uIcc_of_le zero_le_one] using ht) ⟨w, interior_subset hw⟩).symm
  apply (hdint.differentiableAt ?_).differentiableWithinAt
  change interior (closedBall z r) ∈ 𝓝 z
  rw [interior_closedBall _ hr.ne']
  exact ball_mem_nhds z hr

theorem dslope_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (a b : ℂ) : dslope f a b = dslope f b a := by
  by_cases he : a = b
  · rw [he]
  · rw [dslope_of_ne _ (Ne.symm he), dslope_of_ne _ he, slope_comm]

theorem continuousAt_dslope_pair_of_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {x : ℂ}
    (hf : AnalyticAt ℂ f x) :
    ContinuousAt (fun p : ℂ × ℂ => dslope f p.1 p.2) (x, x) := by
  change Tendsto _ _ (𝓝 (dslope f x x))
  rw [dslope_same]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs := hf.hasStrictDerivAt.hasStrictFDerivAt.isLittleO
  have hb := (continuous_swap.tendsto (x, x)).eventually (hs.def (half_pos hε))
  have hd : Tendsto (fun p : ℂ × ℂ => deriv f p.1) (𝓝 (x, x)) (𝓝 (deriv f x)) :=
    hf.deriv.continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
  filter_upwards [hb, Metric.tendsto_nhds.mp hd ε hε] with p hp hpd
  by_cases he : p.2 = p.1
  · simpa only [he, dslope_same] using hpd
  · have hn : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr he
    have hp' : ‖f p.2 - f p.1 - (p.2 - p.1) • deriv f x‖ ≤
        (ε / 2) * ‖p.2 - p.1‖ := hp
    have heq : dslope f p.1 p.2 - deriv f x =
        (p.2 - p.1)⁻¹ • (f p.2 - f p.1 - (p.2 - p.1) • deriv f x) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul, dslope_of_ne _ he]
      rfl
    rw [dist_eq_norm, heq, norm_smul, norm_inv]
    calc
      _ ≤ ‖p.2 - p.1‖⁻¹ * ((ε / 2) * ‖p.2 - p.1‖) :=
        mul_le_mul_of_nonneg_left hp' (by positivity)
      _ = ε / 2 := by field_simp [norm_ne_zero_iff.mpr hn]
      _ < ε := half_lt_self hε

theorem continuousOn_dslope_pair {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U) := by
  intro p hp
  by_cases he : p.2 = p.1
  · rcases p with ⟨a, b⟩
    dsimp only at he hp ⊢
    subst b
    exact (continuousAt_dslope_pair_of_analyticAt (hf.analyticOnNhd hU a hp.1)).continuousWithinAt
  · have hc : ContinuousAt (fun p : ℂ × ℂ =>
        (p.2 - p.1)⁻¹ • (f p.2 - f p.1)) p :=
      ((continuous_snd.sub continuous_fst).continuousAt.inv₀ (sub_ne_zero.mpr he)).smul
        (((hf.continuousOn.continuousAt (hU.mem_nhds hp.2)).comp continuous_snd.continuousAt).sub
          ((hf.continuousOn.continuousAt (hU.mem_nhds hp.1)).comp continuous_fst.continuousAt))
    apply (hc.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [(isOpen_ne_fun continuous_snd continuous_fst).mem_nhds he] with q hq
    exact dslope_of_ne f hq

def SmoothContour.integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : SmoothContour) (f : ℂ → E) : E :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    ∫ t in (0 : ℝ)..1, deriv Γ.path t • f (Γ.path t)

def SmoothContour.cauchyTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : SmoothContour) (f : ℂ → E) (w : ℂ) : E :=
  Γ.integral (fun z => (z - w)⁻¹ • f z)

def SmoothContour.regularizedTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Γ : SmoothContour) (f : ℂ → E) (w : ℂ) : E :=
  Γ.integral (dslope f w)

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Automorphism. -/

noncomputable section

open Set Filter Metric Topology Function

open scoped ComplexConjugate

namespace CrouzeixHilbert.Conformal

def diskShift (w z : ℂ) : ℂ := (z - w) / (1 - conj w * z)

@[simp] theorem diskShift_self (w : ℂ) : diskShift w w = 0 := by simp [diskShift]

@[simp] theorem diskShift_zero (w : ℂ) : diskShift w 0 = -w := by simp [diskShift]

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Riemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Riemann. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

structure DiskEmbedding (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f U
  injective : InjOn f U
  into_disk : ∀ z ∈ U, ‖f z‖ < 1
  normalized : f a = 0

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Univalent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Univalent. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hU a ha
  let r := R / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : 2 * r < R := by dsimp [r]; linarith
  have hK : closedBall a (2 * r) ⊆ U := (closedBall_subset_ball hrR).trans hsub
  have hball : ball a r ⊆ U := (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hK
  let δ : ℕ → ℝ := fun n => r / (n + 1)
  have hδ : ∀ n, 0 < δ n := fun n => div_pos hr (by positivity)
  have hδle : ∀ n, δ n ≤ r := fun n => div_le_self hr.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun n : ℕ => r * (1 / ((n : ℝ) + 1))) atTop (𝓝 (r * 0)))
  have hshift : ∀ n z, z ∈ ball a r → z + (δ n : ℂ) ∈ closedBall a (2 * r) := by
    intro n z hz
    have hd : dist (z + (δ n : ℂ)) a ≤ dist z a + δ n := by
      calc
        _ = ‖z - a + (δ n : ℂ)‖ := by rw [dist_eq_norm]; congr 1; ring
        _ ≤ ‖z - a‖ + ‖(δ n : ℂ)‖ := norm_add_le _ _
        _ = dist z a + δ n := by rw [← dist_eq_norm, Complex.norm_real, Real.norm_of_nonneg (hδ n).le]
    exact hd.trans (by have := hδle n; have := mem_ball.mp hz; linarith)
  have hzK : ∀ z ∈ ball a r, z ∈ closedBall a (2 * r) := fun z hz =>
    (mem_closedBall.mpr <| (mem_ball.mp hz).le.trans (by linarith))
  let F : ℕ → ℂ → ℂ := fun n z => (f (z + (δ n : ℂ)) - f z) / (δ n : ℂ)
  have hFd : ∀ n, DifferentiableOn ℂ (F n) (ball a r) := by
    intro n z hz
    have hd₁ : DifferentiableAt ℂ (fun v => f (v + (δ n : ℂ))) z :=
      ((hf _ (hK (hshift n z hz))).differentiableAt
        (hU.mem_nhds (hK (hshift n z hz)))).comp z (differentiableAt_id.add_const _)
    have hd₂ := (hf z (hball hz)).differentiableAt (hU.mem_nhds (hball hz))
    exact ((hd₁.sub hd₂).div_const _).differentiableWithinAt
  have hFn : ∀ n z, z ∈ ball a r → F n z ≠ 0 := by
    intro n z hz he
    have hen : f (z + (δ n : ℂ)) = f z := sub_eq_zero.mp
      ((div_eq_zero_iff).mp he |>.resolve_right (by exact_mod_cast (hδ n).ne'))
    have hinj := hi (hK (hshift n z hz)) (hball hz) hen
    have hzero : (δ n : ℂ) = 0 := add_left_cancel (hinj.trans (add_zero z).symm)
    exact (hδ n).ne' (Complex.ofReal_eq_zero.mp hzero)
  have hFeq : ∀ n z, F n z = dslope f z (z + (δ n : ℂ)) := by
    intro n z
    have hn : z + (δ n : ℂ) ≠ z := by
      simpa using (show (δ n : ℂ) ≠ 0 by exact_mod_cast (hδ n).ne')
    rw [dslope_of_ne f hn]
    simp only [slope, add_sub_cancel_left, smul_eq_mul, div_eq_mul_inv, vsub_eq_sub, F]
    ring
  have huc := ((isCompact_closedBall a (2 * r)).prod (isCompact_closedBall a (2 * r)))
      |>.uniformContinuousOn_of_continuous
      ((continuousOn_dslope_pair hU hf).mono (prod_mono hK hK))
  have hlim : TendstoUniformlyOn F (deriv f) atTop (ball a r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    filter_upwards [hδ0.eventually (gt_mem_nhds hη)] with n hn
    intro z hz
    have hp : dist (z, z) (z, z + (δ n : ℂ)) < η := by
      rw [dist_prod_same_left, dist_self_add_right, Complex.norm_real, Real.norm_of_nonneg (hδ n).le]
      exact hn
    simpa only [dslope_same, ← hFeq] using
      hmod (z,z) ⟨hzK z hz, hzK z hz⟩ (z, z + (δ n : ℂ)) ⟨hzK z hz, hshift n z hz⟩ hp
  rcases (show EqOn (deriv f) 0 (ball a r) ∨ ∀ z ∈ ball a r, deriv f z ≠ 0 by
      by_cases hz : ∃ z ∈ ball a r, deriv f z ≠ 0
      · exact Or.inr (hurwitz_nonvanishing_limit isOpen_ball (convex_ball a r).isPreconnected
          (fun n => (hFd n).analyticOnNhd isOpen_ball) hFn hlim hz)
      · push_neg at hz
        exact Or.inl hz) with he | hn
  · have hc : ∀ z ∈ ball a r, fderivWithin ℂ f (ball a r) z = 0 := by
      intro z hz
      rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hz)
        ((hf z (hball hz)).differentiableAt (hU.mem_nhds (hball hz)))]
      apply ContinuousLinearMap.ext
      intro v
      simp only [fderiv_eq_smul_deriv, he hz, Pi.zero_apply, smul_zero,
        zero_apply]
    have hb : a + (r / 2 : ℝ) ∈ ball a r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have heq := (convex_ball a r).is_const_of_fderivWithin_eq_zero (hf.mono hball) hc
      (mem_ball_self hr) hb
    have hbad := hi ha (hball hb) heq
    have hz : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -hbad
    have : r / 2 = 0 := Complex.ofReal_eq_zero.mp hz
    linarith
  · exact hn a (mem_ball_self hr)

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PoissonExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poisson Extension. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

def poissonExtension (R : ℝ) (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  circleAverage (fun ζ => poissonKernel 0 w ζ * u ζ) 0 R

def schwarzExtension (R : ℝ) (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  circleAverage (fun ζ => herglotzRieszKernel 0 w ζ * (u ζ : ℂ)) 0 R

def dirichletExtension (R : ℝ) (u : ℂ → ℝ) : ℂ → ℝ :=
  (ball (0 : ℂ) R).piecewise (poissonExtension R u) u

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HarmonicReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Harmonic Reflection. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

def upperHalfBall (R : ℝ) : Set ℂ := ball 0 R ∩ {z | 0 < z.im}

def closedUpperHalfBall (R : ℝ) : Set ℂ := closedBall 0 R ∩ {z | 0 ≤ z.im}

def oddReflection (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then u z else -u (conj z)

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex InnerProductSpace Real

open scoped Classical ComplexConjugate

namespace CrouzeixHilbert.Conformal

structure BoundaryChart (U : Set ℂ) (p : ℂ) where
  e : OpenPartialHomeomorph ℂ ℂ
  zero_mem : (0 : ℂ) ∈ e.source
  at_zero : e 0 = p
  analytic : AnalyticOnNhd ℂ e e.source
  inverse_analytic : AnalyticOnNhd ℂ e.symm e.target
  side : ∀ z ∈ e.source, e z ∈ U ↔ 0 < z.im
  closed_side : ∀ z ∈ e.source, e z ∈ closure U ↔ 0 ≤ z.im

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.InteriorCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

namespace CrouzeixHilbert.Conformal

structure InteriorCollar (U : Set ℂ) where
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  closure_subset_domain : closure U ⊆ domain
  radius : ℝ
  one_lt_radius : 1 < radius
  f : ℂ → ℂ
  h : ℂ → ℂ
  analytic_f : AnalyticOnNhd ℂ f domain
  analytic_h : AnalyticOnNhd ℂ h (ball 0 radius)
  injective_f : InjOn f domain
  injective_h : InjOn h (ball 0 radius)
  bijective_f : BijOn f U (ball 0 1)
  bijective_h : BijOn h (ball 0 1) U
  closed_f : BijOn f (closure U) (closedBall 0 1)
  closed_h : BijOn h (closedBall 0 1) (closure U)
  inverse : InvOn h f domain (f '' domain)
  disk_subset : ball 0 radius ⊆ f '' domain
  boundary_norm : ∀ z ∈ frontier U, ‖f z‖ = 1

namespace InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma closedDisk_subset : closedBall (0 : ℂ) 1 ⊆ ball 0 R.radius := closedBall_subset_ball R.one_lt_radius

end InteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Forms. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

abbrev HS (k : ℕ) := EuclideanSpace ℂ (Fin k × Fin k)

def toHS {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : HS k :=
  WithLp.toLp 2 fun ij => A ij.1 ij.2

def ofHS {k : ℕ} (v : HS k) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => v (i,j)

@[simp] theorem ofHS_toHS {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ofHS (toHS A) = A := rfl

@[simp] theorem toHS_ofHS {k : ℕ} (v : HS k) : toHS (ofHS v) = v := by
  ext ij
  rfl

theorem norm_toHS_sq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  rfl

theorem lp_norm_sq_eq_integral {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

section Splitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure ThreeWaySplitting (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  proj : Fin 3 → E →L[ℝ] E
  self_adjoint : ∀ i, ContinuousLinearMap.adjoint (proj i) = proj i
  comp : ∀ i j, (proj i).comp (proj j) = if i = j then proj i else 0
  total : proj 0 + proj 1 + proj 2 = ContinuousLinearMap.id ℝ E

namespace ThreeWaySplitting

variable (s : ThreeWaySplitting E)

@[simp] theorem proj_proj (i j : Fin 3) (x : E) :
    s.proj i (s.proj j x) = if i = j then s.proj i x else 0 := by
  have h := congrArg (fun f : E →L[ℝ] E => f x) (s.comp i j)
  by_cases hij : i = j
  · subst j
    simpa using h
  · simpa [hij] using h

@[simp] theorem total_apply (x : E) : s.proj 0 x + s.proj 1 x + s.proj 2 x = x := by
  simpa only [add_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun f : E →L[ℝ] E => f x) s.total

def cauchyAdjoint (T : E →L[ℝ] E) : E →L[ℝ] E :=
  s.proj 0 + s.proj 1 + T.comp (s.proj 2)

@[simp] theorem cauchyAdjoint_apply (T : E →L[ℝ] E) (x : E) :
    s.cauchyAdjoint T x = s.proj 0 x + s.proj 1 x + T (s.proj 2 x) := rfl

variable {s} {T : E →L[ℝ] E}

omit [CompleteSpace E] in
theorem norm_apply_le_of_norm_le_one {L : E →L[ℝ] E} (hL : ‖L‖ ≤ 1) (x : E) :
    ‖L x‖ ≤ ‖x‖ := by
  calc
    ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg x)
    _ = ‖x‖ := one_mul _

structure CompatibleInvolution (s : ThreeWaySplitting E) where
  op : E ≃ₗᵢ[ℝ] E
  involutive : Function.Involutive op
  proj_zero : ∀ x, op (s.proj 0 x) = s.proj 0 (op x)
  proj_pos : ∀ x, op (s.proj 1 x) = s.proj 2 (op x)

namespace CompatibleInvolution

variable (j : CompatibleInvolution s)

@[simp] theorem op_op (x : E) : j.op (j.op x) = x := j.involutive x

end CompatibleInvolution

end ThreeWaySplitting

end Splitting

section FieldAction

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def fieldAction (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) : Lp E 2 μ →L[ℝ] Lp E 2 μ := by
  let mem : ∀ u : Lp E 2 μ, MemLp (fun t => L t (u t)) 2 μ := fun u =>
    (Lp.memLp u).mono
      ((show Continuous (fun z : (E →L[ℝ] E) × E => z.1 z.2) by fun_prop).comp_aestronglyMeasurable (hL.prodMk (Lp.aestronglyMeasurable u)))
      (hLn.mono fun t ht => by
        calc
          ‖L t (u t)‖ ≤ ‖L t‖ * ‖u t‖ := (L t).le_opNorm _
          _ ≤ 1 * ‖u t‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg _)
          _ = ‖u t‖ := one_mul _)
  let M : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ := {
    toFun u := (mem u).toLp _
    map_add' u v := by
      apply Lp.ext
      filter_upwards [(mem (u + v)).coeFn_toLp, (mem u).coeFn_toLp,
        (mem v).coeFn_toLp, Lp.coeFn_add u v,
        Lp.coeFn_add ((mem u).toLp _) ((mem v).toLp _)] with t huv hu hv ha hb
      simp only [huv, hb, hu, hv, ha, map_add, Pi.add_apply]
    map_smul' c u := by
      apply Lp.ext
      filter_upwards [(mem (c • u)).coeFn_toLp, (mem u).coeFn_toLp,
        Lp.coeFn_smul c u, Lp.coeFn_smul c ((mem u).toLp _)] with t hcu hu ha hb
      simp only [hcu, hb, hu, ha, map_smul, Pi.smul_apply, RingHom.id_apply] }
  apply M.mkContinuous 1
  intro u
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(mem u).coeFn_toLp, hLn] with t ht hn
  change ‖((mem u).toLp _) t‖ ≤ ‖u t‖
  rw [ht]
  exact ThreeWaySplitting.norm_apply_le_of_norm_le_one hn _

end FieldAction

section MatrixMultipliers

def hsEquiv (k : ℕ) : Matrix (Fin k) (Fin k) ℂ ≃ₗ[ℝ] HS k where
  toFun := toHS
  invFun := ofHS
  left_inv := ofHS_toHS
  right_inv := toHS_ofHS
  map_add' A B := by ext ij; rfl
  map_smul' c A := by ext ij; rfl

@[simp] theorem hsEquiv_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    hsEquiv k A = toHS A := rfl

@[simp] theorem hsEquiv_symm_apply {k : ℕ} (u : HS k) :
    (hsEquiv k).symm u = ofHS u := rfl

theorem norm_toHS_conjTranspose {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS Aᴴ‖ = ‖toHS A‖ := by
  have h : ‖toHS Aᴴ‖ ^ 2 = ‖toHS A‖ ^ 2 := by
    simp only [norm_toHS_sq, Matrix.conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (toHS Aᴴ), norm_nonneg (toHS A)]

theorem norm_toHS_mul_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS (A * B)‖ ≤ ‖A‖ * ‖toHS B‖ := by
  let col : Matrix (Fin k) (Fin k) ℂ → Fin k → EuclideanSpace ℂ (Fin k) :=
    fun M j => WithLp.toLp 2 (fun i => M i j)
  have hcol (M : Matrix (Fin k) (Fin k) ℂ) :
      ‖toHS M‖ ^ 2 = ∑ j, ‖col M j‖ ^ 2 := by
    rw [norm_toHS_sq]
    simp only [PiLp.norm_sq_eq_of_L2, col]
    change (∑ i, ∑ j, ‖M i j‖ ^ 2) = ∑ j, ∑ i, ‖M i j‖ ^ 2
    exact Finset.sum_comm
  have hn (j : Fin k) : ‖col (A * B) j‖ ≤ ‖A‖ * ‖col B j‖ := by
    exact Matrix.l2_opNorm_mulVec A (col B j)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [hcol, mul_pow, hcol, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hn j) 2

theorem norm_toHS_mul_le_right {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ‖toHS (A * B)‖ ≤ ‖toHS A‖ * ‖B‖ := by
  calc
    ‖toHS (A * B)‖ = ‖toHS (Bᴴ * Aᴴ)‖ := by
      rw [← Matrix.conjTranspose_mul, norm_toHS_conjTranspose]
    _ ≤ ‖Bᴴ‖ * ‖toHS Aᴴ‖ := norm_toHS_mul_le _ _
    _ = ‖toHS A‖ * ‖B‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, norm_toHS_conjTranspose, mul_comm]

def hsLeft {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : HS k →L[ℝ] HS k :=
  ((hsEquiv k).toLinearMap.comp
    ((LinearMap.mulLeft ℝ A).comp (hsEquiv k).symm.toLinearMap)).toContinuousLinearMap

def hsRight {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : HS k →L[ℝ] HS k :=
  ((hsEquiv k).toLinearMap.comp
    ((LinearMap.mulRight ℝ A).comp (hsEquiv k).symm.toLinearMap)).toContinuousLinearMap

@[simp] theorem hsLeft_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : HS k) :
    hsLeft A u = toHS (A * ofHS u) := rfl

@[simp] theorem hsRight_apply {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (u : HS k) :
    hsRight A u = toHS (ofHS u * A) := rfl

theorem norm_hsLeft_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖hsLeft A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  simpa only [hsLeft_apply, toHS_ofHS] using norm_toHS_mul_le A (ofHS u)

theorem norm_hsRight_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ‖hsRight A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  simpa only [hsRight_apply, toHS_ofHS, mul_comm] using norm_toHS_mul_le_right (ofHS u) A

def hsLeftCoefficient (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ →L[ℝ] (HS k →L[ℝ] HS k) :=
  ({ toFun := hsLeft
     map_add' := fun A B => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS ((A + B) * ofHS u) = toHS (A * ofHS u) + toHS (B * ofHS u)
       rw [add_mul]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_add _ _
     map_smul' := fun c A => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS ((c • A) * ofHS u) = c • toHS (A * ofHS u)
       rw [Matrix.smul_mul]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_smul c _ } :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] (HS k →L[ℝ] HS k)).toContinuousLinearMap

def hsRightCoefficient (k : ℕ) :
    Matrix (Fin k) (Fin k) ℂ →L[ℝ] (HS k →L[ℝ] HS k) :=
  ({ toFun := hsRight
     map_add' := fun A B => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS (ofHS u * (A + B)) = toHS (ofHS u * A) + toHS (ofHS u * B)
       rw [mul_add]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_add _ _
     map_smul' := fun c A => by
       apply ContinuousLinearMap.ext
       intro u
       change toHS (ofHS u * (c • A)) = c • toHS (ofHS u * A)
       rw [Matrix.mul_smul]
       simpa only [hsEquiv_apply] using (hsEquiv k).map_smul c _ } :
    Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] (HS k →L[ℝ] HS k)).toContinuousLinearMap

def hsStar (k : ℕ) : HS k ≃ₗᵢ[ℝ] HS k where
  toFun u := toHS (ofHS u)ᴴ
  invFun u := toHS (ofHS u)ᴴ
  left_inv u := by simp
  right_inv u := by simp
  map_add' u v := by
    change toHS ((ofHS u + ofHS v)ᴴ) = _
    rw [Matrix.conjTranspose_add]
    simpa only [hsEquiv_apply] using (hsEquiv k).map_add _ _
  map_smul' c u := by
    change toHS ((c • ofHS u)ᴴ) = c • toHS (ofHS u)ᴴ
    rw [Matrix.conjTranspose_smul, star_trivial]
    simpa only [hsEquiv_apply] using (hsEquiv k).map_smul c _
  norm_map' u := by
    change ‖toHS (ofHS u)ᴴ‖ = ‖u‖
    rw [norm_toHS_conjTranspose, toHS_ofHS]

@[simp] theorem hsStar_apply {k : ℕ} (u : HS k) : hsStar k u = toHS (ofHS u)ᴴ := rfl

@[simp] theorem hsStar_hsStar {k : ℕ} (u : HS k) : hsStar k (hsStar k u) = u := by simp

end MatrixMultipliers

section L2Multipliers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : ℕ}

def lpStar : Lp (HS k) 2 μ ≃ₗᵢ[ℝ] Lp (HS k) 2 μ := by
  let M := (hsStar k).toContinuousLinearMap.compLpL 2 μ
  have hinv : Function.Involutive M := by
    intro u
    apply Lp.ext
    filter_upwards [(hsStar k).toContinuousLinearMap.coeFn_compLpL u,
      (hsStar k).toContinuousLinearMap.coeFn_compLpL (M u)] with t hu hMu
    exact hMu.trans (by change hsStar k (M u t) = u t; rw [hu]; exact hsStar_hsStar _)
  refine {
    toLinearEquiv := {
      toLinearMap := M.toLinearMap
      invFun := M
      left_inv := hinv
      right_inv := hinv }
    norm_map' := fun u => ?_ }
  have hn : ∀ᵐ t ∂μ, ‖M u t‖ = ‖u t‖ :=
    ((hsStar k).toContinuousLinearMap.coeFn_compLpL u).mono fun t ht => by
      rw [ht]
      exact (hsStar k).norm_map _
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono fun _ ht => ht.le))
    (Lp.norm_le_norm_of_ae_le (hn.mono fun _ ht => ht.ge))

def lpLeft (F : α → Matrix (Fin k) (Fin k) ℂ) (hm : AEStronglyMeasurable F μ)
    (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) : Lp (HS k) 2 μ →L[ℝ] Lp (HS k) 2 μ :=
  fieldAction (fun t => hsLeft (F t))
    ((hsLeftCoefficient k).continuous.comp_aestronglyMeasurable hm)
    (hn.mono fun _ ht => (norm_hsLeft_le _).trans ht)

def lpRight (F : α → Matrix (Fin k) (Fin k) ℂ) (hm : AEStronglyMeasurable F μ)
    (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) : Lp (HS k) 2 μ →L[ℝ] Lp (HS k) 2 μ :=
  fieldAction (fun t => hsRight (F t))
    ((hsRightCoefficient k).continuous.comp_aestronglyMeasurable hm)
    (hn.mono fun _ ht => (norm_hsRight_le _).trans ht)

end L2Multipliers

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace lp Classical Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

abbrev CircleSpace := AddCircle (1 : ℝ)

local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev circleMeasure : Measure CircleSpace := AddCircle.haarAddCircle

abbrev BoundaryL2 (k : ℕ) := Lp (HS k) 2 circleMeasure

def lpEntry {k : ℕ} (ij : Fin k × Fin k) : BoundaryL2 k →L[ℂ] Lp ℂ 2 circleMeasure :=
  (PiLp.proj 2 (fun _ : Fin k × Fin k => ℂ) ij).compLpL 2 circleMeasure

lemma lpEntry_apply_ae {k : ℕ} (ij : Fin k × Fin k) (u : BoundaryL2 k) :
    lpEntry ij u =ᵐ[circleMeasure] fun t => u t ij :=
  ContinuousLinearMap.coeFn_compLpL _ _

def matrixFourier {k : ℕ} (a : ℤ × (Fin k × Fin k)) : BoundaryL2 k :=
  ContinuousMap.toLp 2 circleMeasure ℂ
    ⟨fun t => fourier a.1 t • EuclideanSpace.single a.2 (1 : ℂ),
      by fun_prop⟩

lemma matrixFourier_apply_ae {k : ℕ} (a : ℤ × (Fin k × Fin k)) :
    matrixFourier a =ᵐ[circleMeasure]
      fun t => fourier a.1 t • EuclideanSpace.single a.2 (1 : ℂ) :=
  ContinuousMap.coeFn_toLp _ _

lemma inner_matrixFourier {k : ℕ} (a : ℤ × (Fin k × Fin k)) (u : BoundaryL2 k) :
    ⟪matrixFourier a, u⟫_ℂ = ⟪fourierLp 2 a.1, lpEntry a.2 u⟫_ℂ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [matrixFourier_apply_ae a, lpEntry_apply_ae a.2 u,
    coeFn_fourierLp 2 a.1] with t hm he hf
  rw [hm, he, hf, inner_smul_left, EuclideanSpace.inner_single_left]
  simp [RCLike.inner_apply, mul_comm]

lemma lpEntry_matrixFourier {k : ℕ} (a : ℤ × (Fin k × Fin k)) (ij : Fin k × Fin k) :
    lpEntry ij (matrixFourier a) = if ij = a.2 then fourierLp 2 a.1 else 0 := by
  apply Lp.ext
  filter_upwards [lpEntry_apply_ae ij (matrixFourier a), matrixFourier_apply_ae a,
    coeFn_fourierLp 2 a.1, (Lp.coeFn_zero ℂ 2 circleMeasure)] with t he hm hf hz
  rw [he, hm]
  by_cases hij : ij = a.2
  · subst ij
    simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
    exact hf.symm
  · simp only [ite_eq_right hij, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_zero]
    exact hz.symm

lemma orthonormal_matrixFourier (k : ℕ) :
    Orthonormal ℂ (@matrixFourier k) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_matrixFourier, lpEntry_matrixFourier]
  by_cases hab : a.2 = b.2
  · rw [ite_eq_left hab, orthonormal_iff_ite.mp orthonormal_fourier]
    simp [Prod.ext_iff, hab]
  · rw [ite_eq_right hab, inner_zero_right, ite_eq_right]
    exact fun h => hab (congrArg Prod.snd h)

lemma lpEntry_ext {k : ℕ} {u v : BoundaryL2 k}
    (h : ∀ ij, lpEntry ij u = lpEntry ij v) : u = v := by
  apply Lp.ext
  have he : ∀ᵐ t ∂circleMeasure, ∀ ij, u t ij = v t ij := by
    rw [ae_all_iff]
    intro ij
    filter_upwards [lpEntry_apply_ae ij u, lpEntry_apply_ae ij v] with t hu hv
    rw [← hu, ← hv, h ij]
  exact he.mono fun t ht => by ext ij; exact ht ij

lemma matrixFourier_orthogonal_eq_bot (k : ℕ) :
    (Submodule.span ℂ (Set.range (@matrixFourier k)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply lpEntry_ext
  intro ij
  rw [map_zero]
  apply fourierBasis.repr.injective
  ext n
  rw [map_zero]
  change _ = 0
  rw [fourierBasis.repr_apply_apply, coe_fourierBasis]
  rw [← inner_matrixFourier (n,ij)]
  exact (Submodule.mem_orthogonal _ _).mp hu _ (Submodule.subset_span ⟨(n,ij), rfl⟩)

def matrixFourierBasis (k : ℕ) :
    HilbertBasis (ℤ × (Fin k × Fin k)) ℂ (BoundaryL2 k) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_matrixFourier k) (matrixFourier_orthogonal_eq_bot k)

@[simp] lemma matrixFourierBasis_apply {k : ℕ} (a : ℤ × (Fin k × Fin k)) :
    matrixFourierBasis k a = matrixFourier a := by
  rw [matrixFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

def l2Mask {ι : Type*} (S : ι → Prop) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) := by
  classical
  let M : ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(ι, ℂ) := {
    toFun u := ⟨fun i => if S i then u i else 0,
      (lp.memℓp u).mono' fun i => by split_ifs <;> simp⟩
    map_add' u v := by
      ext i
      change (if S i then u i + v i else 0) =
        (if S i then u i else 0) + (if S i then v i else 0)
      by_cases hi : S i <;> simp [hi]
    map_smul' c u := by ext i; by_cases hi : S i <;> simp [hi] }
  apply M.mkContinuous 1
  intro u
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro i
  change ‖if S i then u i else 0‖ ≤ ‖u i‖
  split_ifs <;> simp

@[simp] lemma l2Mask_apply {ι : Type*} (S : ι → Prop) (u : ℓ²(ι, ℂ)) (i : ι) :
    l2Mask S u i = if S i then u i else 0 := by classical exact rfl

def frequencyPart (i : Fin 3) (n : ℤ) : Prop :=
  if i = 0 then n = 0 else if i = 1 then 0 < n else n < 0

@[simp] lemma frequencyPart_zero (n : ℤ) : frequencyPart 0 n ↔ n = 0 := by
  simp [frequencyPart]

@[simp] lemma frequencyPart_pos (n : ℤ) : frequencyPart 1 n ↔ 0 < n := by
  simp [frequencyPart]

@[simp] lemma frequencyPart_neg (n : ℤ) : frequencyPart 2 n ↔ n < 0 := by
  simp [frequencyPart]

def fourierProjC (k : ℕ) (i : Fin 3) : BoundaryL2 k →L[ℂ] BoundaryL2 k :=
  ((matrixFourierBasis k).repr.symm.toContinuousLinearEquiv :
      ℓ²(ℤ × (Fin k × Fin k), ℂ) →L[ℂ] BoundaryL2 k).comp
    ((l2Mask (fun a => frequencyPart i a.1)).comp
      (matrixFourierBasis k).repr.toContinuousLinearEquiv.toContinuousLinearMap)

lemma repr_fourierProjC {k : ℕ} (i : Fin 3) (u : BoundaryL2 k)
    (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr (fourierProjC k i u) a =
      if frequencyPart i a.1 then (matrixFourierBasis k).repr u a else 0 := by
  classical
  simp [fourierProjC]

lemma fourierProjC_self_adjoint (k : ℕ) (i : Fin 3) :
    ContinuousLinearMap.adjoint (fourierProjC k i) = fourierProjC k i := by
  classical
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [← (matrixFourierBasis k).repr.inner_map_map, lp.inner_eq_tsum]
  rw [← (matrixFourierBasis k).repr.inner_map_map u, lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  rw [repr_fourierProjC, repr_fourierProjC]
  by_cases ha : frequencyPart i a.1 <;> simp [ha]

lemma fourierProjC_comp (k : ℕ) (i j : Fin 3) :
    (fourierProjC k i).comp (fourierProjC k j) =
      if i = j then fourierProjC k i else 0 := by
  classical
  apply ContinuousLinearMap.ext
  intro u
  apply (matrixFourierBasis k).repr.injective
  ext a
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [repr_fourierProjC, repr_fourierProjC]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, repr_fourierProjC]
    split_ifs <;> rfl
  · rw [ite_eq_right hij]
    simp only [zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
    have hd : ¬ (frequencyPart i a.1 ∧ frequencyPart j a.1) := by
      fin_cases i <;> fin_cases j <;> simp_all <;> omega
    split_ifs <;> simp_all

lemma fourierProjC_total (k : ℕ) :
    fourierProjC k 0 + fourierProjC k 1 + fourierProjC k 2 =
      ContinuousLinearMap.id ℂ (BoundaryL2 k) := by
  classical
  apply ContinuousLinearMap.ext
  intro u
  apply (matrixFourierBasis k).repr.injective
  ext a
  simp only [add_apply, map_add, lp.coeFn_add, Pi.add_apply,
    ContinuousLinearMap.id_apply, repr_fourierProjC]
  rcases lt_trichotomy a.1 0 with hn | hn | hn
  · simp [hn, hn.ne, not_lt.mpr hn.le]
  · simp [hn]
  · simp [hn, hn.ne', not_lt.mpr hn.le]

lemma boundary_real_inner {k : ℕ} (u v : BoundaryL2 k) :
    ⟪u,v⟫_ℝ = (⟪u,v⟫_ℂ).re := by
  simp only [L2.inner_def]
  calc
    _ = ∫ t, (⟪u t,v t⟫_ℂ).re ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [PiLp.inner_apply, Complex.re_sum]
      rfl
    _ = _ := integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) u v)

def fourierSplitting (k : ℕ) : ThreeWaySplitting (BoundaryL2 k) where
  proj i := (fourierProjC k i).restrictScalars ℝ
  self_adjoint i := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro u v
    change ⟪fourierProjC k i u, v⟫_ℝ = ⟪u, fourierProjC k i v⟫_ℝ
    rw [boundary_real_inner, boundary_real_inner]
    have h := ContinuousLinearMap.adjoint_inner_left (fourierProjC k i) v u
    rw [fourierProjC_self_adjoint] at h
    exact congrArg Complex.re h
  comp i j := by
    apply ContinuousLinearMap.ext
    intro u
    have h := congrArg (fun L : BoundaryL2 k →L[ℂ] BoundaryL2 k => L u)
      (fourierProjC_comp k i j)
    split_ifs with hij <;> simpa [hij] using h
  total := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg (fun L : BoundaryL2 k →L[ℂ] BoundaryL2 k => L u) (fourierProjC_total k)

def matrixMean {k : ℕ} (u : BoundaryL2 k) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∫ t, u t (i,j) ∂circleMeasure

def upperTransfer {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  ((fourierSplitting k).proj 1).comp (ContinuousLinearMap.adjoint M)

def boundaryCauchyAdjoint {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  (fourierSplitting k).cauchyAdjoint (upperTransfer M)

def boundaryCauchy {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  (fourierSplitting k).proj 0 + (fourierSplitting k).proj 1 +
    ((fourierSplitting k).proj 2).comp (M.comp ((fourierSplitting k).proj 1))

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Operators. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Boundary

local instance boundaryOperatorsFactOnePos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma norm_integral_weight_sq_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (w : α → ℝ) (u : α → E)
    (hw0 : ∀ᵐ t ∂μ, 0 ≤ w t) (hw : Integrable w μ)
    (hwu : Integrable (fun t => w t • u t) μ)
    (hwu2 : Integrable (fun t => w t * ‖u t‖ ^ 2) μ)
    (hw1 : ∫ t, w t ∂μ = 1) :
    ‖∫ t, w t • u t ∂μ‖ ^ 2 ≤ ∫ t, w t * ‖u t‖ ^ 2 ∂μ := by
  let v := ∫ t, w t • u t ∂μ
  have hi := integral_mono_ae (((hwu.const_inner v)).const_mul 2)
    ((hw.mul_const (‖v‖ ^ 2)).add hwu2) (hw0.mono fun t ht => by
      simp only [Pi.add_apply, real_inner_smul_right]
      have h := sq_nonneg ‖v - u t‖
      rw [norm_sub_sq_real] at h
      nlinarith [mul_nonneg ht h])
  have hv : ∫ t, ⟪v, w t • u t⟫_ℝ ∂μ = ‖v‖ ^ 2 := by
    rw [integral_inner hwu v]
    exact real_inner_self_eq_norm_sq v
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, hv, integral_add (hw.mul_const _) hwu2,
    integral_mul_const, hw1, one_mul] at hi
  linarith

abbrev CircleKernel := C(CircleSpace × CircleSpace, ℝ)

def kernelApply {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) (x : CircleSpace) : HS k :=
  ∫ y, m (x,y) • u y ∂circleMeasure

lemma boundaryLp_integrable {k : ℕ} (u : BoundaryL2 k) : Integrable u circleMeasure :=
  (Lp.memLp u).integrable (by norm_num)

lemma kernel_integrable {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) (x : CircleSpace) :
    Integrable (fun y => m (x,y) • u y) circleMeasure := by
  have hm : AEStronglyMeasurable (fun y => m (x,y)) circleMeasure :=
    (m.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  change Integrable ((fun y => m (x,y)) • (u : CircleSpace → HS k)) circleMeasure
  exact Integrable.bdd_smul (𝕜 := ℝ) (boundaryLp_integrable u) ‖m‖ hm
    (Filter.Eventually.of_forall fun y => m.norm_coe_le_norm (x,y))

lemma kernel_sq_integrable {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) (x : CircleSpace) :
    Integrable (fun y => m (x,y) * ‖u y‖ ^ 2) circleMeasure := by
  have hm : AEStronglyMeasurable (fun y => m (x,y)) circleMeasure :=
    (m.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact ((Lp.memLp u).norm.integrable_sq).bdd_mul hm
    (Filter.Eventually.of_forall fun y => m.norm_coe_le_norm (x,y))

lemma continuous_kernelApply {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    Continuous (kernelApply m u) := by
  apply continuous_of_dominated (bound := fun y => ‖m‖ * ‖u y‖)
  · intro x
    exact (kernel_integrable m u x).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm (x,y)) (norm_nonneg _)
  · exact (boundaryLp_integrable u).norm.const_mul _
  · exact Filter.Eventually.of_forall fun y =>
      (m.continuous.comp (continuous_id.prodMk continuous_const)).smul continuous_const

def kernelLp {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) : BoundaryL2 k :=
  ContinuousMap.toLp 2 circleMeasure ℝ ⟨kernelApply m u, continuous_kernelApply m u⟩

lemma kernelLp_apply_ae {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    kernelLp m u =ᵐ[circleMeasure] kernelApply m u := ContinuousMap.coeFn_toLp _ _

lemma norm_kernelApply_sq_le {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (u : BoundaryL2 k) (x : CircleSpace) :
    ‖kernelApply m u x‖ ^ 2 ≤ ∫ y, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure := by
  apply norm_integral_weight_sq_le (μ := circleMeasure) (fun y => m (x,y)) u
    (Filter.Eventually.of_forall fun y => hm (x,y))
  · exact (m.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact kernel_integrable m u x
  · exact kernel_sq_integrable m u x
  · exact hm1 x

lemma kernel_sq_integrable_prod {k : ℕ} (m : CircleKernel) (u : BoundaryL2 k) :
    Integrable (fun z : CircleSpace × CircleSpace => m z * ‖u z.2‖ ^ 2)
      (circleMeasure.prod circleMeasure) :=
  (((Lp.memLp u).norm.integrable_sq).comp_snd circleMeasure).bdd_mul
    m.continuous.aestronglyMeasurable (Filter.Eventually.of_forall m.norm_coe_le_norm)

lemma norm_kernelLp_le {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) (u : BoundaryL2 k) :
    ‖kernelLp m u‖ ≤ ‖u‖ := by
  have hs : ‖kernelLp m u‖ ^ 2 ≤ ‖u‖ ^ 2 := calc
    _ = ∫ x, ‖kernelLp m u x‖ ^ 2 ∂circleMeasure := lp_norm_sq_eq_integral _
    _ ≤ ∫ x, ∫ y, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure ∂circleMeasure := by
      apply integral_mono_ae ((Lp.memLp (kernelLp m u)).norm.integrable_sq)
        (kernel_sq_integrable_prod m u).integral_prod_left
      filter_upwards [kernelLp_apply_ae m u] with x hx
      rw [hx]
      exact norm_kernelApply_sq_le m hm hm1 u x
    _ = ∫ y, ∫ x, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure ∂circleMeasure :=
      integral_integral_swap (kernel_sq_integrable_prod m u)
    _ = ∫ y, ‖u y‖ ^ 2 ∂circleMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (∫ x, m (x,y) * ‖u y‖ ^ 2 ∂circleMeasure) = ‖u y‖ ^ 2
        rw [integral_mul_const, hm2, one_mul]
    _ = ‖u‖ ^ 2 := (lp_norm_sq_eq_integral _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

lemma kernelLp_add {k : ℕ} (m : CircleKernel) (u v : BoundaryL2 k) :
    kernelLp m (u + v) = kernelLp m u + kernelLp m v := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (u+v), kernelLp_apply_ae m u, kernelLp_apply_ae m v,
    Lp.coeFn_add (kernelLp m u) (kernelLp m v)] with x huv hu hv hsum
  simp only [huv, hsum, Pi.add_apply, hu, hv]
  simp only [kernelApply]
  calc
    _ = ∫ y, m (x,y) • u y + m (x,y) • v y ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add u v] with y hy
      simp only [hy, Pi.add_apply, smul_add]
    _ = _ := integral_add (kernel_integrable m u x) (kernel_integrable m v x)

lemma kernelLp_smul {k : ℕ} (m : CircleKernel) (c : ℝ) (u : BoundaryL2 k) :
    kernelLp m (c • u) = c • kernelLp m u := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (c • u), kernelLp_apply_ae m u,
    Lp.coeFn_smul c (kernelLp m u)] with x hcu hu hsmul
  simp only [hcu, hsmul, Pi.smul_apply, hu]
  simp only [kernelApply]
  calc
    _ = ∫ y, c • (m (x,y) • u y) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c u] with y hy
      rw [hy]
      change m (x,y) • (c • u y) = c • (m (x,y) • u y)
      exact smul_comm _ _ _
    _ = _ := integral_smul c _

def kernelOperator {k : ℕ} (m : CircleKernel)
    (hm : ∀ x, 0 ≤ m x) (hm1 : ∀ x, ∫ y, m (x,y) ∂circleMeasure = 1)
    (hm2 : ∀ y, ∫ x, m (x,y) ∂circleMeasure = 1) :
    BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  ({ toFun := kernelLp m
     map_add' := kernelLp_add m
     map_smul' := kernelLp_smul m } : BoundaryL2 k →ₗ[ℝ] BoundaryL2 k).mkContinuous 1
    (fun u => by
      change ‖kernelLp m u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_kernelLp_le m hm hm1 hm2 u)

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Density. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

section PartialTraces

variable {n m : Type*} [Fintype n]

def crossPartialTrace (X Y : Matrix n m ℂ) : Matrix m m ℂ :=
  (Xᴴ * Y)ᵀ

variable [Fintype m]

def weightedPartialTrace (E : Matrix n n ℂ) (X Y : Matrix n m ℂ) : Matrix m m ℂ :=
  (Xᴴ * E * Y)ᵀ

end PartialTraces

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.SteinMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stein Metric. -/

noncomputable section

open Set Filter

open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Metric

section StablePowers

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem eventually_norm_pow_le (a : A) (ha : spectralRadius ℂ a < 1)
    {r : ℝ} (hr : (spectralRadius ℂ a).toReal < r) :
    ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ r ^ n := by
  have ht : spectralRadius ℂ a ≠ ∞ := ne_of_lt (ha.trans (by simp))
  have hl : Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a).toReal) := by
    simpa only [Function.comp_def,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using
      (ENNReal.tendsto_toReal ht).comp
        (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a)
  filter_upwards [hl.eventually (gt_mem_nhds hr), eventually_gt_atTop (0 : ℕ)]
    with n hn hn0
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg (a ^ n)) _) hn.le n
  simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg (a ^ n))
    (Nat.ne_of_gt hn0)] using h

theorem summable_norm_pow (a : A) (ha : spectralRadius ℂ a < 1) :
    Summable (fun n : ℕ => ‖a ^ n‖) := by
  have ht : spectralRadius ℂ a ≠ ∞ := ne_of_lt (ha.trans (by simp))
  have hlt : (spectralRadius ℂ a).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal ht (by simp)).mpr ha
  obtain ⟨r, hr, hr1⟩ := exists_between hlt
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg.trans hr.le
  apply (summable_geometric_of_lt_one hr0 hr1).of_norm_bounded_eventually
  simpa only [Real.norm_of_nonneg (norm_nonneg _), Nat.cofinite_eq_atTop] using
    eventually_norm_pow_le a ha hr

end StablePowers

section Stein

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def steinSeries (T : A) : A := ∑' j : ℕ, star (T ^ j) * T ^ j

end Stein

section Minimization

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure Feasible (T : A) (τ : ℝ) (H : A) : Prop where
  lower : 1 ≤ H
  upper : H ≤ algebraMap ℝ A τ
  stein : star T * H * T ≤ H

end Minimization

end CrouzeixHilbert.Metric

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint. -/

noncomputable section

open Set Filter

open scoped Topology MatrixOrder Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Endpoint

section Cone

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev Herm (A : Type*) [CStarAlgebra A] := selfAdjoint.submodule ℝ A

instance instPosSMulMonoRealSubtypeMemSubmoduleHerm : PosSMulMono ℝ (Herm A) where
  smul_le_smul_of_nonneg_left {r} hr {x y} h := by
    change r • (x : A) ≤ r • (y : A)
    exact smul_le_smul_of_nonneg_left h hr

def unit : Herm A := ⟨1, IsSelfAdjoint.one A⟩

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem unit_val : ((unit : Herm A) : A) = 1 := rfl

def strictCone : Set (Herm A) :=
  {H | ∃ ε : ℝ, 0 < ε ∧ ε • (unit : Herm A) ≤ H}

def congruence (T : A) : Herm A →ₗ[ℝ] Herm A where
  toFun H := ⟨star T * H * T, by
    change IsSelfAdjoint (star T * (H : A) * T)
    simpa only [star_star] using H.property.conjugate (star T)⟩
  map_add' H J := by
    apply Subtype.ext
    simp only [Submodule.coe_add, mul_add, add_mul]
  map_smul' r H := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem congruence_val (T : A) (H : Herm A) :
    ((congruence T H : Herm A) : A) = star T * H * T := rfl

end Cone

section Separation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev SlackSpace (A : Type*) [CStarAlgebra A] := ℝ × Herm A × Herm A × Herm A

def slacks (T : A) (s : ℝ) (H : Herm A) : SlackSpace A :=
  (s, H - unit, s • unit - H, H - congruence T H)

def lowerOpen (τ : ℝ) : Set (SlackSpace A) :=
  Iio τ ×ˢ strictCone ×ˢ strictCone ×ˢ strictCone

def scalarPart (f : SlackSpace A →L[ℝ] ℝ) : ℝ := f (1, 0, 0, 0)

def firstPart (f : SlackSpace A →L[ℝ] ℝ) : Herm A →L[ℝ] ℝ :=
  -(f.comp ((ContinuousLinearMap.inr ℝ ℝ (Herm A × Herm A × Herm A)).comp
    (ContinuousLinearMap.inl ℝ (Herm A) (Herm A × Herm A))))

def secondPart (f : SlackSpace A →L[ℝ] ℝ) : Herm A →L[ℝ] ℝ :=
  -(f.comp ((ContinuousLinearMap.inr ℝ ℝ (Herm A × Herm A × Herm A)).comp
    ((ContinuousLinearMap.inr ℝ (Herm A) (Herm A × Herm A)).comp
      (ContinuousLinearMap.inl ℝ (Herm A) (Herm A)))))

def thirdPart (f : SlackSpace A →L[ℝ] ℝ) : Herm A →L[ℝ] ℝ :=
  -(f.comp ((ContinuousLinearMap.inr ℝ ℝ (Herm A × Herm A × Herm A)).comp
    ((ContinuousLinearMap.inr ℝ (Herm A) (Herm A × Herm A)).comp
      (ContinuousLinearMap.inr ℝ (Herm A) (Herm A)))))

structure DualCertificate (T : A) (τ : ℝ) (H : Herm A) where
  X : Herm A →L[ℝ] ℝ
  Y : Herm A →L[ℝ] ℝ
  Z : Herm A →L[ℝ] ℝ
  X_positive : ∀ J, 0 ≤ J → 0 ≤ X J
  Y_positive : ∀ J, 0 ≤ J → 0 ≤ Y J
  Z_positive : ∀ J, 0 ≤ J → 0 ≤ Z J
  X_unit : X unit = 1
  Y_unit : Y unit = τ
  balance : ∀ J, X J - Y J = Z J - Z (congruence T J)
  Y_slack : Y (H - unit) = 0
  X_slack : X (τ • unit - H) = 0
  Z_slack : Z (H - congruence T H) = 0

end Separation

section Riesz

open scoped InnerProductSpace ComplexOrder

open Boundary

def hermHS (n : ℕ) : Submodule ℝ (HS n) :=
  LinearMap.ker ((hsStar n).toLinearEquiv.toLinearMap - LinearMap.id)

@[simp] theorem mem_hermHS {n : ℕ} (u : HS n) :
    u ∈ hermHS n ↔ (ofHS u).IsHermitian := by
  simp only [hermHS, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, sub_eq_zero,
    hsStar_apply, Matrix.IsHermitian]
  constructor
  · intro h
    exact congrArg ofHS h
  · intro h
    rw [h, toHS_ofHS]

def hermHSCoordinate (n : ℕ) : hermHS n →ₗ[ℝ] Herm (Matrix (Fin n) (Fin n) ℂ) where
  toFun u := ⟨ofHS u, (mem_hermHS u.val).mp u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Riesz

end CrouzeixHilbert.Endpoint

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realization. -/

noncomputable section

open Set Filter

open scoped Topology InnerProductSpace

namespace CrouzeixHilbert.Realization

section Pair

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev SumSpace (H : Type*) [NormedAddCommGroup H] := WithLp 2 (H × H)

def pairL (A B : E →L[ℂ] H) : E →L[ℂ] SumSpace H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp (A.prod B)

def rowL (A B : H →L[ℂ] E) : SumSpace H →L[ℂ] E :=
  A.comp (WithLp.fstL 2 ℂ H H) + B.comp (WithLp.sndL 2 ℂ H H)

@[simp] theorem pairL_apply (A B : E →L[ℂ] H) (x : E) :
    pairL A B x = WithLp.toLp 2 (A x, B x) := rfl

@[simp] theorem rowL_apply (A B : H →L[ℂ] E) (x : SumSpace H) :
    rowL A B x = A x.fst + B x.snd := rfl

end Pair

section Transfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure Colligation (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  unitary : SumSpace H ≃ₗᵢ[ℂ] SumSpace H

namespace Colligation

def a (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 1 0))

def b (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 0 1))

def c (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.sndL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 1 0))

def d (C : Colligation H) : H →L[ℂ] H :=
  (WithLp.sndL 2 ℂ H H).comp
    (C.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp (pairL 0 1))

def transfer (C : Colligation H) (z : ℂ) : H →L[ℂ] H :=
  C.d + z • (C.c * Ring.inverse (1 - z • C.a) * C.b)

end Colligation

end Transfer

end CrouzeixHilbert.Realization

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.MatrixEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix Endpoint. -/

noncomputable section

open Set Filter

open scoped InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace CrouzeixHilbert.Endpoint

open Boundary

structure MatrixCertificate {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (τ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) where
  X : Matrix (Fin n) (Fin n) ℂ
  Y : Matrix (Fin n) (Fin n) ℂ
  Z : Matrix (Fin n) (Fin n) ℂ
  X_positive : X.PosSemidef
  Y_positive : Y.PosSemidef
  Z_positive : Z.PosSemidef
  X_trace : X.trace.re = 1
  Y_trace : Y.trace.re = τ
  balance : X - Y = Z - T * Z * Tᴴ
  Y_slack : (Y * (H - 1)).trace.re = 0
  X_slack : (X * (τ • 1 - H)).trace.re = 0
  Z_slack : (Z * (H - Tᴴ * H * T)).trace.re = 0

structure EndpointFactors {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (κ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) where
  X : Matrix (Fin n) (Fin n) ℂ
  Y : Matrix (Fin n) (Fin n) ℂ
  Q : Matrix (Fin n) (Fin n) ℂ
  X_norm : ‖toHS X‖ = 1
  Y_norm : ‖toHS Y‖ = 1
  X_endpoint : CFC.sqrt H * X = κ • X
  Y_endpoint : CFC.sqrt H * Y = Y
  perpendicular : Xᴴ * Y = 0
  Q_positive : Q.PosSemidef
  balance : X * Xᴴ - Y * Yᴴ = Q -
    (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H)) * Q *
      (CFC.sqrt H * T * Ring.inverse (CFC.sqrt H))ᴴ

end CrouzeixHilbert.Endpoint

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.RationalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Transfer. -/

noncomputable section

open Set Filter

open scoped Topology Matrix Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Realization

section RationalMatrices

variable {n : ℕ}

def pencil (a : Coeff n) : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
  1 - (Polynomial.X : Polynomial ℂ) • a.map Polynomial.C

def transferDenominator (a : Coeff n) : Polynomial ℂ := (pencil a).det

def transferNumerator (a b c d : Coeff n) : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
  transferDenominator a • d.map Polynomial.C +
    (Polynomial.X : Polynomial ℂ) • (c.map Polynomial.C * (pencil a).adjugate * b.map Polynomial.C)

def transferRational (a b c d : Coeff n) : RationalMatrix n := fun i j =>
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (transferNumerator a b c d i j) /
    (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (transferDenominator a)

def entryMap (i j : Fin n) : Coeff n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

end RationalMatrices

namespace Colligation

variable {n : ℕ}

def rational (C : Colligation (EuclideanSpace ℂ (Fin n))) : RationalMatrix n :=
  transferRational ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.a) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.b)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.c) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm C.d)

end Colligation

section Transpose

variable {n : ℕ}

def conjugateVector (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => star (x.ofLp i))

namespace Colligation

def diskExtremal (C : Colligation (EuclideanSpace ℂ (Fin n))) : RationalMatrix n :=
  C.rationalᵀ

end Colligation

end Transpose

end CrouzeixHilbert.Realization

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Vectorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vectorization. -/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.L2Operator Kronecker InnerProductSpace MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Realization

def vectorization {n : ℕ} (X : Coeff n) : Amplification (EuclideanSpace ℂ (Fin n)) n :=
  ∑ j, ↑((Matrix.toEuclideanCLM (𝕜 := ℂ) X) (EuclideanSpace.basisFun (Fin n) ℂ j) ⊗ₜ[ℂ]
    (EuclideanSpace.basisFun (Fin n) ℂ j))

@[simp] theorem vectorization_coordinates {n : ℕ} (X : Coeff n) :
    matrixAmplificationCoordinates n n (vectorization X) = Boundary.toHS X := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [vectorization, map_sum, WithLp.ofLp_sum, Finset.sum_apply, matrixAmplificationCoordinates_tmul,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]
  simp [Boundary.toHS]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BlockPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block Polynomial. -/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker TensorProduct

namespace CrouzeixHilbert

def blockPolynomialEval {n m : ℕ} (D : Coeff n) :
    Matrix (Fin m) (Fin m) (Polynomial ℂ) →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun M i j := (Polynomial.aeval D (M i.2 j.2)) i.1 j.1
  map_zero' := by ext ⟨i,j⟩ ⟨k,l⟩; simp
  map_one' := by
    ext ⟨i,j⟩ ⟨k,l⟩
    change (Polynomial.aeval D (if j = l then 1 else 0)) i k =
      if (i,j) = (k,l) then 1 else 0
    by_cases h : j = l
    · subst l
      simp only [ite_true, map_one, Matrix.one_apply, Prod.mk.injEq, and_true]
    · simp only [h, ite_false, map_zero, Matrix.zero_apply, Prod.mk.injEq, and_false]
  map_add' M N := by
    ext ⟨i,j⟩ ⟨k,l⟩
    change (Polynomial.aeval D (M j l + N j l)) i k = _ + _
    rw [map_add]
    rfl
  map_mul' M N := by
    ext ⟨i,j⟩ ⟨k,l⟩
    change (Polynomial.aeval D (∑ h, M j h * N h l)) i k =
      ∑ h : Fin n × Fin m, (Polynomial.aeval D (M j h.2)) i h.1 *
        (Polynomial.aeval D (N h.2 l)) h.1 k
    simp only [map_sum, map_mul, Matrix.sum_apply, Matrix.mul_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]

@[simp] theorem blockPolynomialEval_apply {n m : ℕ} (D : Coeff n)
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (i k : Fin n) (j l : Fin m) :
    blockPolynomialEval D M (i,j) (k,l) = Polynomial.aeval D (M j l) i k := rfl

def rationalBaseMatrix {n : ℕ} (D : Coeff n) (r : RatFunc ℂ) : Coeff n :=
  Polynomial.aeval D r.num * Ring.inverse (Polynomial.aeval D r.denom)

def blockRationalEval {n m : ℕ} (D : Coeff n) (R : RationalMatrix m) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ i, ∑ j, rationalBaseMatrix D (R i j) ⊗ₖ Matrix.single i j 1

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Homotopy. -/

noncomputable section

open scoped InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def operatorHomotopy (A : Operator H) (a : ℂ) (s : ℝ) : Operator H :=
  algebraMap ℂ (Operator H) a + s • (A - algebraMap ℂ (Operator H) a)

@[simp] theorem operatorHomotopy_zero (A : Operator H) (a : ℂ) :
    operatorHomotopy A a 0 = algebraMap ℂ (Operator H) a := by simp [operatorHomotopy]

@[simp] theorem operatorHomotopy_one (A : Operator H) (a : ℂ) :
    operatorHomotopy A a 1 = A := by simp [operatorHomotopy]

def homotopyResolvent (A : Operator H) (a : ℂ) (s : ℝ) (z : ℂ) : Operator H :=
  Ring.inverse (algebraMap ℂ (Operator H) z - operatorHomotopy A a s)

def homotopyKernel (A : Operator H) (a : ℂ) (Γ : SmoothContour) (s t : ℝ) : Operator H :=
  deriv Γ.path t • (homotopyResolvent A a s (Γ.path t) *
    (A - algebraMap ℂ (Operator H) a) * homotopyResolvent A a s (Γ.path t))

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.MatrixContours
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix Contours. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance matrixContourOperatorRealNormedSpace_r6c72e2_1 (m : ℕ) :
    NormedSpace ℝ (Operator (Amplification H m)) :=
  NormedSpace.restrictScalars ℝ ℂ _
def tensorCoefficientCLM (A : Operator H) (m : ℕ) :
    Coeff m →L[ℂ] Operator (Amplification H m) := by
  let L : Coeff m →ₗ[ℂ] Operator (Amplification H m) :=
    { toFun := fun B => tensorOperator A B
      map_add' := by
        intro B C
        apply ContinuousLinearMap.ext
        intro v
        refine UniformSpace.Completion.induction_on v
          (isClosed_eq (tensorOperator A (B + C)).continuous
            ((tensorOperator A B).continuous.add (tensorOperator A C).continuous)) ?_
        intro a
        simp only [tensorOperator, map_add, TensorProduct.mapL_add_right,
          ContinuousLinearMap.completion_apply_coe, add_apply,
          UniformSpace.Completion.coe_add]
      map_smul' := by
        intro c B
        apply ContinuousLinearMap.ext
        intro v
        refine UniformSpace.Completion.induction_on v
          (isClosed_eq (tensorOperator A (c • B)).continuous
            ((tensorOperator A B).continuous.const_smul c)) ?_
        intro a
        simp only [tensorOperator, map_smul, TensorProduct.mapL_smul_right,
          ContinuousLinearMap.completion_apply_coe, smul_apply,
          UniformSpace.Completion.coe_smul, RingHom.id_apply] }
  exact L.mkContinuous ‖A‖ (fun B => norm_tensorOperator_le A B)

@[simp]
theorem tensorCoefficientCLM_apply (A : Operator H) {m : ℕ} (B : Coeff m) :
    tensorCoefficientCLM A m B = tensorOperator A B := rfl

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Compression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compression. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Compression

section Multiplication

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def fieldAction (L : α → E →L[ℂ] E) (hL : AEStronglyMeasurable L μ)
    (C : ℝ) (hC : 0 ≤ C) (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ C) :
    Lp E 2 μ →L[ℂ] Lp E 2 μ := by
  let mem : ∀ u : Lp E 2 μ, MemLp (fun t => L t (u t)) 2 μ := fun u =>
    ((Lp.memLp u).norm.const_mul C).mono
      ((show Continuous (fun z : (E →L[ℂ] E) × E => z.1 z.2) by fun_prop).comp_aestronglyMeasurable (hL.prodMk (Lp.aestronglyMeasurable u)))
      (hLn.mono fun t ht => by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC, abs_norm]
        exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _)))
  let M : Lp E 2 μ →ₗ[ℂ] Lp E 2 μ := {
    toFun u := (mem u).toLp _
    map_add' u v := by
      apply Lp.ext
      filter_upwards [(mem (u + v)).coeFn_toLp, (mem u).coeFn_toLp,
        (mem v).coeFn_toLp, Lp.coeFn_add u v,
        Lp.coeFn_add ((mem u).toLp _) ((mem v).toLp _)] with t huv hu hv ha hb
      simp only [huv, hb, hu, hv, ha, map_add, Pi.add_apply]
    map_smul' c u := by
      apply Lp.ext
      filter_upwards [(mem (c • u)).coeFn_toLp, (mem u).coeFn_toLp,
        Lp.coeFn_smul c u, Lp.coeFn_smul c ((mem u).toLp _)] with t hcu hu ha hb
      simp only [hcu, hb, hu, ha, map_smul, Pi.smul_apply, RingHom.id_apply] }
  apply M.mkContinuous C
  intro u
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(mem u).coeFn_toLp, hLn] with t ht hn
  change ‖((mem u).toLp _) t‖ ≤ C * ‖u t‖
  rw [ht]
  exact ((L t).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

end Multiplication

section Isometry

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def orbit (R : C(α, E →L[ℂ] E)) : E →ₗ[ℂ] C(α, E) where
  toFun x := ⟨fun t => R t x, R.continuous.clm_apply continuous_const⟩
  map_add' x y := by ext t; exact (R t).map_add x y
  map_smul' c x := by ext t; exact (R t).map_smul c x

def lift (R : C(α, E →L[ℂ] E)) : E →ₗ[ℂ] Lp E 2 μ :=
  (ContinuousMap.toLp 2 μ ℂ).toLinearMap.comp (orbit R)

omit [CompleteSpace E] in
theorem lift_apply_ae (R : C(α, E →L[ℂ] E)) (x : E) :
    lift (μ := μ) R x =ᵐ[μ] fun t => R t x :=
  ContinuousMap.coeFn_toLp μ (orbit R x)

theorem inner_lift (R : C(α, E →L[ℂ] E)) (x y : E) :
    ⟪lift (μ := μ) R x, lift (μ := μ) R y⟫_ℂ =
      ⟪x, (∫ t, star (R t) * R t ∂μ) y⟫_ℂ := by
  have hi : Integrable (fun t => star (R t) * R t) μ :=
    (R.continuous.star.mul R.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [L2.inner_def, ContinuousLinearMap.integral_apply hi,
    ← integral_inner (𝕜 := ℂ) (f := fun t => (star (R t) * R t) y)
      ((ContinuousLinearMap.apply ℂ E y).integrable_comp hi) x]
  apply integral_congr_ae
  filter_upwards [lift_apply_ae R x, lift_apply_ae R y] with t hx hy
  rw [hx, hy]
  exact (ContinuousLinearMap.adjoint_inner_right (R t) x (R t y)).symm

def isometry (R : C(α, E →L[ℂ] E)) (hmass : ∫ t, star (R t) * R t ∂μ = 1) :
    E →ₗᵢ[ℂ] Lp E 2 μ :=
  (lift R).isometryOfInner fun x y => by rw [inner_lift, hmass]; rfl

@[simp] theorem isometry_apply (R : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1) (x : E) :
    isometry R hmass x = lift R x := rfl

def densityRoot (Λ : C(α, E →L[ℂ] E)) (hΛ : ∀ t, 0 ≤ Λ t) : C(α, E →L[ℂ] E) :=
  ⟨fun t => CFC.sqrt (Λ t),
    CFC.continuousOn_sqrt.comp_continuous Λ.continuous (fun t => hΛ t)⟩

omit [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α] in
@[simp] theorem densityRoot_star_mul (Λ : C(α, E →L[ℂ] E)) (hΛ : ∀ t, 0 ≤ Λ t)
    (t : α) : star (densityRoot Λ hΛ t) * densityRoot Λ hΛ t = Λ t := by
  change star (CFC.sqrt (Λ t)) * CFC.sqrt (Λ t) = _
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq, CFC.sqrt_mul_sqrt_self _ (hΛ t)]

end Isometry

end CrouzeixHilbert.Compression

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Resolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent. -/

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

def diskDensity (D : Operator H) (ζ : ℂ) : Operator H :=
  Ring.inverse (1 - ζ⁻¹ • D) + star (Ring.inverse (1 - ζ⁻¹ • D)) - 1

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Calculus. -/

noncomputable section

open MeasureTheory

open scoped Topology

namespace CrouzeixHilbert.Disk

abbrev CircleSpace := AddCircle (1 : ℝ)

local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev σ : Measure CircleSpace := AddCircle.haarAddCircle

section Series

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
theorem inverse_one_sub_of_summable (a : A) (hs : Summable (fun n : ℕ => a ^ n)) :
    IsUnit (1 - a) ∧ Ring.inverse (1 - a) = ∑' n : ℕ, a ^ n := by
  let u : Aˣ := ⟨1 - a, ∑' n : ℕ, a ^ n, hs.one_sub_mul_tsum_pow, hs.tsum_pow_mul_one_sub⟩
  refine ⟨⟨u, rfl⟩, ?_⟩
  change Ring.inverse (u : A) = _
  rw [Ring.inverse_unit]
  rfl

lemma norm_fourier (n : ℤ) (t : CircleSpace) : ‖fourier n t‖ = 1 := Circle.norm_coe _

lemma fourier_one_pow (n : ℕ) (t : CircleSpace) :
    (fourier 1 t) ^ n = fourier (n : ℤ) t := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]

lemma inverse_fourier_pow (n : ℕ) (t : CircleSpace) :
    ((fourier 1 t)⁻¹) ^ n = fourier (-(n : ℤ)) t := by
  rw [Complex.inv_eq_conj (norm_fourier _ _), ← map_pow, fourier_one_pow, fourier_neg]

lemma summable_diskPowers (D : A) (hD : spectralRadius ℂ D < 1) (t : CircleSpace) :
    Summable (fun n : ℕ => ((fourier 1 t)⁻¹ • D) ^ n) := by
  apply (Metric.summable_norm_pow D hD).of_norm_bounded
  intro n
  simp only [smul_pow, norm_smul, norm_pow, norm_inv, norm_fourier,
    inv_one, one_pow, one_mul, le_refl]

lemma disk_inverse_series (D : A) (hD : spectralRadius ℂ D < 1) (t : CircleSpace) :
    Ring.inverse (1 - (fourier 1 t)⁻¹ • D) =
      ∑' n : ℕ, fourier (-(n : ℤ)) t • D ^ n := by
  rw [(inverse_one_sub_of_summable _ (summable_diskPowers D hD t)).2]
  simp only [smul_pow, inverse_fourier_pow]

lemma continuous_diskInverse (D : A) (hD : spectralRadius ℂ D < 1) :
    Continuous (fun t : CircleSpace => Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) := by
  simp_rw [disk_inverse_series D hD]
  refine continuous_tsum (fun n => (fourier _).continuous.smul continuous_const)
    (Metric.summable_norm_pow D hD) ?_
  intro n t
  simp only [norm_smul, norm_fourier, one_mul, le_refl]

end Series

section Density

variable {A : Type*} [CStarAlgebra A]

def phi (D : A) (t : CircleSpace) : A :=
  Ring.inverse (1 - (fourier 1 t)⁻¹ • D) +
    star (Ring.inverse (1 - (fourier 1 t)⁻¹ • D)) - 1

theorem continuous_phi (D : A) (hD : spectralRadius ℂ D < 1) : Continuous (phi D) :=
  ((continuous_diskInverse D hD).add (continuous_diskInverse D hD).star).sub continuous_const

end Density

end CrouzeixHilbert.Disk

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.TensorDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Density. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance tensorDensityOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

local instance tensorDensityOperatorCompleteSpace (size : ℕ) :
    CompleteSpace (Operator (Amplification H size)) := by
  let : ContinuousSMul ℂ (Amplification H size) := IsBoundedSMul.continuousSMul
  exact ContinuousLinearMap.instCompleteSpace

@[simp] theorem tensorOperator_one (m : ℕ) :
    tensorOperator (1 : Operator H) (1 : Coeff m) = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (tensorOperator 1 (1 : Coeff m)).continuous continuous_id) ?_
  intro v
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe, map_one]
  congr 1
  change TensorProduct.mapL (ContinuousLinearMap.id ℂ H)
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m))) v = v
  simp

variable [CompleteSpace H]

section PositiveDensity

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]

def amplifiedRoot (Λ : C(α, Operator H)) (hΛ : ∀ t, 0 ≤ Λ t) (m : ℕ) :
    C(α, Operator (Amplification H m)) :=
  ⟨fun t => tensorOperator (Compression.densityRoot Λ hΛ t) (1 : Coeff m),
    (tensorOperatorCLM (1 : Coeff m)).continuous.comp
      (Compression.densityRoot Λ hΛ).continuous⟩

def coefficientField {m : ℕ} (F : C(α, Coeff m)) :
    C(α, Operator (Amplification H m)) :=
  ⟨fun t => tensorOperator (1 : Operator H) (F t),
    (tensorCoefficientCLM (1 : Operator H) m).continuous.comp F.continuous⟩

end PositiveDensity

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DensityCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Density Compatibility. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Boundary

def toHSCLM (n : ℕ) : Coeff n →L[ℂ] HS n :=
  ({ toFun := toHS
     map_add' := fun _ _ => by apply PiLp.ext; intro ij; rfl
     map_smul' := fun _ _ => by apply PiLp.ext; intro ij; rfl } :
      Coeff n →ₗ[ℂ] HS n).toContinuousLinearMap

@[simp] theorem toHSCLM_apply {n : ℕ} (X : Coeff n) : toHSCLM n X = toHS X := rfl

def weightedPartialTraceCLM {n : ℕ} (X Y : Coeff n) : Coeff n →L[ℂ] Coeff n :=
  ({ toFun E := weightedPartialTrace E X Y
     map_add' E G := by simp [weightedPartialTrace, mul_add, add_mul]
     map_smul' c E := by simp [weightedPartialTrace] } :
      Coeff n →ₗ[ℂ] Coeff n).toContinuousLinearMap

@[simp] theorem weightedPartialTraceCLM_apply {n : ℕ} (E X Y : Coeff n) :
    weightedPartialTraceCLM X Y E = weightedPartialTrace E X Y := rfl

def densityContinuous {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) :
    C(CircleSpace, HS n) :=
  ⟨fun t => toHS (weightedPartialTrace (E t) X Y),
    (toHSCLM n).continuous.comp ((weightedPartialTraceCLM X Y).continuous.comp E.continuous)⟩

def densityLp {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) : BoundaryL2 n :=
  ContinuousMap.toLp 2 circleMeasure ℂ (densityContinuous E X Y)

end Boundary

open Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Fibers. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

attribute [local instance] tensorDensityOperatorCompleteSpace

def matrixOperatorMap (n : ℕ) : Coeff n →L[ℂ] Operator (EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap.toContinuousLinearMap

@[simp] theorem matrixOperatorMap_apply {n : ℕ} (A : Coeff n) :
    matrixOperatorMap n A = Matrix.toEuclideanCLM (𝕜 := ℂ) A := rfl

def matrixBaseField {n : ℕ} (L : C(CircleSpace, Coeff n)) :
    C(CircleSpace, Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)) :=
  ⟨fun t => tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n),
    (tensorOperatorCLM (1 : Coeff n)).continuous.comp
      ((matrixOperatorMap n).continuous.comp L.continuous)⟩

@[simp] theorem vectorization_inj {n : ℕ} {X Y : Coeff n} :
    vectorization X = vectorization Y ↔ X = Y := by
  constructor
  · intro h
    have he := congrArg (matrixAmplificationCoordinates n n) h
    rw [vectorization_coordinates, vectorization_coordinates] at he
    exact congrArg ofHS he
  · exact congrArg vectorization

end CrouzeixHilbert

namespace CrouzeixHilbert.Boundary

def matrixDensityRoot {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) : C(CircleSpace, Coeff n) :=
  ⟨fun t => CFC.sqrt (E t),
    CFC.continuousOn_sqrt.comp_continuous E.continuous (fun t => (hE t).nonneg)⟩

@[simp] theorem matrixDensityRoot_star_mul {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (t : CircleSpace) :
    (matrixDensityRoot E hE t)ᴴ * matrixDensityRoot E hE t = E t := by
  change star (CFC.sqrt (E t)) * CFC.sqrt (E t) = _
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,
    CFC.sqrt_mul_sqrt_self _ (hE t).nonneg]

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CauchyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cauchy Projection. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

section Tensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tensorBilinearCLM (m : ℕ) : Operator H →L[ℂ] Coeff m →L[ℂ] Operator (Amplification H m) := by
  let L : Operator H →ₗ[ℂ] Coeff m →L[ℂ] Operator (Amplification H m) := {
    toFun A := tensorCoefficientCLM A m
    map_add' A D := by
      ext B v
      exact congrArg (fun T : Operator (Amplification H m) => T v)
        ((tensorOperatorCLM B).map_add A D)
    map_smul' c A := by
      ext B v
      exact congrArg (fun T : Operator (Amplification H m) => T v)
        ((tensorOperatorCLM B).map_smul c A) }
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := Operator H) (F := Coeff m →L[ℂ] Operator (Amplification H m)) L 1 fun A => ?_
  rw [one_mul]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    (fun B => norm_tensorOperator_le A B)

@[simp] theorem tensorBilinearCLM_apply (m : ℕ) (A : Operator H) (B : Coeff m) :
    tensorBilinearCLM m A B = tensorOperator A B := rfl

end Tensor

namespace Boundary

def boundaryField {n : ℕ} (U : C(CircleSpace, Coeff n)) : BoundaryL2 n :=
  ContinuousMap.toLp 2 circleMeasure ℂ
    ⟨fun t => toHS (U t), (toHSCLM n).continuous.comp U.continuous⟩

def matrixLaurentMonomial {n : ℕ} (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    C(CircleSpace, Coeff n) :=
  ⟨fun t => (c * fourier a.1 t) • Matrix.single a.2.1 a.2.2 (1 : ℂ),
    (continuous_const.mul (fourier a.1).continuous).smul continuous_const⟩

end Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PolynomialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Approximation. -/

noncomputable section

open scoped Topology

open Set Filter Metric MeasureTheory

namespace CrouzeixHilbert

def compactCauchyKernel (K : Set ℂ) (w : ↥(Kᶜ)) : C(K, ℂ) :=
  ⟨fun z => ((w : ℂ) - z)⁻¹, (continuous_const.sub continuous_subtype_val).inv₀
    (by
      intro z he
      apply w.property
      rw [show (w : ℂ) = (z : ℂ) from sub_eq_zero.mp he]
      exact z.property)⟩

def compactCauchyKernelExtension (K : Set ℂ) (w : ℂ) : C(K, ℂ) := by
  classical
  exact if hw : w ∈ Kᶜ then compactCauchyKernel K ⟨w, hw⟩ else 0

@[simp]
theorem compactCauchyKernelExtension_apply {K : Set ℂ} {w : ℂ} (hw : w ∉ K) (z : K) :
    compactCauchyKernelExtension K w z = (w - z)⁻¹ := by
  classical
  unfold compactCauchyKernelExtension
  split
  · rfl
  · contradiction

open scoped Matrix.Norms.L2Operator

universe u

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Sharpness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A two-dimensional operator with sharp constant two. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def sharpOperator : Operator (EuclideanSpace ℂ (Fin 2)) :=
  (2 : ℂ) • InnerProductSpace.rankOne ℂ
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)

def sharpCoefficients : Fin 2 → Coeff 1 := ![0, 1]

@[simp]
theorem sharp_matrixPolynomial (z : ℂ) :
    matrixPolynomial (d := 1) sharpCoefficients z = z • (1 : Coeff 1) := by
  simp [matrixPolynomial, sharpCoefficients, Fin.sum_univ_two]

@[simp]
theorem sharp_polynomialEval : polynomialEval sharpOperator (d := 1) sharpCoefficients =
    tensorOperator sharpOperator (1 : Coeff 1) := by
  simp [polynomialEval, sharpCoefficients, Fin.sum_univ_two]

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskHolomorphic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Holomorphic. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance diskHolomorphicOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

section DensityIntegral

variable {α : Type v} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] (μ : Measure α) [IsFiniteMeasure μ]

def densityIntegralCLM (Λ : C(α, Operator H)) (m : ℕ) :
    C(α, Coeff m) →L[ℂ] Operator (Amplification H m) := by
  let : Module ℝ (Operator (Amplification H m)) :=
    (diskHolomorphicOperatorRealNormedSpace m).toModule
  let : SMulCommClass ℝ ℂ (Operator (Amplification H m)) :=
    IsScalarTower.to_smulCommClass
  have hc (F : C(α, Coeff m)) :
      Continuous (fun t => tensorOperator (Λ t) (F t)) :=
    ((tensorBilinearCLM m).continuous.comp Λ.continuous).clm_apply F.continuous
  have hi (F : C(α, Coeff m)) :
      Integrable (fun t => tensorOperator (Λ t) (F t)) μ :=
    (hc F).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : C(α, Coeff m) →ₗ[ℂ] Operator (Amplification H m) := {
    toFun F := ∫ t, tensorOperator (Λ t) (F t) ∂μ
    map_add' F G := by
      simp only [ContinuousMap.add_apply, ← tensorCoefficientCLM_apply, map_add]
      exact integral_add (hi F) (hi G)
    map_smul' c F := by
      simp only [ContinuousMap.smul_apply, ← tensorCoefficientCLM_apply, map_smul,
        integral_smul, RingHom.id_apply] }
  refine L.mkContinuous (‖Λ‖ * μ.real univ) fun F => ?_
  have hb : ∀ᵐ t ∂μ, ‖tensorOperator (Λ t) (F t)‖ ≤ ‖Λ‖ * ‖F‖ :=
    Eventually.of_forall fun t => (norm_tensorOperator_le _ _).trans
      (mul_le_mul (Λ.norm_coe_le_norm t) (F.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg _))
  exact (norm_integral_le_of_norm_le_const hb).trans_eq (by ring)

@[simp] theorem densityIntegralCLM_apply (Λ : C(α, Operator H)) {m : ℕ}
    (F : C(α, Coeff m)) :
    densityIntegralCLM μ Λ m F = ∫ t, tensorOperator (Λ t) (F t) ∂μ := rfl

end DensityIntegral

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CircleCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle Coordinate. -/

noncomputable section

open Set Metric Filter Topology Complex MeasureTheory

namespace CrouzeixHilbert.Boundary

local instance instFactLtRealOfNat_solutions_1 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def circleCoordinate : C(CircleSpace, ℂ) := fourier 1

@[simp] lemma norm_circleCoordinate (t : CircleSpace) : ‖circleCoordinate t‖ = 1 := by
  rw [circleCoordinate, fourier_apply, Circle.norm_coe]

lemma circleCoordinate_ne_zero (t : CircleSpace) : circleCoordinate t ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_circleCoordinate]; exact one_ne_zero)

lemma circleCoordinate_injective : Function.Injective circleCoordinate := by
  intro x y h
  apply AddCircle.injective_toCircle (T := 1) one_ne_zero
  apply Subtype.coe_injective
  simpa only [circleCoordinate, fourier_one] using h

@[simp] lemma circleCoordinate_neg (t : CircleSpace) :
    circleCoordinate (-t) = (circleCoordinate t)⁻¹ := by
  simp only [circleCoordinate, fourier_one, AddCircle.toCircle_neg, Circle.coe_inv]

lemma circleCoordinate_coe (x : ℝ) :
    circleCoordinate (x : CircleSpace) = circleMap 0 1 (2 * Real.pi * x) := by
  rw [circleCoordinate, fourier_coe_apply]
  simp only [Int.cast_one, mul_one, ofReal_one, div_one, circleMap, ofReal_mul,
    ofReal_ofNat, zero_add, one_mul]
  congr 1
  ring

lemma integral_circleCoordinate_eq_circleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ t, f (circleCoordinate t) ∂circleMeasure) = Real.circleAverage f 0 1 := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add, circleCoordinate_coe]
  rw [intervalIntegral.integral_comp_mul_left (fun θ => f (circleMap 0 1 θ)) (ne_of_gt Real.two_pi_pos)]
  simp only [mul_zero, mul_one, Real.circleAverage]

lemma integral_holomorphic_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    (∫ t, f (circleCoordinate t) ∂circleMeasure) = f 0 := by
  rw [integral_circleCoordinate_eq_circleAverage]
  apply DiffContOnCl.circleAverage
  apply DifferentiableOn.diffContOnCl
  simpa only [abs_one, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] using hf

lemma integral_holomorphic_inverse_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) :
    (∫ t, f (circleCoordinate t)⁻¹ ∂circleMeasure) = f 0 := by
  simp_rw [← circleCoordinate_neg]
  rw [integral_neg_eq_self (fun t => f (circleCoordinate t)) circleMeasure, integral_holomorphic_circleCoordinate hf]

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.SeparateHolomorphic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate Holomorphic. -/

noncomputable section

open Set Filter Metric Topology Function Complex MeasureTheory

open scoped Interval

namespace CrouzeixHilbert

lemma differentiableOn_parameter_intervalIntegral_pos {U : Set ℂ} (hU : IsOpen U)
    {T : ℝ} (hT : 0 < T) {f : ℂ → ℝ → ℂ}
    (hf : ContinuousOn (uncurry f) (U ×ˢ Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, DifferentiableOn ℂ (fun z => f z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..T, f z t) U := by
  have hmap : MapsTo (fun p : ℂ × ℝ => (p.1, T * p.2))
      (U ×ˢ Icc (0 : ℝ) 1) (U ×ˢ Icc 0 T) := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    exact ⟨hz, mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩
  have hi := differentiableOn_parameter_intervalIntegral hU
    (f := fun z t => f z (T * t))
    (hf.comp (f := fun p : ℂ × ℝ => (p.1, T * p.2)) (by fun_prop) hmap)
    (fun t ht => hd (T * t) ⟨mul_nonneg hT.le ht.1, by nlinarith [ht.2]⟩)
  have he (z : ℂ) : T • (∫ t in (0 : ℝ)..1, f z (T * t)) =
      ∫ t in (0 : ℝ)..T, f z t := by
    simpa only [mul_zero, mul_one] using intervalIntegral.smul_integral_comp_mul_left
      (f z) (a := 0) (b := 1) T
  exact (hi.const_smul T).congr (fun z _ => (he z).symm)

lemma deriv_eq_circle_parameter {U : Set ℂ} {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) {u : ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : closedBall u R ⊆ U) :
    deriv f u = (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((circleMap 0 R θ * I) / (circleMap 0 R θ) ^ 2) *
          f (u + circleMap 0 R θ) := by
  have he := (hd.mono hRU).deriv_eq_smul_circleIntegral hR
  have hn : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  calc
    deriv f u = (2 * (Real.pi : ℂ) * I)⁻¹ *
      (∮ w in C(u,R), (1 / (w-u)^2) • f w) := by
        rw [he, smul_eq_mul, inv_mul_cancel_left₀ hn]
    _ = _ := by
      congr 1
      simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      have hm : circleMap u R θ = u + circleMap 0 R θ := by simp [circleMap]
      dsimp only
      rw [hm, add_sub_cancel_left]
      ring

theorem continuousOn_first_derivative {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ → ℂ → ℂ} (hf : ContinuousOn (uncurry f) (U ×ˢ V))
    (hd : ∀ v ∈ V, DifferentiableOn ℂ (fun u => f u v) U) :
    ContinuousOn (fun p : ℂ × ℂ => deriv (fun u => f u p.2) p.1) (U ×ˢ V) := by
  rintro ⟨u,v⟩ ⟨hu,hv⟩
  obtain ⟨δ,hδ,hδU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hu)
  let R := δ / 3
  have hR : 0 < R := div_pos hδ (by norm_num)
  let P := ball u R ×ˢ V
  have hP : IsOpen P := isOpen_ball.prod hV
  have hp : (u,v) ∈ P := ⟨mem_ball_self hR,hv⟩
  have hshift (p : P) (θ : ℝ) : (p.1.1 + circleMap 0 R θ, p.1.2) ∈ U ×ˢ V := by
    refine ⟨hδU ?_,p.2.2⟩
    rw [mem_closedBall, dist_eq_norm]
    have hn := mem_ball.mp p.2.1
    rw [dist_eq_norm] at hn
    have hm : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    calc
      ‖p.1.1 + circleMap 0 R θ - u‖ = ‖(p.1.1-u) + circleMap 0 R θ‖ := by congr 1; ring
      _ ≤ ‖p.1.1-u‖ + ‖circleMap 0 R θ‖ := norm_add_le _ _
      _ ≤ δ := by rw [hm]; dsimp [R] at hn ⊢; linarith
  have hcoeff : Continuous (fun θ : ℝ => (circleMap 0 R θ * I) / (circleMap 0 R θ)^2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ
    exact pow_ne_zero _ (by
      apply norm_ne_zero_iff.mp
      rw [norm_circleMap_zero, abs_of_pos hR]
      exact hR.ne')
  have hfamily : Continuous (fun q : P × ℝ =>
      ((circleMap 0 R q.2 * I) / (circleMap 0 R q.2)^2) *
        f (q.1.1.1 + circleMap 0 R q.2) q.1.1.2) := by
    apply (hcoeff.comp continuous_snd).mul
    exact hf.comp_continuous (f := fun q : P × ℝ =>
      (q.1.1.1 + circleMap 0 R q.2, q.1.1.2)) (by fun_prop) (fun q => hshift q.1 q.2)
  have hc := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun (p : P) θ => ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
      f (p.1.1 + circleMap 0 R θ) p.1.2) hfamily 0 (2 * Real.pi)).const_mul (2 * (Real.pi : ℂ) * I)⁻¹
  have hc' : ContinuousOn (fun p : ℂ × ℂ => (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
          f (p.1 + circleMap 0 R θ) p.2) P :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  have he : EqOn (fun p : ℂ × ℂ => deriv (fun w => f w p.2) p.1)
      (fun p => (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
          f (p.1 + circleMap 0 R θ) p.2) P := by
    intro p hp
    apply deriv_eq_circle_parameter (hd _ hp.2) hR
    intro w hw
    apply hδU
    have hd1 := mem_ball.mp hp.1
    have hd2 := mem_closedBall.mp hw
    have hd3 := dist_triangle w p.1 u
    rw [mem_closedBall]
    dsimp [R] at hd1 hd2
    linarith
  exact ((hc'.congr he).continuousAt (hP.mem_nhds hp)).continuousWithinAt

theorem differentiableOn_second_first_derivative {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) {f : ℂ → ℂ → ℂ}
    (hf : ContinuousOn (uncurry f) (U ×ˢ V))
    (hd : ∀ v ∈ V, DifferentiableOn ℂ (fun u => f u v) U)
    (hv : ∀ u ∈ U, DifferentiableOn ℂ (f u) V) {u : ℂ} (hu : u ∈ U) :
    DifferentiableOn ℂ (fun v => deriv (fun w => f w v) u) V := by
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hu)
  have hshift (θ : ℝ) : u + circleMap 0 R θ ∈ U := by
    apply hRU
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      norm_circleMap_zero, abs_of_pos hR]
  have hcoeff : Continuous (fun θ : ℝ => (circleMap 0 R θ * I) / (circleMap 0 R θ)^2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ
    apply pow_ne_zero
    apply norm_ne_zero_iff.mp
    rw [norm_circleMap_zero, abs_of_pos hR]
    exact hR.ne'
  have hfamily : ContinuousOn (fun q : ℂ × ℝ =>
      ((circleMap 0 R q.2 * I) / (circleMap 0 R q.2)^2) *
        f (u + circleMap 0 R q.2) q.1) (V ×ˢ Icc 0 (2*Real.pi)) := by
    apply (hcoeff.comp continuous_snd).continuousOn.mul
    exact hf.comp (f := fun q : ℂ × ℝ => (u + circleMap 0 R q.2, q.1))
      (by fun_prop) (fun q hq => ⟨hshift q.2,hq.1⟩)
  have hh := differentiableOn_parameter_intervalIntegral_pos hV Real.two_pi_pos
    (f := fun v θ => ((circleMap 0 R θ * I) / (circleMap 0 R θ)^2) *
      f (u + circleMap 0 R θ) v) hfamily
    (fun θ _ => (hv _ (hshift θ)).const_mul _)
  exact (hh.const_mul (2 * (Real.pi : ℂ) * I)⁻¹).congr
    (fun v hv => deriv_eq_circle_parameter (hd v hv) hR hRU)

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CircleAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle Analytic. -/

noncomputable section

open Set Metric Filter Topology Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Boundary

local instance circleAnalyticFactZeroLtOne : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma integral_circleMeasure_eq_interval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : CircleSpace → E) :
    (∫ t, f t ∂circleMeasure) = ∫ t in (0 : ℝ)..1, f (t : CircleSpace) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage 1 0]
  simp only [inv_one, one_smul, zero_add]

lemma differentiableOn_parameter_circleIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {V : Set ℂ} (hV : IsOpen V)
    {f : ℂ → CircleSpace → E}
    (hf : ContinuousOn (Function.uncurry f) (V ×ˢ univ))
    (hd : ∀ t, DifferentiableOn ℂ (fun z => f z t) V) :
    DifferentiableOn ℂ (fun z => ∫ t, f z t ∂circleMeasure) V := by
  simp_rw [integral_circleMeasure_eq_interval]
  apply differentiableOn_parameter_intervalIntegral hV
  · exact hf.comp (f := fun p : ℂ × ℝ => (p.1,(p.2 : CircleSpace)))
      (continuous_fst.prodMk ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  · exact fun t _ => hd (t : CircleSpace)

@[simp] lemma circleCoordinate_pow (n : ℕ) (t : CircleSpace) :
    (circleCoordinate t)^n = fourier (n : ℤ) t := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]; rfl

@[simp] lemma circleCoordinate_inverse_pow (n : ℕ) (t : CircleSpace) :
    ((circleCoordinate t)⁻¹)^n = fourier (-(n : ℤ)) t := by
  rw [Complex.inv_eq_conj (norm_circleCoordinate t), ← map_pow, circleCoordinate_pow, fourier_neg]

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DiskBoundaryChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

def localCayley (z : ℂ) : ℂ := (I - z) / (I + z)

@[simp] theorem localCayley_zero : localCayley 0 = 1 := by simp [localCayley]

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorRiemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Riemann. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

def invertedExterior (K : Set ℂ) (a : ℂ) : Set ℂ :=
  {z | z = 0 ∨ a + z⁻¹ ∉ K}

@[simp] theorem zero_mem_invertedExterior (K : Set ℂ) (a : ℂ) :
    0 ∈ invertedExterior K a := Or.inl rfl

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

def inversionChart (a : ℂ) : OpenPartialHomeomorph ℂ ℂ where
  toFun z := a + z⁻¹
  invFun z := (z - a)⁻¹
  source := {z | z ≠ 0}
  target := {z | z ≠ a}
  map_source' z hz := by
    change a + z⁻¹ ≠ a
    simpa only [ne_eq, add_eq_left, inv_eq_zero] using (show z ≠ 0 from hz)
  map_target' z hz := inv_ne_zero (sub_ne_zero.mpr hz)
  left_inv' z _ := by simp only [add_sub_cancel_left, inv_inv]
  right_inv' z _ := by simp only [inv_inv, add_sub_cancel]
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl
  continuousOn_toFun z hz := (continuousAt_const.add (continuousAt_inv₀ hz)).continuousWithinAt
  continuousOn_invFun z hz := ((continuousAt_id.sub continuousAt_const).inv₀
    (sub_ne_zero.mpr hz)).continuousWithinAt

structure ExteriorCollar (U : Set ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  G : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ G {t | radius < ‖t‖}
  injective : InjOn G {t | radius < ‖t‖}
  outside : BijOn G {t | 1 < ‖t‖} (closure U)ᶜ
  boundary : BijOn G (sphere 0 1) (frontier U)
  inside : MapsTo G {t | radius < ‖t‖ ∧ ‖t‖ < 1} U
  leading : ℂ
  leading_ne_zero : leading ≠ 0
  regular : ℂ → ℂ
  regular_analytic : AnalyticOnNhd ℂ regular (ball 0 radius⁻¹)
  laurent : ∀ t, radius < ‖t‖ → G t = leading * t + regular t⁻¹

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Normal. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate

open scoped InnerProductSpace

namespace CrouzeixHilbert.Conformal

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma parameter_open : IsOpen {t : ℂ | C.radius < ‖t‖} := isOpen_lt continuous_const continuous_norm

lemma deriv_ne_zero {t : ℂ} (ht : C.radius < ‖t‖) : deriv C.G t ≠ 0 :=
  deriv_ne_zero_of_injOn C.parameter_open C.analytic.differentiableOn C.injective ht

theorem supporting_normal (hc : Convex ℝ U) {t : ℂ} (ht : ‖t‖ = 1)
    {z : ℂ} (hz : z ∈ closure U) :
    0 ≤ (conj (t * deriv C.G t) * (C.G t - z)).re := by
  have htC : C.radius < ‖t‖ := ht ▸ C.radius_lt_one
  have hdn := C.deriv_ne_zero htC
  let d := (C.analytic t htC).hasStrictDerivAt.hasStrictFDerivAt_equiv hdn
  let e := (d.toOpenPartialHomeomorph C.G).restrOpen {t : ℂ | C.radius < ‖t‖} C.parameter_open
  have heC : e.source ⊆ {t : ℂ | C.radius < ‖t‖} := inter_subset_right
  have het : t ∈ e.source := ⟨d.mem_toOpenPartialHomeomorph_source, htC⟩
  have heG : (e : ℂ → ℂ) = C.G := rfl
  have hegt : C.G t ∈ e.target := e.map_source het
  have hei : e.symm (C.G t) = t := e.left_inv het
  have hp : C.G t ∈ closure U := (C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr ht)).1
  have hemax : IsLocalMaxOn (fun w : ℂ => ‖e.symm w‖ ^ 2) (closure U) (C.G t) := by
    filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds hegt),
      self_mem_nhdsWithin] with w hw hwU
    rw [hei, ht, one_pow]
    have hwsmall : ‖e.symm w‖ ≤ 1 := by
      by_contra hn
      have houtside := C.outside.mapsTo (lt_of_not_ge hn)
      have heq : C.G (e.symm w) = w := e.right_inv hw
      exact houtside (heq.symm ▸ hwU)
    nlinarith [norm_nonneg (e.symm w)]
  have heder : HasDerivAt e.symm (deriv C.G t)⁻¹ (C.G t) :=
    e.hasDerivAt_symm hegt hdn (by rw [hei, heG]; exact (C.analytic t htC).differentiableAt.hasDerivAt)
  have hdir := hemax.hasFDerivWithinAt_nonpos
    (heder.hasFDerivAt.restrictScalars ℝ).norm_sq.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hc.closure.segment_subset hp hz))
  simp only [ContinuousLinearMap.comp_apply, smul_apply] at hdir
  simp only [innerSL_apply_apply] at hdir
  rw [hei, real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hdir
  simp only [two_smul] at hdir
  change (((z - C.G t) * (deriv C.G t)⁻¹) * conj t).re +
    (((z - C.G t) * (deriv C.G t)⁻¹) * conj t).re ≤ 0 at hdir
  have halg : (((z - C.G t) * (deriv C.G t)⁻¹) * conj t).re =
      - (conj (t * deriv C.G t) * (C.G t - z)).re / Complex.normSq (deriv C.G t) := by
    rw [Complex.inv_def]
    simp only [map_mul, div_eq_mul_inv, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
    ring
  rw [halg] at hdir
  have hpos := Complex.normSq_pos.mpr hdn
  have hle : - (conj (t * deriv C.G t) * (C.G t - z)).re /
      Complex.normSq (deriv C.G t) ≤ 0 := by linarith
  exact neg_nonpos.mp (by simpa only [zero_mul] using (div_le_iff₀ hpos).mp hle)

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Kernel. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

abbrev reciprocalDisk : Set ℂ := ball 0 C.radius⁻¹

lemma inverse_mem_reciprocalDisk {t : ℂ} (ht : C.radius < ‖t‖) :
    t⁻¹ ∈ C.reciprocalDisk := by
  rw [mem_ball_zero_iff, norm_inv]
  exact (inv_lt_inv₀ (C.radius_pos.trans ht) C.radius_pos).mpr ht

lemma inverse_mem_parameter {u : ℂ} (hu : u ∈ C.reciprocalDisk) (hu0 : u ≠ 0) :
    C.radius < ‖u⁻¹‖ := by
  rw [norm_inv]
  exact (lt_inv_comm₀ C.radius_pos (norm_pos_iff.mpr hu0)).mpr (mem_ball_zero_iff.mp hu)

lemma deriv_laurent {t : ℂ} (ht : C.radius < ‖t‖) :
    deriv C.G t = C.leading - (t⁻¹)^2 * deriv C.regular t⁻¹ := by
  have ht0 : t ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  have hd := ((hasDerivAt_id t).const_mul C.leading).add
    ((C.regular_analytic _ (C.inverse_mem_reciprocalDisk ht)).differentiableAt.hasDerivAt.comp t
      (hasDerivAt_inv ht0))
  have he : C.G =ᶠ[𝓝 t] (fun t => C.leading * t + C.regular t⁻¹) := by
    filter_upwards [C.parameter_open.mem_nhds ht] with w hw
    exact C.laurent w hw
  dsimp only [id_eq, Pi.add_apply, comp_apply] at hd
  rw [he.deriv_eq]
  exact hd.deriv.trans (by rw [inv_pow]; ring)

def dividedDenominator (u v : ℂ) : ℂ :=
  C.leading - u * v * dslope C.regular v u

lemma continuousOn_dividedDenominator :
    ContinuousOn (uncurry C.dividedDenominator) (C.reciprocalDisk ×ˢ C.reciprocalDisk) := by
  have hd := continuousOn_dslope_pair isOpen_ball C.regular_analytic.differentiableOn
  apply continuousOn_const.sub
  apply (continuous_fst.mul continuous_snd).continuousOn.mul
  exact hd.comp (f := Prod.swap) continuous_swap.continuousOn (fun _ h => ⟨h.2,h.1⟩)

lemma differentiableOn_dividedDenominator_left {v : ℂ} (hv : v ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (fun u => C.dividedDenominator u v) C.reciprocalDisk := by
  apply (differentiableOn_const _).sub
  apply (differentiableOn_id.mul_const v).mul
  exact (differentiableOn_dslope (isOpen_ball.mem_nhds hv)).mpr C.regular_analytic.differentiableOn

lemma differentiableOn_dividedDenominator_right {u : ℂ} (hu : u ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (C.dividedDenominator u) C.reciprocalDisk := by
  have hd : DifferentiableOn ℂ (fun v => dslope C.regular v u) C.reciprocalDisk := by
    exact ((differentiableOn_dslope (isOpen_ball.mem_nhds hu)).mpr
      C.regular_analytic.differentiableOn).congr (fun v _ => dslope_swap C.regular v u)
  exact (differentiableOn_const _).sub ((differentiableOn_id.const_mul u).mul hd)

lemma dividedDenominator_eq {u v : ℂ} (hu : u ∈ C.reciprocalDisk) (hv : v ∈ C.reciprocalDisk)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    C.dividedDenominator u v = (C.G u⁻¹ - C.G v⁻¹) / (u⁻¹-v⁻¹) := by
  rw [C.laurent _ (C.inverse_mem_parameter hu hu0), C.laurent _ (C.inverse_mem_parameter hv hv0)]
  simp only [dividedDenominator, inv_inv, dslope_of_ne _ huv, slope_def_field]
  field_simp
  ring

lemma dividedDenominator_diag {u : ℂ} (hu : u ∈ C.reciprocalDisk) (hu0 : u ≠ 0) :
    C.dividedDenominator u u = deriv C.G u⁻¹ := by
  rw [C.deriv_laurent (C.inverse_mem_parameter hu hu0), inv_inv]
  simp only [dividedDenominator, dslope_same]
  ring

lemma dividedDenominator_ne_zero {u v : ℂ} (hu : u ∈ C.reciprocalDisk)
    (hv : v ∈ C.reciprocalDisk) : C.dividedDenominator u v ≠ 0 := by
  by_cases hu0 : u = 0
  · simpa only [dividedDenominator, hu0, zero_mul, sub_zero] using C.leading_ne_zero
  by_cases hv0 : v = 0
  · simpa only [dividedDenominator, hv0, mul_zero, zero_mul, sub_zero] using C.leading_ne_zero
  by_cases huv : u = v
  · subst v
    rw [C.dividedDenominator_diag hu hu0]
    exact C.deriv_ne_zero (C.inverse_mem_parameter hu hu0)
  rw [C.dividedDenominator_eq hu hv hu0 hv0 huv]
  apply div_ne_zero
  · intro he
    exact huv (inv_injective (C.injective (C.inverse_mem_parameter hu hu0)
      (C.inverse_mem_parameter hv hv0) (sub_eq_zero.mp he)))
  · exact sub_ne_zero.mpr (fun he => huv (inv_injective he))

def correction (u v : ℂ) : ℂ :=
  -u * deriv (fun z => C.dividedDenominator z v) u / C.dividedDenominator u v

lemma continuousOn_correction :
    ContinuousOn (uncurry C.correction) (C.reciprocalDisk ×ˢ C.reciprocalDisk) := by
  apply ContinuousOn.div
  · apply continuous_fst.neg.continuousOn.mul
    exact continuousOn_first_derivative isOpen_ball isOpen_ball C.continuousOn_dividedDenominator
      (fun _ hv => C.differentiableOn_dividedDenominator_left hv)
  · exact C.continuousOn_dividedDenominator
  · exact fun _ h => C.dividedDenominator_ne_zero h.1 h.2

lemma differentiableOn_correction_left {v : ℂ} (hv : v ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (fun u => C.correction u v) C.reciprocalDisk :=
  (differentiableOn_id.neg.mul
    ((C.differentiableOn_dividedDenominator_left hv).deriv isOpen_ball)).div
    (C.differentiableOn_dividedDenominator_left hv) (fun _ hu => C.dividedDenominator_ne_zero hu hv)

lemma differentiableOn_correction_right {u : ℂ} (hu : u ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (C.correction u) C.reciprocalDisk := by
  apply DifferentiableOn.div
  · apply DifferentiableOn.const_mul
    exact differentiableOn_second_first_derivative isOpen_ball isOpen_ball
      C.continuousOn_dividedDenominator
      (fun _ hv => C.differentiableOn_dividedDenominator_left hv)
      (fun _ hu => C.differentiableOn_dividedDenominator_right hu) hu
  · exact C.differentiableOn_dividedDenominator_right hu
  · exact fun _ hv => C.dividedDenominator_ne_zero hu hv

@[simp] lemma correction_zero_left (v : ℂ) : C.correction 0 v = 0 := by
  simp only [correction, neg_zero, zero_mul, zero_div]

@[simp] lemma correction_zero_right (u : ℂ) : C.correction u 0 = 0 := by
  simp only [correction, dividedDenominator, mul_zero, zero_mul, sub_zero,
    deriv_const, mul_zero, zero_div]

lemma correction_eq {t w : ℂ} (ht : C.radius < ‖t‖) (hw : C.radius < ‖w‖)
    (htw : t ≠ w) :
    C.correction t⁻¹ w⁻¹ = t * deriv C.G t / (C.G t - C.G w) - t / (t-w) := by
  have ht0 : t ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans hw)
  have hg : C.G t - C.G w ≠ 0 := sub_ne_zero.mpr (fun he => htw (C.injective ht hw he))
  have htw' : t-w ≠ 0 := sub_ne_zero.mpr htw
  have hQ := C.dividedDenominator_eq (C.inverse_mem_reciprocalDisk ht)
    (C.inverse_mem_reciprocalDisk hw) (inv_ne_zero ht0) (inv_ne_zero hw0)
    (fun he => htw (inv_injective he))
  simp only [inv_inv] at hQ
  have hdQ := ((C.differentiableOn_dividedDenominator_left
    (C.inverse_mem_reciprocalDisk hw)).differentiableAt
      (isOpen_ball.mem_nhds (C.inverse_mem_reciprocalDisk ht))).hasDerivAt.comp t
        (hasDerivAt_inv ht0)
  have hdG := ((C.analytic t ht).differentiableAt.hasDerivAt.sub_const (C.G w)).div
    ((hasDerivAt_id t).sub_const w) htw'
  have he : (fun z => C.dividedDenominator z⁻¹ w⁻¹) =ᶠ[𝓝 t]
      (fun z => (C.G z - C.G w)/(z-w)) := by
    filter_upwards [C.parameter_open.mem_nhds ht, eventually_ne_nhds htw] with z hz hzw
    have hz0 : z ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans hz)
    simpa only [inv_inv] using C.dividedDenominator_eq (C.inverse_mem_reciprocalDisk hz)
      (C.inverse_mem_reciprocalDisk hw) (inv_ne_zero hz0) (inv_ne_zero hw0)
      (fun he => hzw (inv_injective he))
  dsimp only [Function.comp_apply, id_eq] at hdQ hdG
  have hd := (hdQ.congr_of_eventuallyEq he.symm).unique hdG
  dsimp only [correction]
  rw [hQ]
  field_simp at hd ⊢
  exact hd

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Kernel. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma closed_unit_subset_reciprocalDisk : closedBall (0 : ℂ) 1 ⊆ C.reciprocalDisk := by
  intro z hz
  rw [mem_ball_zero_iff]
  exact (mem_closedBall_zero_iff.mp hz).trans_lt
    ((one_lt_inv₀ C.radius_pos).mpr C.radius_lt_one)

lemma circle_inverse_mem (t : CircleSpace) : (circleCoordinate t)⁻¹ ∈ C.reciprocalDisk :=
  C.inverse_mem_reciprocalDisk (by rw [norm_circleCoordinate]; exact C.radius_lt_one)

def boundaryCorrection : C(CircleSpace × CircleSpace, ℂ) where
  toFun p := C.correction (circleCoordinate p.2)⁻¹ (circleCoordinate p.1)⁻¹
  continuous_toFun := C.continuousOn_correction.comp_continuous
    (((circleCoordinate.continuous.comp continuous_snd).inv₀
      (fun p => circleCoordinate_ne_zero p.2)).prodMk
      ((circleCoordinate.continuous.comp continuous_fst).inv₀
        (fun p => circleCoordinate_ne_zero p.1)))
    (fun p => ⟨C.circle_inverse_mem p.2, C.circle_inverse_mem p.1⟩)

def boundaryKernel : CircleKernel where
  toFun p := 1 + 2 * (C.boundaryCorrection p).re
  continuous_toFun := continuous_const.add
    (continuous_const.mul (continuous_re.comp C.boundaryCorrection.continuous))

lemma circle_real_quotient {t w : ℂ} (ht : ‖t‖ = 1) (hw : ‖w‖ = 1) (hne : t ≠ w) :
    2 * (t/(t-w)).re = 1 := by
  have hn : normSq (t-w) ≠ 0 := normSq_eq_zero.not.mpr (sub_ne_zero.mpr hne)
  have hts : t.re * t.re + t.im * t.im = 1 := by
    rw [← normSq_apply, normSq_eq_norm_sq, ht, one_pow]
  have hws : w.re * w.re + w.im * w.im = 1 := by
    rw [← normSq_apply, normSq_eq_norm_sq, hw, one_pow]
  rw [div_re, ← add_div]
  field_simp
  simp only [normSq_apply, sub_re, sub_im]
  nlinarith

lemma boundaryKernel_off_diagonal (hc : Convex ℝ U) {w t : CircleSpace} (hnt : t ≠ w) :
    0 ≤ C.boundaryKernel (w,t) := by
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  have hw : C.radius < ‖circleCoordinate w‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  have htw : circleCoordinate t ≠ circleCoordinate w := fun he => hnt (circleCoordinate_injective he)
  have hn := C.supporting_normal hc (norm_circleCoordinate t)
    (C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr (norm_circleCoordinate w))).1
  have hq : 0 ≤ (circleCoordinate t * deriv C.G (circleCoordinate t) /
      (C.G (circleCoordinate t) - C.G (circleCoordinate w))).re := by
    rw [div_re, ← add_div]
    apply div_nonneg _ (normSq_nonneg _)
    simpa only [mul_re, conj_re, conj_im, sub_neg_eq_add, neg_mul] using hn
  change 0 ≤ 1 + 2 * (C.correction _ _).re
  rw [C.correction_eq ht hw htw, sub_re]
  have he := circle_real_quotient (norm_circleCoordinate t) (norm_circleCoordinate w) htw
  linarith

lemma boundaryKernel_nonnegative (hc : Convex ℝ U) (p : CircleSpace × CircleSpace) :
    0 ≤ C.boundaryKernel p := by
  let : Nontrivial Circle := ⟨⟨1, -1, by
    intro h
    have h' := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at h'⟩⟩
  let : Nontrivial CircleSpace := (AddCircle.homeomorphCircle (T := 1) one_ne_zero).surjective.nontrivial
  apply (dense_compl_singleton p.1).induction (P := fun t => 0 ≤ C.boundaryKernel (p.1,t))
    (fun t ht => C.boundaryKernel_off_diagonal hc (by simpa using ht))
    (isClosed_le continuous_const
      (C.boundaryKernel.continuous.comp (continuous_const.prodMk continuous_id))) p.2

lemma boundaryCorrection_integral_right (w : CircleSpace) :
    (∫ t, C.boundaryCorrection (w,t) ∂circleMeasure) = 0 := by
  change (∫ t, C.correction (circleCoordinate t)⁻¹ (circleCoordinate w)⁻¹ ∂circleMeasure) = 0
  rw [integral_holomorphic_inverse_circleCoordinate
    ((C.differentiableOn_correction_left (C.circle_inverse_mem w)).mono C.closed_unit_subset_reciprocalDisk)]
  exact C.correction_zero_left _

lemma boundaryCorrection_integral_left (t : CircleSpace) :
    (∫ w, C.boundaryCorrection (w,t) ∂circleMeasure) = 0 := by
  change (∫ w, C.correction (circleCoordinate t)⁻¹ (circleCoordinate w)⁻¹ ∂circleMeasure) = 0
  rw [integral_holomorphic_inverse_circleCoordinate
    ((C.differentiableOn_correction_right (C.circle_inverse_mem t)).mono C.closed_unit_subset_reciprocalDisk)]
  exact C.correction_zero_right _

lemma boundaryKernel_integral_right (w : CircleSpace) :
    (∫ t, C.boundaryKernel (w,t) ∂circleMeasure) = 1 := by
  have hi : Integrable (fun t => C.boundaryCorrection (w,t)) circleMeasure :=
    (C.boundaryCorrection.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ t, 1 + 2 * (C.boundaryCorrection (w,t)).re ∂circleMeasure) = 1
  have hr : Integrable (fun t => (C.boundaryCorrection (w,t)).re) circleMeasure := hi.re
  rw [integral_add (integrable_const (1 : ℝ)) (hr.const_mul 2), integral_const_mul, show (∫ t, (C.boundaryCorrection (w,t)).re ∂circleMeasure) =
      (∫ t, C.boundaryCorrection (w,t) ∂circleMeasure).re from Complex.reCLM.integral_comp_comm hi,
    C.boundaryCorrection_integral_right, zero_re, mul_zero, add_zero, integral_const]
  simp

lemma boundaryKernel_integral_left (t : CircleSpace) :
    (∫ w, C.boundaryKernel (w,t) ∂circleMeasure) = 1 := by
  have hi : Integrable (fun w => C.boundaryCorrection (w,t)) circleMeasure :=
    (C.boundaryCorrection.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ w, 1 + 2 * (C.boundaryCorrection (w,t)).re ∂circleMeasure) = 1
  have hr : Integrable (fun w => (C.boundaryCorrection (w,t)).re) circleMeasure := hi.re
  rw [integral_add (integrable_const (1 : ℝ)) (hr.const_mul 2), integral_const_mul, show (∫ w, (C.boundaryCorrection (w,t)).re ∂circleMeasure) =
      (∫ w, C.boundaryCorrection (w,t) ∂circleMeasure).re from Complex.reCLM.integral_comp_comm hi,
    C.boundaryCorrection_integral_left, zero_re, mul_zero, add_zero, integral_const]
  simp

def boundaryOperator (hc : Convex ℝ U) (k : ℕ) : BoundaryL2 k →L[ℝ] BoundaryL2 k :=
  kernelOperator C.boundaryKernel (C.boundaryKernel_nonnegative hc)
    C.boundaryKernel_integral_right C.boundaryKernel_integral_left

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Contour. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

def boundaryMap : C(CircleSpace, ℂ) where
  toFun t := C.G (circleCoordinate t)
  continuous_toFun := C.analytic.continuousOn.comp_continuous circleCoordinate.continuous
    (fun t => by change C.radius < ‖circleCoordinate t‖; rw [norm_circleCoordinate]; exact C.radius_lt_one)

def boundaryNormal : C(CircleSpace, ℂ) where
  toFun t := circleCoordinate t * deriv C.G (circleCoordinate t)
  continuous_toFun := circleCoordinate.continuous.mul
    (C.analytic.deriv.continuousOn.comp_continuous circleCoordinate.continuous
      (fun t => by change C.radius < ‖circleCoordinate t‖; rw [norm_circleCoordinate]; exact C.radius_lt_one))

lemma boundaryMap_mem_frontier (t : CircleSpace) : C.boundaryMap t ∈ frontier U :=
  C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr (norm_circleCoordinate t))

def boundaryContour : SmoothContour where
  path t := C.G (unitCirclePath t)
  smooth := (C.analytic.contDiffOn C.parameter_open.uniqueDiffOn |>.restrict_scalars ℝ).comp_contDiff
    unitCirclePath_smooth (fun t => by change C.radius < ‖unitCirclePath t‖; rw [unitCirclePath_norm]; exact C.radius_lt_one)
  closed := by rw [unitCirclePath_closed]

def reciprocalDenominator (z u : ℂ) : ℂ := C.leading + u * (C.regular u - z)

def reciprocalCauchy (z u : ℂ) : ℂ :=
  (C.leading - u^2 * deriv C.regular u) / C.reciprocalDenominator z u

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Faber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faber. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma twice_coordinate_mem (t : CircleSpace) : C.radius < ‖2 * circleCoordinate t‖ := by
  rw [norm_mul, norm_circleCoordinate, mul_one, norm_ofNat]
  exact C.radius_lt_one.trans (by norm_num)

def outerMap : C(CircleSpace, ℂ) :=
  ⟨fun t => C.G (2 * circleCoordinate t),
    C.analytic.continuousOn.comp_continuous
      (continuous_const.mul circleCoordinate.continuous) C.twice_coordinate_mem⟩

def outerDomain : Set ℂ := (range C.outerMap)ᶜ

lemma isOpen_outerDomain : IsOpen C.outerDomain :=
  (isCompact_range C.outerMap.continuous).isClosed.isOpen_compl

lemma closure_subset_outerDomain : closure U ⊆ C.outerDomain := by
  rintro z hz ⟨t, rfl⟩
  exact C.outside.mapsTo (by
    change 1 < ‖2 * circleCoordinate t‖
    rw [norm_mul, norm_ofNat, norm_circleCoordinate, mul_one]
    norm_num) hz

lemma outer_difference_ne_zero {z : ℂ} (hz : z ∈ C.outerDomain) (t : CircleSpace) :
    C.G (2 * circleCoordinate t) - z ≠ 0 := by
  intro he
  exact hz ⟨t, sub_eq_zero.mp he⟩

def physicalCoefficient (j : ℤ) (z : ℂ) : ℂ :=
  ∫ t, (2 * circleCoordinate t)^j *
    ((2 * circleCoordinate t * deriv C.G (2 * circleCoordinate t)) /
      (C.G (2 * circleCoordinate t) - z)) ∂circleMeasure

lemma differentiableOn_physicalCoefficient (j : ℤ) :
    DifferentiableOn ℂ (C.physicalCoefficient j) C.outerDomain := by
  have hq : Continuous (fun t : CircleSpace =>
      2 * circleCoordinate t * deriv C.G (2 * circleCoordinate t)) :=
    (continuous_const.mul circleCoordinate.continuous).mul
      (C.analytic.deriv.continuousOn.comp_continuous
        (continuous_const.mul circleCoordinate.continuous) C.twice_coordinate_mem)
  apply differentiableOn_parameter_circleIntegral C.isOpen_outerDomain
  · exact ((continuous_const.mul (circleCoordinate.continuous.comp continuous_snd)).continuousOn.zpow₀ j
        (fun p _ => Or.inl (mul_ne_zero (by norm_num) (circleCoordinate_ne_zero p.2)))).mul
      ((hq.comp continuous_snd).continuousOn.div
        ((C.outerMap.continuous.comp continuous_snd).sub continuous_fst).continuousOn
        (fun p hp => C.outer_difference_ne_zero hp.1 p.2))
  · intro t
    exact (differentiableOn_const _).mul
      ((differentiableOn_const _).div ((differentiableOn_const _).sub differentiableOn_id)
        (fun z hz => C.outer_difference_ne_zero hz t))

def correctionMoment (j : ℕ) (v : ℂ) : ℂ :=
  ∫ t, (circleCoordinate t)^j * C.correction (circleCoordinate t)⁻¹ v ∂circleMeasure

lemma continuousOn_correctionMoment_integrand (j : ℕ) :
    ContinuousOn (Function.uncurry (fun v (t : CircleSpace) =>
      (circleCoordinate t)^j * C.correction (circleCoordinate t)⁻¹ v))
      (C.reciprocalDisk ×ˢ univ) := by
  apply ContinuousOn.mul
  · exact ((circleCoordinate.continuous.comp continuous_snd).pow j).continuousOn
  · have hc : Continuous (fun p : ℂ × CircleSpace => ((circleCoordinate p.2)⁻¹,p.1)) :=
      ((circleCoordinate.continuous.comp continuous_snd).inv₀
        (fun p => circleCoordinate_ne_zero p.2)).prodMk continuous_fst
    have hi : MapsTo (fun p : ℂ × CircleSpace => ((circleCoordinate p.2)⁻¹,p.1))
        (C.reciprocalDisk ×ˢ univ) (C.reciprocalDisk ×ˢ C.reciprocalDisk) :=
      fun p hp => ⟨C.circle_inverse_mem p.2, hp.1⟩
    exact C.continuousOn_correction.comp
      (f := fun p : ℂ × CircleSpace => ((circleCoordinate p.2)⁻¹,p.1)) hc.continuousOn hi

lemma differentiableOn_correctionMoment_integrand (j : ℕ) (t : CircleSpace) :
    DifferentiableOn ℂ (fun v =>
      (circleCoordinate t)^j * C.correction (circleCoordinate t)⁻¹ v) C.reciprocalDisk := by
  exact (C.differentiableOn_correction_right (C.circle_inverse_mem t)).const_mul _

lemma differentiableOn_correctionMoment (j : ℕ) :
    DifferentiableOn ℂ (C.correctionMoment j) C.reciprocalDisk := by
  unfold correctionMoment
  apply differentiableOn_parameter_circleIntegral (E := ℂ) isOpen_ball
  · exact C.continuousOn_correctionMoment_integrand j
  · exact C.differentiableOn_correctionMoment_integrand j

@[simp] lemma correctionMoment_zero (j : ℕ) : C.correctionMoment j 0 = 0 := by
  simp [correctionMoment]

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Fourier. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma correctionMoment_continuous_trace (j : ℕ) :
    Continuous (fun w : CircleSpace => C.correctionMoment j (circleCoordinate w)⁻¹) :=
  (C.differentiableOn_correctionMoment j).continuousOn.comp_continuous
    (circleCoordinate.continuous.inv₀ circleCoordinate_ne_zero) C.circle_inverse_mem

def scalarChannel {k : ℕ} (i l : Fin k) (f : C(CircleSpace, ℂ)) : C(CircleSpace, Coeff k) :=
  ⟨fun t => f t • Matrix.single i l (1 : ℂ), f.continuous.smul continuous_const⟩

def correctionChannel {k : ℕ} (a : ℕ × (Fin k × Fin k)) : C(CircleSpace, Coeff k) :=
  scalarChannel a.2.1 a.2.2
    ⟨fun t => C.correctionMoment a.1 (circleCoordinate t)⁻¹, C.correctionMoment_continuous_trace a.1⟩

def physicalChannel {k : ℕ} (a : ℤ × (Fin k × Fin k)) : C(CircleSpace, Coeff k) :=
  scalarChannel a.2.1 a.2.2
    ⟨fun t => C.physicalCoefficient a.1 (C.boundaryMap t),
      (C.differentiableOn_physicalCoefficient a.1).continuousOn.comp_continuous
        C.boundaryMap.continuous (fun t => C.closure_subset_outerDomain
          (C.boundaryMap_mem_frontier t).1)⟩

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Projection. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

def boundaryFieldCLM (k : ℕ) : C(CircleSpace, Coeff k) →L[ℂ] BoundaryL2 k :=
  (ContinuousMap.toLp 2 circleMeasure ℂ).comp
    (ContinuousLinearMap.compLeftContinuous ℂ CircleSpace (toHSCLM k))

@[simp] lemma boundaryFieldCLM_apply {k : ℕ} (F : C(CircleSpace, Coeff k)) :
    boundaryFieldCLM k F = boundaryField F := rfl

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

def physicalPolynomial (p : Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j * C.physicalCoefficient (j : ℤ) z

lemma differentiableOn_physicalPolynomial (p : Polynomial ℂ) :
    DifferentiableOn ℂ (C.physicalPolynomial p) C.outerDomain := by
  exact DifferentiableOn.fun_sum (fun j _ =>
    (C.differentiableOn_physicalCoefficient (j : ℤ)).const_mul (p.coeff j))

def polynomialCircle (p : Polynomial ℂ) : C(CircleSpace, ℂ) :=
  ⟨fun t => p.eval (circleCoordinate t), p.continuous.comp circleCoordinate.continuous⟩

def physicalPolynomialTrace (p : Polynomial ℂ) : C(CircleSpace, ℂ) :=
  ⟨fun t => C.physicalPolynomial p (C.boundaryMap t),
    (C.differentiableOn_physicalPolynomial p).continuousOn.comp_continuous
      C.boundaryMap.continuous (fun t => C.closure_subset_outerDomain (C.boundaryMap_mem_frontier t).1)⟩

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Module. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

def analyticTrace {V : Set ℂ} (hUV : closure U ⊆ V) (f : ℂ → ℂ)
    (hf : ContinuousOn f V) : C(CircleSpace, ℂ) :=
  ⟨fun t => f (C.boundaryMap t), hf.comp_continuous C.boundaryMap.continuous
    (fun t => hUV (C.boundaryMap_mem_frontier t).1)⟩

def matrixAnalyticTrace {V : Set ℂ} (hUV : closure U ⊆ V) {k : ℕ} (f : ℂ → Coeff k)
    (hf : ContinuousOn f V) : C(CircleSpace, Coeff k) :=
  ⟨fun t => f (C.boundaryMap t), hf.comp_continuous C.boundaryMap.continuous
    (fun t => hUV (C.boundaryMap_mem_frontier t).1)⟩

def physicalRepresentative {k : ℕ} (a : ℤ × (Fin k × Fin k)) (c : ℂ) (z : ℂ) : Coeff k :=
  (c * C.physicalCoefficient a.1 z) • Matrix.single a.2.1 a.2.2 1

lemma physicalRepresentative_holomorphic {k : ℕ} (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    EntrywiseHolomorphic C.outerDomain (C.physicalRepresentative a c) := by
  intro i j
  exact ((C.differentiableOn_physicalCoefficient a.1).const_mul c).mul_const _

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Transport. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

def interiorBoundary : C(CircleSpace, ℂ) :=
  C.analyticTrace R.closure_subset_domain R.f R.analytic_f.continuousOn

lemma norm_interiorBoundary (t : CircleSpace) : ‖C.interiorBoundary R t‖ = 1 :=
  R.boundary_norm _ (C.boundaryMap_mem_frontier t)

def angularJacobian : C(CircleSpace, ℂ) :=
  ⟨fun t => C.boundaryNormal t * deriv R.f (C.boundaryMap t) / C.interiorBoundary R t,
    (C.boundaryNormal.continuous.mul (R.analytic_f.deriv.continuousOn.comp_continuous
      C.boundaryMap.continuous (fun t => R.closure_subset_domain (C.boundaryMap_mem_frontier t).1))).div
      (C.interiorBoundary R).continuous
      (fun t => norm_ne_zero_iff.mp (by rw [C.norm_interiorBoundary]; exact one_ne_zero))⟩

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Measure. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

local instance instFactLtRealOfNat_solutions : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

def interiorAngle : C(CircleSpace, CircleSpace) :=
  ⟨fun t => (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm
    ⟨C.interiorBoundary R t, by exact mem_sphere_zero_iff_norm.mpr (C.norm_interiorBoundary R t)⟩,
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.continuous.comp
      ((C.interiorBoundary R).continuous.subtype_mk _)⟩

def angularIntegralCLM : C(CircleSpace, ℂ) →L[ℂ] ℂ := by
  have hi (f : C(CircleSpace, ℂ)) : Integrable
      (fun t => C.angularJacobian R t * f (C.interiorAngle R t)) circleMeasure :=
    ((C.angularJacobian R).continuous.mul (f.continuous.comp (C.interiorAngle R).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let L : C(CircleSpace, ℂ) →ₗ[ℂ] ℂ := {
    toFun f := ∫ t, C.angularJacobian R t * f (C.interiorAngle R t) ∂circleMeasure
    map_add' f g := by
      simp only [ContinuousMap.add_apply, mul_add]
      exact integral_add (hi f) (hi g)
    map_smul' c f := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      simp_rw [mul_left_comm _ c, ← smul_eq_mul c]
      exact integral_smul c _ }
  refine L.mkContinuous ‖C.angularJacobian R‖ fun f => ?_
  have hb : ∀ᵐ t ∂circleMeasure, ‖C.angularJacobian R t * f (C.interiorAngle R t)‖ ≤
      ‖C.angularJacobian R‖ * ‖f‖ := Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_mul ((C.angularJacobian R).norm_coe_le_norm t)
      (f.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, probReal_univ, one_mul, mul_one] using norm_integral_le_of_norm_le_const hb

def circleIntegralCLM : C(CircleSpace, ℂ) →L[ℂ] ℂ := by
  let L : C(CircleSpace, ℂ) →ₗ[ℂ] ℂ := {
    toFun f := ∫ t, f t ∂circleMeasure
    map_add' f g := integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    map_smul' c f := integral_smul c _ }
  refine L.mkContinuous 1 fun f => ?_
  simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, probReal_univ, one_mul, mul_one] using norm_integral_le_of_norm_le_const
    (Eventually.of_forall f.norm_coe_le_norm : ∀ᵐ t ∂circleMeasure, ‖f t‖ ≤ ‖f‖)

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.SimilarityRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Similarity Representation. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Boundary

def boundaryStar {n : ℕ} (U : C(CircleSpace, Coeff n)) : C(CircleSpace, Coeff n) :=
  ⟨fun t => (U t)ᴴ, U.continuous.star⟩

@[simp] theorem boundaryStar_apply {n : ℕ} (U : C(CircleSpace, Coeff n)) (t : CircleSpace) :
    boundaryStar U t = (U t)ᴴ := rfl

def tensorIntegral {n : ℕ} (E U : C(CircleSpace, Coeff n)) :
    Operator (Amplification (EuclideanSpace ℂ (Fin n)) n) :=
  ∫ t, tensorOperator (matrixOperatorMap n (E t)) (U t) ∂circleMeasure

def reflectedBoundaryCauchy {n : ℕ} (M : BoundaryL2 n →L[ℝ] BoundaryL2 n) :
    BoundaryL2 n →L[ℝ] BoundaryL2 n :=
  lpStar.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundaryCauchy M).comp lpStar.toContinuousLinearEquiv.toContinuousLinearMap)

end Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Density. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance physicalDensityOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

def operatorDensity (D : Operator H) (hD : spectralRadius ℂ D < 1) : C(CircleSpace, Operator H) :=
  ⟨fun t => C.angularJacobian R t • Disk.phi D (C.interiorAngle R t),
    (C.angularJacobian R).continuous.smul ((Disk.continuous_phi D hD).comp (C.interiorAngle R).continuous)⟩

end Conformal.ExteriorCollar

def operatorToMatrix (n : ℕ) : Operator (EuclideanSpace ℂ (Fin n)) →L[ℂ] Coeff n :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma operatorToMatrix_apply {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n))) :
    operatorToMatrix n A = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm A := rfl

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

def matrixDensity {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) : C(CircleSpace, Coeff n) :=
  ⟨fun t => operatorToMatrix n (C.operatorDensity R D hD t),
    (operatorToMatrix n).continuous.comp (C.operatorDensity R D hD).continuous⟩

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Calculus. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

def pullbackDomain (V : Set ℂ) : Set ℂ := ball 0 R.radius ∩ R.h ⁻¹' V

def diskTrace {V : Set ℂ} (hUV : closure U ⊆ V) {m : ℕ} (F : ℂ → Coeff m)
    (hF : ContinuousOn F V) : C(CircleSpace, Coeff m) :=
  ⟨fun t => F (R.h (circleCoordinate t)),
    hF.comp_continuous
      (R.analytic_h.continuousOn.comp_continuous circleCoordinate.continuous
        (fun t => R.closedDisk_subset (mem_closedBall_zero_iff.mpr (norm_circleCoordinate t).le)))
      (fun t => hUV (R.closed_h.mapsTo (mem_closedBall_zero_iff.mpr (norm_circleCoordinate t).le)))⟩

end Conformal.InteriorCollar

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance physicalCalculusOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma boundaryMap_not_mem (hU : IsOpen U) (t : CircleSpace) : C.boundaryMap t ∉ U :=
  fun ht => (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ ht)

def operatorResolvent (A : Operator H) (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) :
    C(CircleSpace, Operator H) :=
  ⟨fun t => C.boundaryNormal t • Ring.inverse (algebraMap ℂ (Operator H) (C.boundaryMap t) - A),
    C.boundaryNormal.continuous.smul ((continuousOn_resolvent A).comp_continuous C.boundaryMap.continuous
      (fun t ht => C.boundaryMap_not_mem hU t (hKU ht)))⟩

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U)

def matrixResolvent : C(CircleSpace, Coeff n) :=
  ⟨fun t => operatorToMatrix n (C.operatorResolvent A hKU hU t),
    (operatorToMatrix n).continuous.comp (C.operatorResolvent A hKU hU).continuous⟩

@[simp] lemma matrixResolvent_operator (t : CircleSpace) :
    matrixOperatorMap n (C.matrixResolvent A hKU hU t) = C.operatorResolvent A hKU hU t := by
  simp only [matrixResolvent, ContinuousMap.coe_mk, matrixOperatorMap_apply,
    operatorToMatrix_apply, StarAlgEquiv.apply_symm_apply]

def matrixResolventDensity : C(CircleSpace, Coeff n) :=
  C.matrixResolvent A hKU hU + boundaryStar (C.matrixResolvent A hKU hU)

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end


