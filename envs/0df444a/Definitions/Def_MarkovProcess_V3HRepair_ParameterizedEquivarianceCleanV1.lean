-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ParameterizedEquivarianceCleanV1
-- name    : MarkovProcess_V3HRepair_ParameterizedEquivarianceCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:31:27.746018+00:00
-- url     : https://prove2.me/theorems/1541bb52-d91f-4f5b-8a73-d958a2a6b786
-- title:
--   Verified MarkovProcess source repair: ParameterizedEquivarianceCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess ParameterizedEquivarianceCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ParameterizedEquivarianceCleanV1 source SHA-256 4a2f016b998070337045d9587f3594a093043fc434faf9f2bcef09506036ab8f. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 7e6cc3f7-46ee-4612-8468-4782c0f190bb, d856dbd5-d986-4df9-86f6-2c44394ea752, 7854f349-2b55-4f3e-8d25-114c85b0e877; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Parameterized_Equivariance_252d78e3
import Definitions.Def_MarkovProcess_V3HRepair_TrajectoryEquivarianceCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FiniteKernelEquivarianceCleanV2
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Measurability

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [TopologicalSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]

namespace IsRescaledConjugate

variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}

omit [BorelSpace alpha] [BorelSpace beta] in
/-- The fibre form of the relation: at every parameter the corresponding slices of `P` and `P'`
are rescaled conjugates in the sense of `SubMarkovKernelSemigroup.IsRescaledConjugate`. -/
theorem fibre (h : IsRescaledConjugate P P' g e c) (theta : Theta) :
    SubMarkovKernelSemigroup.IsRescaledConjugate (P.toSubMarkovKernelSemigroup (g theta))
      (P'.toSubMarkovKernelSemigroup theta) e c :=
  fun t x ↦ h theta t x

/-- Fibrewise conservativity transfers across rescaled conjugacy. -/
theorem isConservative (h : IsRescaledConjugate P P' g e c) (hP : P.IsConservative) :
    P'.IsConservative :=
  fun theta ↦ (h.fibre theta).isConservative (hP (g theta))

end IsRescaledConjugate

end Measurability

section ParameterizedMomentBridge
variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
/-- Fibrewise Kolmogorov moment bounds imply fibrewise Kolmogorov regularity. -/
theorem KolmogorovRegular.of_hasKolmogorovMoments {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P.KolmogorovRegular hP :=
  fun theta ↦ SubMarkovKernelSemigroup.IsConservative.kolmogorovRegular_of_hasKolmogorovMoments
    (P.toSubMarkovKernelSemigroup theta) (hP theta) (hmom theta)
end ParameterizedMomentBridge

section Moments

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [PseudoEMetricSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]
variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}

/-- **Fibrewise transfer of the Kolmogorov moment criterion.**  If the state map is an isometry,
the parameter-uniform displacement bound of `P` passes to its rescaled conjugate `P'` with the
constant multiplied by `c ^ q`, uniformly in the parameter. -/
theorem IsRescaledConjugate.hasKolmogorovMoments
    (h : IsRescaledConjugate P P' g e c) (he : Isometry (e : alpha → beta)) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) : P'.HasKolmogorovMoments p q (M * c ^ q) :=
  fun theta ↦ (h.fibre theta).hasKolmogorovMoments he (hmom (g theta))

end Moments

section ContinuousProcess

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha] [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
  (P' : ParameterizedSubMarkovKernelSemigroup Theta beta)
  (hP : P.IsConservative) (hP' : P'.IsConservative)

/-- **Equivariance of the parameterized continuous-path process.**  If the fibre of `P'` at every
parameter `theta` is the fibre of `P` at `g theta` conjugated by `e` and sped up by `c`, then the
quenched continuous-path process of `P'` is the quenched process of `P`, pulled back along
`(theta, x) ↦ (g theta, e.symm x)` and pushed forward by `ContinuousPath.rescale e c`.

Joint measurability in the parameter and the starting state is carried by the kernel structure on
both sides; the Feller hypothesis is needed only for `P`. -/
theorem IsConservative.continuousProcess_eq_map_rescale
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (hK' : P'.KolmogorovRegular hP')
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' g e c) :
    IsConservative.continuousProcess P' hP' =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × beta ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c) := by
  refine Kernel.ext fun p ↦ ?_
  obtain ⟨theta, x⟩ := p
  rw [IsConservative.continuousProcess_apply,
    Kernel.map_apply _ (ContinuousPath.measurable_rescale e c), Kernel.comap_apply,
    IsConservative.continuousProcess_apply]
  exact SubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale
    (P.toSubMarkovKernelSemigroup (g theta)) (hP (g theta))
    (P'.toSubMarkovKernelSemigroup theta) (hP' theta) (hFeller (g theta)) (hK (g theta))
    (hK' theta) hc (h.fibre theta) x

/-- The parameterized equivariance identity at a fixed parameter and starting state. -/
theorem IsConservative.continuousProcess_apply_rescale
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (hK' : P'.KolmogorovRegular hP')
    {g : Theta → Theta} {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' g e c) (theta : Theta) (x : beta) :
    IsConservative.continuousProcess P' hP' (theta, x) =
      (IsConservative.continuousProcess P hP (g theta, e.symm x)).map
        (ContinuousPath.rescale e c) := by
  rw [IsConservative.continuousProcess_apply, IsConservative.continuousProcess_apply]
  exact SubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale
    (P.toSubMarkovKernelSemigroup (g theta)) (hP (g theta))
    (P'.toSubMarkovKernelSemigroup theta) (hP' theta) (hFeller (g theta)) (hK (g theta))
    (hK' theta) hc (h.fibre theta) x

/-- **Intrinsic form of the parameterized equivariance theorem.**  When the state map is an
isometry, a parameter-uniform Kolmogorov moment bound on `P` alone supplies the fibrewise
regularity of both families. -/
theorem IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M)
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ beta}
    (he : Isometry (e : alpha → beta)) {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' g e c) :
    IsConservative.continuousProcess P' hP' =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × beta ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c) :=
  IsConservative.continuousProcess_eq_map_rescale P P' hP hP' hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
    (KolmogorovRegular.of_hasKolmogorovMoments P' hP' (h.hasKolmogorovMoments he hmom)) hg hc h

/-- **Covariance.**  A parameterized family that is its own rescaled conjugate along `(g, e, c)`
has a quenched continuous-path process invariant under the corresponding transformation of the
parameter, the starting state and the path.  Stationarity and re-gauging covariance of a random
environment are the case `c = 1`, with `g` the environment shift and `e` the matching spatial
translation. -/
theorem IsConservative.continuousProcess_covariant
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP)
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ alpha} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P g e c) :
    IsConservative.continuousProcess P hP =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × alpha ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c) :=
  IsConservative.continuousProcess_eq_map_rescale P P hP hP hFeller hK hK hg hc h

end ContinuousProcess

end

end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale
#print axioms MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale
#print axioms MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments
#print axioms MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_covariant

noncomputable def MarkovProcess.V3HRepairProof_7e6cc3f746ee461284684782c0f190bb :=
  @MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale

noncomputable def MarkovProcess.V3HRepairProof_d856dbd5d9864df986f62c44394ea752 :=
  @MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_covariant

noncomputable def MarkovProcess.V3HRepairProof_7854f3492b554f3e8d25114c85b0e877 :=
  @MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments


