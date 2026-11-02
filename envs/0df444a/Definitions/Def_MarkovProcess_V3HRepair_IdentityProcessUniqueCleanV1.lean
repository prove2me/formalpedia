-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_IdentityProcessUniqueCleanV1
-- name    : MarkovProcess_V3HRepair_IdentityProcessUniqueCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:17:22.044187+00:00
-- url     : https://prove2.me/theorems/ea4209b6-e37c-42fd-9d64-7c2d020b8b8a
-- title:
--   Verified MarkovProcess source repair: IdentityProcessUniqueCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess IdentityProcessUniqueCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.IdentityProcessUniqueCleanV1 source SHA-256 00da8fb11e69bedb12ad0d02144252061880c9d3195b65ddd4434756292ab2a4. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 8df303b1-9526-41a6-9d33-e26695721191; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Examples_Identity_d8db12c8
import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentIntrinsicUniqueAliasCleanV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

section Feller

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- Integrating a `C₀` function against the identity semigroup returns the function itself. -/
theorem kernelIntegral_idSemigroup (t : NNReal) (f : C₀(alpha, ℝ)) :
    kernelIntegral ((idSemigroup (alpha := alpha)) t) f = f := by
  funext x
  rw [kernelIntegral, idSemigroup_apply t x]
  exact integral_dirac' (f : alpha → ℝ) x f.continuous.stronglyMeasurable

/-- The identity semigroup maps `C₀` into itself. -/
theorem mapsC0_idSemigroup : (idSemigroup (alpha := alpha)).MapsC0 := by
  intro t f
  rw [kernelIntegral_idSemigroup t f]
  exact ⟨f.continuous, f.zero_at_infty'⟩

variable [LocallyCompactSpace alpha]

/-- The identity semigroup is a Feller semigroup: its `C₀` operators are all the identity, so
they map `C₀` into itself and have constant, hence continuous, time orbits. -/
theorem isFellerKernelSemigroup_idSemigroup :
    (idSemigroup (alpha := alpha)).IsFellerKernelSemigroup := by
  refine ⟨mapsC0_idSemigroup, fun f ↦ ?_⟩
  have hconst : (fun _ : NNReal ↦ (idSemigroup (alpha := alpha)).c0Operator
      mapsC0_idSemigroup 0 f) =
      fun t : NNReal ↦ (idSemigroup (alpha := alpha)).c0Operator mapsC0_idSemigroup t f := by
    funext t
    apply ZeroAtInftyContinuousMap.ext
    intro x
    rw [SubMarkovKernelSemigroup.c0Operator_apply,
      SubMarkovKernelSemigroup.c0Operator_apply,
      kernelIntegral_idSemigroup t f, kernelIntegral_idSemigroup 0 f]
  rw [← hconst]
  exact continuous_const

end Feller

section Moments

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The identity semigroup satisfies the Kolmogorov moment criterion with `p = 1`, `q = 2` and
vanishing constant: the displacement over any time is identically zero. -/
theorem hasKolmogorovMoments_idSemigroup :
    (idSemigroup (alpha := alpha)).HasKolmogorovMoments 1 2 0 := by
  refine ⟨one_pos, one_lt_two, fun h y ↦ ?_⟩
  have hmeas : Measurable (fun z : alpha ↦ edist z y ^ (1 : ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 1
  rw [idSemigroup_apply h y, lintegral_dirac' y hmeas, edist_self,
    ENNReal.zero_rpow_of_pos one_pos, ENNReal.coe_zero, zero_mul]

end Moments

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [Nonempty alpha]

omit [LocallyCompactSpace alpha] in
/-- The identity semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_idSemigroup :
    (idSemigroup (alpha := alpha)).KolmogorovRegular isConservative_idSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_idSemigroup hasKolmogorovMoments_idSemigroup

/-- **The main theorem, applied to the identity semigroup.**  There is exactly one Markov kernel
from the state space to continuous paths whose finite-dimensional distributions are those of the
identity semigroup.  In particular the hypotheses of
`SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments`
are jointly satisfiable. -/
theorem existsUnique_continuousProcess_idSemigroup :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (idSemigroup (alpha := alpha)) I :=
  isFellerKernelSemigroup_idSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    (idSemigroup (alpha := alpha)) isConservative_idSemigroup hasKolmogorovMoments_idSemigroup


end Process
end
end MarkovProcess

#print axioms MarkovProcess.existsUnique_continuousProcess_idSemigroup

noncomputable def MarkovProcess.V3HRepairProof_8df303b1952641a69d33e26695721191 :=
  @MarkovProcess.existsUnique_continuousProcess_idSemigroup


