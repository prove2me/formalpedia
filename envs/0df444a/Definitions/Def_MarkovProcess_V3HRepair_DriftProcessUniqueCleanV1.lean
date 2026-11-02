-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_DriftProcessUniqueCleanV1
-- name    : MarkovProcess_V3HRepair_DriftProcessUniqueCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:17:44.853217+00:00
-- url     : https://prove2.me/theorems/d7729af0-076b-46aa-934b-7b314e19f88c
-- title:
--   Verified MarkovProcess source repair: DriftProcessUniqueCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess DriftProcessUniqueCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.DriftProcessUniqueCleanV1 source SHA-256 a4a0e7dc5ff598c28733374bfced5fbddfe483feb93ac439d3da6f9c5c60f6d6. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 50337e8a-b875-456d-a98e-f4ea8a8e2bd8; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Examples_Drift_f1e2d4e2
import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentIntrinsicUniqueAliasCleanV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]


section Feller
theorem hasContinuousC0Orbits_driftSemigroup (v : E) :
    (driftSemigroup v).HasContinuousC0Orbits (mapsC0_driftSemigroup v) := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hf⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  have hv : (0 : ℝ) < ‖v‖ + 1 := by positivity
  refine ⟨delta / (‖v‖ + 1), div_pos hdelta hv, fun a hab ↦ ?_⟩
  have hab' : |(a : ℝ) - (b : ℝ)| < delta / (‖v‖ + 1) := by
    rw [← NNReal.dist_eq]
    exact hab
  have hkey : ∀ x : E, dist (f (x + (a : ℝ) • v)) (f (x + (b : ℝ) • v)) ≤ eps / 2 := by
    intro x
    refine le_of_lt (hf ?_)
    have hsub : (x + (a : ℝ) • v) - (x + (b : ℝ) • v) = ((a : ℝ) - (b : ℝ)) • v := by
      rw [sub_smul]
      abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc |(a : ℝ) - (b : ℝ)| * ‖v‖ ≤ |(a : ℝ) - (b : ℝ)| * (‖v‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith only []) (abs_nonneg _)
      _ < delta / (‖v‖ + 1) * (‖v‖ + 1) := mul_lt_mul_of_pos_right hab' hv
      _ = delta := div_mul_cancel₀ delta (ne_of_gt hv)
  have hle : dist ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) a f)
      ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) b f) ≤ eps / 2 := by
    rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
    refine (BoundedContinuousFunction.dist_le (le_of_lt (half_pos heps))).2 fun x ↦ ?_
    show dist ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) a f x)
      ((driftSemigroup v).c0Operator (mapsC0_driftSemigroup v) b f x) ≤ eps / 2
    rw [SubMarkovKernelSemigroup.c0Operator_apply, SubMarkovKernelSemigroup.c0Operator_apply,
      kernelIntegral_driftSemigroup_apply, kernelIntegral_driftSemigroup_apply]
    exact hkey x
  linarith only [hle, heps]

/-- The drift semigroup is a Feller semigroup. -/
theorem isFellerKernelSemigroup_driftSemigroup (v : E) :
    (driftSemigroup v).IsFellerKernelSemigroup :=
  ⟨mapsC0_driftSemigroup v, hasContinuousC0Orbits_driftSemigroup v⟩

end Feller

section Moments

/-- The drift semigroup satisfies the Kolmogorov moment criterion with `p = q = 2` and constant
`‖v‖²`: the displacement over time `h` is exactly `h ‖v‖`. -/
theorem hasKolmogorovMoments_driftSemigroup (v : E) :
    (driftSemigroup v).HasKolmogorovMoments 2 2 (‖v‖₊ ^ 2) := by
  refine ⟨two_pos, one_lt_two, fun h y ↦ ?_⟩
  have hmeas : Measurable (fun z : E ↦ edist z y ^ (2 : ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 2
  have hnn : nndist (y + (h : ℝ) • v) y = h * ‖v‖₊ := by
    rw [nndist_eq_nnnorm, add_sub_cancel_left, nnnorm_smul]
    congr 1
    apply NNReal.coe_injective
    rw [coe_nnnorm, Real.norm_of_nonneg h.coe_nonneg]
  rw [driftSemigroup_apply, lintegral_dirac' _ hmeas, edist_nndist, hnn,
    ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.coe_mul, mul_pow, ENNReal.coe_pow]
  exact le_of_eq (mul_comm _ _)

end Moments

section Process

/-- The drift semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_driftSemigroup (v : E) :
    (driftSemigroup v).KolmogorovRegular (isConservative_driftSemigroup v) :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    (isConservative_driftSemigroup v) (hasKolmogorovMoments_driftSemigroup v)

/-- **The main theorem, applied to the drift semigroup.**  There is exactly one Markov kernel
from the state space to continuous paths whose finite-dimensional distributions are those of the
deterministic drift with velocity `v`. -/
theorem existsUnique_continuousProcess_driftSemigroup (v : E) :
    ∃! Q : Kernel E (ContinuousPath E), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (driftSemigroup v) I :=
  (isFellerKernelSemigroup_driftSemigroup v).existsUnique_continuousProcess_of_hasKolmogorovMoments
    (driftSemigroup v) (isConservative_driftSemigroup v) (hasKolmogorovMoments_driftSemigroup v)


end Process
end
end MarkovProcess

#print axioms MarkovProcess.existsUnique_continuousProcess_driftSemigroup

noncomputable def MarkovProcess.V3HRepairProof_50337e8ab875456da98ef4ea8a8e2bd8 :=
  @MarkovProcess.existsUnique_continuousProcess_driftSemigroup


