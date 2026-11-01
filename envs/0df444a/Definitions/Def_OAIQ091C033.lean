-- Prove2me | Definitions.Def_OAIQ091C033
-- name    : OAIQ091C033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:05:04.376905+00:00
-- url     : https://prove2.me/theorems/ec7634a8-e171-43d3-8deb-2a6e768336af
-- title:
--   Definitions bundle OAIQ091C033 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C029` and `OAIQ091C030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C034`, `OAIQ091C051`, `OAIQ091C052` and `OAIQ091C056`; the statement `OAI_PositiveEinsteinFour_HighestHessian_traceComponent_pairing_hessian`; the proof of `OAI_PositiveEinsteinFour_Bianchi_matrixRotation_energy`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C029
import Definitions.Def_OAIQ091C030

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The round-sphere covering map, with its polar values
and surjectivity supplied by global exponential coverage. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped BigOperators Manifold ContDiff _root_.Topology
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable [PreconnectedSpace M]

theorem roundSphereMap_surjective (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    Function.Surjective (roundSphereMap g o e) := by
  intro x
  obtain ⟨v, hv, hlen⟩ := frameExponential_global_minimizing g o hRic e he x
  by_cases hz : v = 0
  · refine ⟨roundPolarPoint 0 firstDirection, ?_⟩
    rw [roundSphereMap_polar hRic hplus hminus e he 0 ⟨le_rfl, Real.pi_pos.le⟩,
      zero_smul, ← hz, hv]
  · let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
    have hvq : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
    have hmin : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
      rw [hvq]
      change metricDistance g e.base (frameExponential g o e v) = ‖v‖
      rw [hv, hlen]
    have hc := (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg v)).mp hmin
    have hπ : ‖v‖ ≤ Real.pi := hc.trans
      (actualCutTime_le_pi g hRic (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))))
    refine ⟨roundPolarPoint ‖v‖ q, ?_⟩
    rw [roundSphereMap_polar hRic hplus hminus e he ‖v‖ ⟨(norm_nonneg v), hπ⟩, hvq, hv]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


