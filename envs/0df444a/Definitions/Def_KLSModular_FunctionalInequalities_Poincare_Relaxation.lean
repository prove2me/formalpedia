-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_Relaxation
-- name    : KLSModular_FunctionalInequalities_Poincare_Relaxation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:32:47.944245+00:00
-- url     : https://prove2.me/theorems/33b81a93-0d3f-4459-b2f9-a34a6959e52b
-- title:
--   Poincaré test family from a finite pre-energy
-- statement:
--   `Poincare.TestFamily.ofPreEnergy` builds a test family from a pre-energy on real L²(μ), assigning each concrete test the variance of its ambient L² realization and its original finite energy. The bundle contains only this family definition; it does not itself state density, quadraticity, or a comparison between the pre-energy and its sequential relaxation. The associated framework permits empty test types and extended optimal constants, including ⊤.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Relaxation.Recovery
--   import FunctionalInequalities.Poincare.L2.Energy
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def ofPreEnergy : TestFamily where
--     Test := P.Test
--     variance f := L2.variance μ (P.toAmbient f)
--     energy := P.energy
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Relaxation/Recovery`](https://prove2.me/theorems/61648fda-a4ff-49b1-a631-1c0a917bd957), [`Poincare/L2/Energy`](https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927).
--
--   Theorems in source order:
--
--   - [`holds_ofPreEnergy_iff`](https://prove2.me/theorems/45fe7f2a-781b-4639-a2c2-4c48911bc95c)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/Relaxation.lean) · `FunctionalInequalities.Poincare.Relaxation` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/Relaxation.lean#L30-L34 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.Relaxation`, definition bundle `KLSModular_FunctionalInequalities_Poincare_Relaxation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Recovery
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy

noncomputable section
open MeasureTheory Filter Topology
namespace FunctionalInequalities
namespace Poincare
namespace TestFamily
universe u
variable {α : Type u} [MeasurableSpace α] (μ : ProbabilityMeasure α)
  (P : Energy.PreEnergy (Lp ℝ 2 (μ : Measure α)))
/-- Concrete tests with the variance of their `L²` realizations and their raw finite energy. -/
def ofPreEnergy : TestFamily where
  Test := P.Test
  variance f := L2.variance μ (P.toAmbient f)
  energy := P.energy
end TestFamily
end Poincare
end FunctionalInequalities


