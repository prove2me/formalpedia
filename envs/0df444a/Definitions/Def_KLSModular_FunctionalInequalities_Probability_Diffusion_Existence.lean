-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
-- name    : KLSModular_FunctionalInequalities_Probability_Diffusion_Existence
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:25:24.796826+00:00
-- url     : https://prove2.me/theorems/523c289a-088b-456f-9966-2cf2f32eb8dc
-- title:
--   Zero-jump Poisson measure and diffusion coefficient packaging
-- statement:
--   The private auxiliary definition `zeroPoisson` constructs a Poisson random measure with zero intensity on `Unit`: its counting process is identically zero, with the corresponding measurability, integer-valuedness, Poisson-law, independence, and past/future independence fields. The private definition `diffusionCoeffs` packages autonomous drift $b$, diffusion coefficients $\sigma$, and zero jump coefficients into `JumpDiffusionCoeffs N d Unit`. These are technical data structures used by the surrounding existence construction; this bundle itself exposes no public existence theorem.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Diffusion.Setup
--   import LevyStochCalc.Ito.PicardGlobal
--   import LevyStochCalc.Ito.VectorItoVersionLimit
--   import LevyStochCalc.Ito.ItoFormulaUnbounded
--   import LevyStochCalc.Brownian.AugmentedFiltration
--   import LevyStochCalc.Brownian.MultidimFiltered
--   import LevyStochCalc.Brownian.ItoL2CompletionMaster
--   import LevyStochCalc.Probability.DoobContinuous
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   private def zeroPoisson {Ω : Type u} [MeasurableSpace Ω]
--       (P : Measure Ω) [IsProbabilityMeasure P] :
--       Poisson.PoissonRandomMeasure.{u, 0, 0} P (0 : Measure Unit)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Diffusion/Setup`](https://prove2.me/theorems/75711a6c-6c0c-4b07-ab17-35ac267ca6bd), [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083), [`LevyStochCalc/Ito/VectorItoVersionLimit`](https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6), [`LevyStochCalc/Ito/ItoFormulaUnbounded`](https://prove2.me/theorems/02a88305-4a4f-4275-8628-0058c5b0b6ff), [`LevyStochCalc/Brownian/AugmentedFiltration`](https://prove2.me/theorems/3cbf8b32-8c2c-4826-b624-2939bc0b44c4), [`LevyStochCalc/Brownian/MultidimFiltered`](https://prove2.me/theorems/b4d1ac23-3fea-40f2-8621-83c034eb1b1a), [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780).
--
--   Theorems in source order:
--
--   - [`diffusionCoeffs_lipschitz`](https://prove2.me/theorems/fd8b709d-67fc-4441-99f2-2be39c9c9a73)
--   - [`exists_isDiffusion`](https://prove2.me/theorems/7af98979-05ab-4014-86ce-c2315b88e573)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Existence.lean) · `FunctionalInequalities.Probability.Diffusion.Existence` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Existence.lean#L29-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Existence`, definition bundle `KLSModular_FunctionalInequalities_Probability_Diffusion_Existence`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Setup
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal
import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit
import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnbounded
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace FunctionalInequalities
namespace Probability
namespace Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
universe u
 def zeroPoisson {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    Poisson.PoissonRandomMeasure.{u, 0, 0} P (0 : Measure Unit) where
  N := fun _ => 0
  measurable_eval := fun _ => measurable_const
  integer_valued := fun _ _ =>
    Filter.Eventually.of_forall fun _ => ⟨0, by simp⟩
  infinite_at_infinite_intensity := by
    intro B _ h
    simp [Poisson.referenceIntensity] at h
  poisson_law := by
    intro B _ _
    have hz : poissonMeasure 0 = Measure.dirac 0 := by
      apply Measure.ext_of_singleton
      intro n
      cases n <;> simp [poissonMeasure_singleton]
    change P.map (fun _ => (0 : ℝ≥0∞)) = _
    rw [Measure.map_const]
    simp [Poisson.referenceIntensity, Poisson.poissonMeasureENN, hz]
  independent_disjoint := by
    classical
    intro ι _ _ _ _
    apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro S sets hs
    clear hs
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      by_cases hz : (0 : ℝ≥0∞) ∈ sets i <;> simp_all [Set.preimage_const]
  joint_past_future_independent := by
    intro s t _ _ A _ _
    simp only [Measure.coe_zero, Pi.zero_apply, MeasurableSpace.comap_const]
    exact indep_bot_right _
 def diffusionCoeffs {N d : ℕ}
    (b : (Fin N → ℝ) → Fin N → ℝ)
    (σ : (Fin N → ℝ) → Fin d → Fin N → ℝ) :
    LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs N d Unit :=
  ⟨fun _ => b, fun _ x i k => σ x k i, fun _ _ _ => 0⟩
end Diffusion
end Probability
end FunctionalInequalities


