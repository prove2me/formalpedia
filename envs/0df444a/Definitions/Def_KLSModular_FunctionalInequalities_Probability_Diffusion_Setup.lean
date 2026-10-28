-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Setup
-- name    : KLSModular_FunctionalInequalities_Probability_Diffusion_Setup
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T19:24:11.461215+00:00
-- url     : https://prove2.me/theorems/75711a6c-6c0c-4b07-ab17-35ac267ca6bd
-- title:
--   Usual Brownian filtration and diffusion predicate
-- statement:
--   For a multidimensional Brownian motion `W` under a probability measure $P$, `usualFiltration W` is the augmentation of the right-continuous natural filtration of `W`; the included instance asserts that this filtration is right-continuous. `IsDiffusion W ℱ hW b σ x₀ Y` means that $Y : \mathbb{R}\to\Omega\to(\mathrm{Fin}\,N\to\mathbb{R})$ has an Itô representation with initial value $x₀$, drift $b(Y_s)$, and diffusion coefficients $\sigma(Y_s)$ driven by the Brownian coordinates of `W`. The predicate additionally requires measurability, progressive measurability, and finite `ENNReal` squared energy on every interval $[0,T]$ with $T>0$ for each diffusion coefficient, together with the `IsVectorItoVersion` relation.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardGlobal
--   import LevyStochCalc.Ito.VectorItoVersionLimit
--   import LevyStochCalc.Ito.ItoFormulaUnbounded
--   import LevyStochCalc.Brownian.AugmentedFiltration
--   import LevyStochCalc.Brownian.MultidimFiltered
--   import LevyStochCalc.Brownian.ItoL2CompletionMaster
--   import LevyStochCalc.Brownian.ItoFinsetSum
--   import LevyStochCalc.Probability.DoobContinuous
--   import LevyStochCalc.Poisson.Filtered
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def usualFiltration (W : MultidimBrownianMotion P d) :
--       Filtration ℝ ‹MeasurableSpace Ω› :=
--     augFiltration W.naturalFiltration.rightCont P
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083), [`LevyStochCalc/Ito/VectorItoVersionLimit`](https://prove2.me/theorems/369f5dfc-9ec0-43f0-9778-d630d2bf30a6), [`LevyStochCalc/Ito/ItoFormulaUnbounded`](https://prove2.me/theorems/02a88305-4a4f-4275-8628-0058c5b0b6ff), [`LevyStochCalc/Brownian/AugmentedFiltration`](https://prove2.me/theorems/3cbf8b32-8c2c-4826-b624-2939bc0b44c4), [`LevyStochCalc/Brownian/MultidimFiltered`](https://prove2.me/theorems/b4d1ac23-3fea-40f2-8621-83c034eb1b1a), [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/ItoFinsetSum`](https://prove2.me/theorems/3c65a1ac-837e-48a1-b323-dc87feeb6397), [`LevyStochCalc/Probability/DoobContinuous`](https://prove2.me/theorems/948ff195-c1ab-45a5-b573-556d15dca780), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Setup.lean) · `FunctionalInequalities.Probability.Diffusion.Setup` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Setup.lean#L33-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Setup`, definition bundle `KLSModular_FunctionalInequalities_Probability_Diffusion_Setup`; the repository is private at upload time).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal
import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit
import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnbounded
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_AugmentedFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFinsetSum
import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_Filtered

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
namespace FunctionalInequalities
namespace Probability
namespace Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
  LevyStochCalc.Brownian.Ito
section Usual
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
noncomputable def usualFiltration (W : MultidimBrownianMotion P d) :
    Filtration ℝ ‹MeasurableSpace Ω› :=
  augFiltration W.naturalFiltration.rightCont P
instance (W : MultidimBrownianMotion P d) : (usualFiltration W).IsRightContinuous :=
  isRightContinuous_augFiltration W.naturalFiltration P
end Usual
section Diffusion
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {N d : ℕ}
/-- `Y` is an everywhere-continuous adapted version of
`x₀ + ∫₀ᵗ b(Y_s) ds + Σ_k ∫₀ᵗ σ_k(Y_s) dW^k_s`, coefficients evaluated along `Y` itself. -/
def IsDiffusion (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (b : (Fin N → ℝ) → Fin N → ℝ) (σ : (Fin N → ℝ) → Fin d → Fin N → ℝ) (x₀ : Fin N → ℝ)
    (Y : ℝ → Ω → Fin N → ℝ) : Prop :=
  ∃ (hm : ∀ i k, Measurable (Function.uncurry fun ω s => σ (Y s ω) k i))
    (hp : ∀ i k, Probability.ProgressivelyMeasurable ℱ fun ω s => σ (Y s ω) k i)
    (hq : ∀ i k (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖σ (Y s ω) k i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
    IsVectorItoVersion W ℱ hW (fun i k ω s => σ (Y s ω) k i) hm hp hq
      (fun _ => x₀) (fun i ω s => b (Y s ω) i) Y
end Diffusion
end Diffusion
end Probability
end FunctionalInequalities


