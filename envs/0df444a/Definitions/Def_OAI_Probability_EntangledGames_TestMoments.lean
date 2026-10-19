-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_TestMoments
-- name    : OAI_Probability_EntangledGames_TestMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:34:46.404664+00:00
-- url     : https://prove2.me/theorems/0559f4d5-d516-42aa-a40f-28f96c7e069e
-- title:
--   Winning events, win rates and their moments for a random outcome
-- statement:
--   This file defines elementary statistics of a random outcome in which each of finitely many coordinates is either won or lost; they drive a moment method for bounding the probability of winning many coordinates.
--
--   Let $\Omega$ be a finite set with a probability law $\rho$, let $I$ be a finite nonempty set of coordinates, and let $\operatorname{win}(\omega,i)\in\{\text{true},\text{false}\}$ record whether coordinate $i$ is won in the outcome $\omega\in\Omega$.
--
--   1. **Event of a set.** For a finite set $c\subseteq I$, $\mathbf 1_c(\omega)=1$ if $\operatorname{win}(\omega,i)$ holds for every $i\in c$, and $\mathbf 1_c(\omega)=0$ otherwise.
--   2. **Mass.** $\operatorname{mass}(c)=\mathbb{E}_{\omega\sim\rho}\big[\mathbf 1_c(\omega)\big]$ is the probability that all coordinates of $c$ are won; in particular $\operatorname{mass}(\emptyset)=1$.
--   3. **Win rate.** The fraction of coordinates won,
--   $$\operatorname{rate}(\omega)=\frac{1}{|I|}\,\#\{i\in I:\operatorname{win}(\omega,i)\},$$
--   written in the file as the average of the win indicator under the uniform law on $I$.
--   4. **Moments.** For $t\in\mathbb{N}$,
--   $$\operatorname{moment}(c,t)=\mathbb{E}_{\omega\sim\rho}\big[\mathbf 1_c(\omega)\,\operatorname{rate}(\omega)^t\big].$$
--
--   Since $\operatorname{rate}(\omega)^t$ is the probability that $t$ independent uniformly random coordinates are all won, $\operatorname{moment}(c,t)$ is the probability that every coordinate of $c$ and $t$ further random coordinates are won, and $\operatorname{moment}(c,0)=\operatorname{mass}(c)$. For $q\ge0$ one has $\rho(\operatorname{rate}\ge q)\,q^t\le\operatorname{moment}(\emptyset,t)$, while a bound on the average $\mathbb{E}_i\operatorname{mass}(c\cup\{i\})$ over a uniform coordinate $i$ in terms of $\operatorname{mass}(c)$ controls the moments from above; combined, these bound the probability that at least a $q$-fraction of the coordinates is won.
--
--   **Formalization Note** The definitions are `Tests.event`, `Tests.mass`, `Tests.rate` and `Tests.moment`; the win predicate is Boolean-valued and the event is the real number $0$ or $1$. `event` and `rate` do not involve $\rho$. `rate` uses the uniform law `Law.uniform` on $I$, which is why $I$ is assumed nonempty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/TestMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/TestMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel

namespace OAI

universe u_I u_Ω

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)
def event (c : Finset I) (ω : Ω) : ℝ := if ∀ i ∈ c, win ω i then 1 else 0
def mass (c : Finset I) : ℝ := ρ.avg (event win c)
def rate (ω : Ω) : ℝ := (uniform (R := I)).avg (fun i => if win ω i then 1 else 0)
def moment (c : Finset I) (t : ℕ) : ℝ := ρ.avg (fun ω => event win c ω*(rate win ω)^t)

end Tests
end ThresholdParallelRepetition.FiniteProbability

end

end OAI


