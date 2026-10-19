-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_TestExtraction
-- name    : OAI_Probability_EntangledGames_TestExtraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:37:15.014808+00:00
-- url     : https://prove2.me/theorems/c65496b1-c859-4211-89a7-d04135c997df
-- title:
--   Threshold probability of the empirical winning rate
-- statement:
--   Let $I$ be a nonempty finite set of coordinates and $\Omega$ a finite set of outcomes. A finite law $\rho$ on $\Omega$ is a family of weights $\rho(\omega)\ge0$ with $\sum_{\omega\in\Omega}\rho(\omega)=1$, and $\mathbb E_\rho[f]=\sum_{\omega}\rho(\omega)f(\omega)$ is the corresponding average. Let $\mathrm{win}:\Omega\times I\to\{\mathrm{true},\mathrm{false}\}$ record, for each outcome $\omega$ and coordinate $i$, whether coordinate $i$ is won in $\omega$, and let
--   $$
--   \mathrm{rate}(\omega)=\frac{1}{|I|}\,\#\{i\in I:\ \mathrm{win}(\omega,i)=\mathrm{true}\}
--   $$
--   be the fraction of won coordinates, i.e. the average of the win indicators under the uniform law on $I$.
--
--   **Threshold probability.** For a real number $s$,
--   $$
--   \mathrm{threshold}_{\rho,\mathrm{win}}(s)=\mathbb E_\rho\big[\mathbf 1[\mathrm{rate}\ge s]\big]=\sum_{\omega\in\Omega}\rho(\omega)\,\mathbf 1\big[s\le\mathrm{rate}(\omega)\big],
--   $$
--   the probability under $\rho$ that at least a fraction $s$ of the coordinates is won.
--
--   This is the abstract form of the tail probability in threshold parallel repetition. For a $k$-fold repeated game with $k\ge1$, take $I=\{0,\dots,k-1\}$, let $\Omega$ consist of the question and answer tuples, let $\rho$ be the joint law of questions and answers produced by a strategy, and let $\mathrm{win}(\omega,i)$ be the acceptance of coordinate $i$. Since the number of won coordinates is an integer, $\mathrm{rate}\ge v+\delta$ holds exactly when at least $\lceil (v+\delta)k\rceil$ coordinates are won, so the threshold probability of the main theorem is $\mathrm{threshold}_{\rho,\mathrm{win}}(v+\delta)$ with $v$ the entangled value. Stating it for arbitrary finite laws lets Markov-type and moment bounds be proved once and then specialised.
--
--   **Formalization Note** The definition is `Tests.threshold ρ win s := ρ.avg (fun ω => if s ≤ rate win ω then 1 else 0)`, where `Law Ω` is the structure of nonnegative weights summing to $1$, `avg` is the weighted sum, and `rate win ω` (from the test-moments file) is the average of the $0/1$ indicators of `win ω i` under the uniform law on `I`. The second section of the file only fixes variables (a game, a repeated model, and hypotheses identifying the model's question law and acceptance predicate with those of the game) and contains no declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/TestExtraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/TestExtraction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments

namespace OAI

universe u_I u_Ω

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)

def threshold (s : ℝ) : ℝ := ρ.avg (fun ω => if s ≤ rate win ω then (1:ℝ) else 0)
end ThresholdParallelRepetition.FiniteProbability.Tests

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI


