-- Prove2me | Definitions.Def_OAI_Probability_Localization_Experiment
-- name    : OAI_Probability_Localization_Experiment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T19:33:44.730986+00:00
-- url     : https://prove2.me/theorems/337e23eb-8418-4298-8dd8-9bc34517a070
-- title:
--   The Gaussian block law is a probability measure
-- statement:
--   For $n\in\mathbb{N}$ put $m=\lfloor n/16\rfloor$. A Gaussian block is a real $m\times(n+1)$ matrix $X=(X_{r,a})$ with rows $r\in\{0,\dots,m-1\}$ and columns $a\in\{0,\dots,n\}$. The Gaussian block law $\gamma_n$ is the law of such a matrix with independent standard normal entries, that is, the product measure
--
--   $$
--   \gamma_n=\bigotimes_{r=0}^{m-1}\ \bigotimes_{a=0}^{n}\mathcal{N}(0,1)\qquad\text{on }\mathbb{R}^{m\times(n+1)} .
--   $$
--
--   The file records that $\gamma_n$ is a probability measure for every $n$. When $n<16$ there are no rows, and $\gamma_n$ is the unit mass on the empty matrix.
--
--   In the repeated-localization experiment a point $z$ of the small cube in $\mathbb{R}^n$ is lifted to $\mathrm{chart}(z)=\big(z_1,\dots,z_n,\sqrt{1-\|z\|^2}\big)\in\mathbb{R}^{n+1}$. A block $X\sim\gamma_n$ then produces the exact labels $X\,\mathrm{chart}(z)\in\mathbb{R}^m$, and the probability that a randomized rule outputs a given symbol is the integral of the rule's output probabilities against $\gamma_n$. Because $\gamma_n$ is a probability measure, these averaged probabilities lie in $[0,1]$ and sum to one.
--
--   **Formalization Note** The law is `gaussianBlockLaw n` from the base definitions, an iterated `Measure.pi` of `gaussianReal 0 1` over `Fin (n / 16)` and `Fin (n + 1)`. The instance `gaussianBlockLaw_isProbabilityMeasure` follows by instance inference, since finite products of probability measures are probability measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Experiment.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/Experiment.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianFiniteEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

instance gaussianBlockLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianBlockLaw n) := by
  unfold gaussianBlockLaw
  infer_instance

end RepeatedLocalization

end OAI


