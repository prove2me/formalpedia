-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
-- name    : OAI_Analysis_Littlewood_ProductProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:03:47.466969+00:00
-- url     : https://prove2.me/theorems/196a9270-0a65-444b-b26f-da2847d23ab5
-- title:
--   Product Bernoulli weights on Boolean configurations, expectation, and no-hit indicators
-- statement:
--   Let $E$ be a finite set and $p\in\mathbb{R}$. A configuration is a map $s:E\to\{\mathrm{true},\mathrm{false}\}$; $s_e=\mathrm{true}$ means that $e$ is selected. Write $\mathbf{1}[\cdot]$ for the indicator of a condition.
--
--   1. **Coin weight.**
--   $$
--   w_p(s)=\prod_{e\in E}\begin{cases}p, & s_e=\mathrm{true},\\ 1-p, & s_e=\mathrm{false}.\end{cases}
--   $$
--
--   2. **Expectation.** For $f$ from configurations to $\mathbb{R}$, $\mathbb{E}_p[f]=\sum_{s}w_p(s)\,f(s)$, the sum over all $2^{|E|}$ configurations.
--
--   3. **No-hit indicator.** For $A\subseteq E$, $N_A(s)=\prod_{e\in A}\mathbf{1}[s_e=\mathrm{false}]$, which is $1$ if no element of $A$ is selected and $0$ otherwise.
--
--   4. **Selection indicator.** $\chi_e(s)=\mathbf{1}[s_e=\mathrm{true}]$ for $e\in E$.
--
--   The weights sum to $1$ for every real $p$ and are nonnegative for $0\le p\le1$, so in that range $\mathbb{E}_p$ is the expectation for independent selection of each element with probability $p$. Then $\mathbb{E}_p[N_A]=(1-p)^{|A|}$, $\mathbb{E}_p[\chi_e]=p$ and $\mathbb{E}_p[\chi_e\chi_f]=p^2$ for $e\ne f$, and products of no-hit indicators are the basic events of the second-moment (Chebyshev) estimates. This finite probability space models one round of the random nibble, in which every edge of a hypergraph is selected independently and a vertex survives exactly when none of its incident edges is selected.
--
--   **Formalization Note** `coinWeight p s`, `expectation p f`, `noHit A s` and `selectedIndicator e s` are real-valued, the configuration space is the finite type `E → Bool`, and no hypothesis on $p$ is built into the definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ProductProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/ProductProbability.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading

namespace OAI

universe uE uI

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset

section ProductSpace
variable {E : Type uE} [Fintype E] [DecidableEq E]

def coinWeight (p : ℝ) (s : E → Bool) : ℝ :=
  ∏ e, if s e then p else 1 - p

def expectation (p : ℝ) (f : (E → Bool) → ℝ) : ℝ :=
  ∑ s, coinWeight p s * f s

def noHit (A : Finset E) (s : E → Bool) : ℝ :=
  ∏ e ∈ A, if s e then 0 else 1

/-- A Bernoulli indicator, for counting selected edges. -/
def selectedIndicator (e : E) (s : E → Bool) : ℝ := if s e then 1 else 0

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI


