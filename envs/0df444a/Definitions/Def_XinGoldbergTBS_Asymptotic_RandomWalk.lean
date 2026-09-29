-- Prove2me | Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk
-- name    : XinGoldbergTBS_Asymptotic_RandomWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:20:02.514909+00:00
-- url     : https://prove2.me/theorems/585d948d-86e8-4555-93ed-8190b882f4d4
-- title:
--   Random walk $W^r_k$, running maxima $Z^r_k$, $Z^r_\infty$ and their means $M^r_k$, $M^r_\infty$
-- statement:
--   For $r \in \mathbb R$ and i.i.d. demands $D_1, D_2, \dots \sim D$, set
--   $$W^r_k = \sum_{j=1}^{k}(r - D_j), \qquad Z^r_k = \max_{i \in [0, k-1]} W^r_i \ (k \ge 1), \qquad Z^r_\infty = \sup_{i \ge 0} W^r_i,$$
--   and $M^r_k = \mathbb E[Z^r_k]$, $M^r_\infty = \mathbb E[Z^r_\infty]$ (p. 444). Since $W^r_0 = 0$, all these maxima are nonnegative, and $Z^r_\infty$ and $M^r_\infty$ may be $+\infty$. The same $Z^r_\infty$ is the quantity $I^r_\infty = \sup_{j \ge 0}(jr - \sum_{i=1}^j D_i)$ in the TBS cost formula (3) (p. 440).
--
--   These objects describe the stationary inventory position of a TBS policy and are the main tool of the lower bound on $r_L$.
--
--   **Formalization Note** $Z^r_\infty$ and all expectations take values in $[0,\infty]$; $M^r_k$ is the expectation of the (nonnegative) finite maximum. The demand path coordinate $j$ is the paper's $D_{j+1}$.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 444, Section 3.2 (definitions before Corollary 3); p. 440, Eq. (3)

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model

/-!
# The random walk `W^r`, its running maxima `Z^r`, and `M^r` (p. 444)

On the i.i.d. demand path (coordinate `j` is `D_{j+1}`): `W^r_k = ∑_{j=1}^k (r - D_j)`,
`Z^r_k = max_{i ∈ [0, k-1]} W^r_i` (`k ≥ 1`), `Z^r_∞ = sup_{i ≥ 0} W^r_i ∈ [0, ∞]`,
`M^r_k = 𝔼[Z^r_k]`, `M^r_∞ = 𝔼[Z^r_∞]`. Since `W^r_0 = 0`, all these maxima are nonnegative;
`Z^r_∞` and the expectations are `ℝ≥0∞`-valued, so `Z^r_∞ = ∞` and `M^r_∞ = ∞` are kept.
The same `Z^r_∞` is the paper's `I^r_∞ = sup_{j ≥ 0}(jr - ∑_{i=1}^j D_i)` (p. 440).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- `W^r_k = ∑_{j=1}^k (r - D_j)`. -/
def W (r : ℝ) (d : Path) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, (r - d j)

/-- `Z^r_k = max_{i ∈ [0, k-1]} W^r_i` (for `k ≥ 1`; a finite maximum). -/
def Z (r : ℝ) (d : Path) (k : ℕ) : ℝ := ⨆ i : Fin k, W r d i

/-- `Z^r_∞ = sup_{i ≥ 0} W^r_i ∈ [0, ∞]` (`W^r_0 = 0`). -/
def Zinf (r : ℝ) (d : Path) : ℝ≥0∞ := ⨆ i : ℕ, ENNReal.ofReal (W r d i)

/-- `M^r_k = 𝔼[Z^r_k]`. -/
def M (μ : DemandLaw) (r : ℝ) (k : ℕ) : ℝ≥0∞ := ∫⁻ d, ENNReal.ofReal (Z r d k) ∂pathLaw μ

/-- `M^r_∞ = 𝔼[Z^r_∞]`. -/
def Minf (μ : DemandLaw) (r : ℝ) : ℝ≥0∞ := ∫⁻ d, Zinf r d ∂pathLaw μ

end XinGoldbergTBS.Asymptotic


