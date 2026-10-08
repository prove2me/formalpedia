-- Prove2me | Definitions.Def_SelfishRouting_Linear_LinearLatency
-- name    : SelfishRouting_Linear_LinearLatency
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:58.362996+00:00
-- url     : https://prove2.me/theorems/2910fb65-f672-4183-8d61-fa219f049846
-- title:
--   Linear latencies $\ell_e(x)=a_ex+b_e$, marginal costs $\ell^*_e(x)=2a_ex+b_e$, and $L^*_i(f^*)$
-- statement:
--   Section 4 of Roughgarden and Tardos considers **linear latency functions**
--   $$\ell_e(x)=a_e x+b_e ,$$
--   with coefficients $a_e,b_e$ (nonnegative in every statement that uses them).
--
--   The **marginal cost function** of edge $e$ is the derivative of $x\,\ell_e(x)$ (§2.3, p. 9), which for a linear latency is (§4, p. 14)
--   $$\ell^*_e(x)=\big(x\,\ell_e(x)\big)'=2a_e x+b_e .$$
--   The marginal cost of a route $P$ under a flow $f$ is $\ell^*_P(f)=\sum_{e\in P}\ell^*_e(f_e)$, i.e. the path latency of the model built from the latencies $\ell^*$.
--
--   For a flow $f^*$ and a commodity $i$, $L^*_i(f^*)$ is "the minimum marginal cost of increasing flow on an $s_i$-$t_i$ path with respect to $f^*$" (Lemma 4.4, p. 16):
--   $$L^*_i(f^*)=\min_{P\in\mathcal P_i}\ell^*_P(f^*).$$
--
--   **Formalization Note** $L^*_i$ is the infimum over the finite type of routes serving $i$, which is attained (a minimum) whenever some route serves $i$. If no route serves $i$, Lean's real infimum is $0$; every statement that uses $L^*_i$ assumes $r_i>0$ together with a feasible flow, which forces a route serving $i$, so this convention never enters.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 14, §4 (ℓₑ(x) = aₑx + bₑ, ℓ*ₑ(x) = 2aₑx + bₑ); p. 9 (marginal cost); p. 16, Lemma 4.4 (L*ᵢ(f*))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model

namespace SelfishRouting.Linear

/-- Linear latency functions `ℓ_e(x) = a_e x + b_e` (§4, p. 14). -/
def linLatency {J : ℕ} (a b : Fin J → ℝ) : Fin J → ℝ → ℝ :=
  fun j t => a j * t + b j

/-- The marginal cost function `ℓ*_e(x) = (ℓ_e(x) x)′ = 2 a_e x + b_e` of a linear latency
(§2.3, p. 9; §4, p. 14). -/
def marginalLatency {J : ℕ} (a b : Fin J → ℝ) : Fin J → ℝ → ℝ :=
  fun j t => 2 * a j * t + b j

/-- `L*_i(f*)`, the minimum marginal cost of increasing flow on an `sᵢ`-`tᵢ` path with respect
to `x` (Lemma 4.4, p. 16): the minimum over the routes `r` serving commodity `i` of the
marginal path cost `ℓ*_P(x) = ∑_{e ∈ P} ℓ*_e(x_e)`.

The infimum ranges over the finite type of routes serving `i`; when that type is nonempty it is
attained, so it is a minimum. When no route serves `i` the real infimum is `0` by convention;
every statement using this definition assumes `0 < rate i` and a feasible flow, which forces a
route serving `i`. -/
noncomputable def minMarginalPathCost {J R Sd : ℕ} (A : Fin J → Fin R → ℝ)
    (s : Fin R → Fin Sd) (a b : Fin J → ℝ) (x : Fin R → ℝ) (i : Fin Sd) : ℝ :=
  ⨅ r : {r : Fin R // s r = i}, SelfishRouting.Bicriteria.pathLatency A (marginalLatency a b) x r.1

end SelfishRouting.Linear


