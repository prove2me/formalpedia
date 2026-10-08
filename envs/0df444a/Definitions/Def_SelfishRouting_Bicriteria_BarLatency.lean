-- Prove2me | Definitions.Def_SelfishRouting_Bicriteria_BarLatency
-- name    : SelfishRouting_Bicriteria_BarLatency
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:11.314286+00:00
-- url     : https://prove2.me/theorems/24c63d6c-136a-45ca-b885-293f464ab839
-- title:
--   Proof of Theorem 3.1, p. 12 — the modified latencies $\bar\ell_e$
-- statement:
--   The proof of Theorem 3.1 replaces the latency functions $\ell$ by new latency functions $\bar\ell$ built from the edge flows $f_e$ of a Nash flow $f$:
--   $$
--   \bar\ell_e(x) = \begin{cases} \ell_e(f_e) & \text{if } x \le f_e, \\ \ell_e(x) & \text{if } x \ge f_e. \end{cases}
--   $$
--   The two cases agree at $x = f_e$. Thus $\bar\ell_e$ is $\ell_e$ flattened to the constant $\ell_e(f_e)$ below the Nash edge flow (Figure 4 of the paper).
--
--   Here $\bar\ell$ is a function of $\ell$ and of the vector of edge flows $y = (y_e)_e$; the statements of the mission apply it with $y$ the edge flows of the Nash flow.
--
--   The function is the device that lets the cost of any flow under $\bar\ell$ be bounded both above (by the original cost plus $C(f)$) and below (by $2C(f)$ for flows of twice the rates).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 12, proof of Theorem 3.1 (definition of ℓ̄)

import Mathlib

namespace SelfishRouting.Bicriteria

/-- The modified latency functions `ℓ̄` of the proof of Theorem 3.1 (p. 12), built from the
latencies `ℓ` and the edge flows `y` of a Nash flow:
`ℓ̄_e(t) = ℓ_e(y_e)` for `t ≤ y_e` and `ℓ̄_e(t) = ℓ_e(t)` for `t ≥ y_e`
(the two cases agree at `t = y_e`). -/
noncomputable def barLatency {J : ℕ} (ℓ : Fin J → ℝ → ℝ) (y : Fin J → ℝ) (j : Fin J)
    (t : ℝ) : ℝ :=
  if t ≤ y j then ℓ j (y j) else ℓ j t

end SelfishRouting.Bicriteria


