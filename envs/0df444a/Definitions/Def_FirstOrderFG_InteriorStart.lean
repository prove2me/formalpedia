-- Prove2me | Definitions.Def_FirstOrderFG_InteriorStart
-- name    : FirstOrderFG_InteriorStart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:37.239577+00:00
-- url     : https://prove2.me/theorems/bf7e6a15-0437-47b5-8de9-f6465735b517
-- title:
--   Admissible start rule for the Picard iteration
-- statement:
--   A **start rule** $q_0$ assigns to every base distribution $p$ and parameter $\gamma$ an initial point $q_0(p,\gamma)$ of the Picard iteration. It is **admissible** if, whenever $V_{\mathrm{self}}\ne\emptyset$, the point lies in the relative interior of $\Delta(V_{\mathrm{self}})$:
--   $$
--   q_0(p,\gamma)_i>0\ \ (i\in V_{\mathrm{self}}),\qquad \sum_{i\in V_{\mathrm{self}}}q_0(p,\gamma)_i=1 .
--   $$
--   The paper fixes any interior start; the uniform distribution on $V_{\mathrm{self}}$ is an example.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Proposition A.3, p.20; Algorithm 2, line 6, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **An admissible Picard start rule.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Proposition A.3, p.20 ("Fix any
`q^{(0)} ∈ int(∆(V_self))`"), as used by Algorithm 2, line 6, p.10.

A start rule `q₀` chooses, for the current base distribution `p` and parameter `γ`, the initial
point `q₀ p γ` of the Picard iteration. It is admissible when that point lies in the relative
interior of `∆(V_self)` (strictly positive coordinates on `V_self`, summing to one) whenever
`V_self` is nonempty.

**Formalization Note.** The paper leaves the start free; the theorems quantify over every
admissible start rule, so they hold for each choice (e.g. the uniform distribution on `V_self`). -/
def InteriorStart {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E]
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) : Prop :=
  ∀ (p : Fin K → ℝ) (γ : ℝ), (Vself E).Nonempty →
    (∀ i ∈ Vself E, 0 < q₀ p γ i) ∧ ∑ i ∈ Vself E, q₀ p γ i = 1

end FirstOrderFG


