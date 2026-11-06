-- Prove2me | Definitions.Def_FirstOrderFG_picardFixed
-- name    : FirstOrderFG_picardFixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:49:15.034204+00:00
-- url     : https://prove2.me/theorems/e4614ba2-bd7f-41b2-9104-096b33885e18
-- title:
--   The interior $\varepsilon$-fixed point computed by Picard iteration
-- statement:
--   Given $p$ in the interior of $\Delta(V_{\mathrm{self}})$, $\gamma>0$ and an interior start $q^{(0)}$, line 6 of Algorithm 2 computes an interior $\varepsilon$-fixed point of $F_{p,\gamma}$ by Picard iteration. Here it is the first iterate $q^{(n)}$ with $n\ge1$ and
--   $$
--   \|q^{(n)}-F_{p,\gamma}(q^{(n)})\|_1\le\varepsilon=\frac1{KT^2}.
--   $$
--
--   **Formalization Note** The stopping index is the infimum of the set of such $n$; that this set is nonempty (the iteration terminates) is the Picard residual milestone.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 6, p.10; Proposition A.3, p.20

import Mathlib
import Definitions.Def_FirstOrderFG_picardIter
import Definitions.Def_FirstOrderFG_fixResidual
import Definitions.Def_FirstOrderFG_epsFix

namespace FirstOrderFG

/-- **The interior `ε`-fixed point computed by Picard iteration (Algorithm 2, line 6).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Algorithm 2, line 6, p.10 ("Compute an interior `ε`-fixed point `q_t` of `q ↦ (…)` by Picard
iteration"), and Proposition A.3, p.20 ("Fix any `q^{(0)} ∈ int(∆(V_self))` and set
`q^{(n+1)} = F_{p,γ}(q^{(n)})`").

`picardFixed E T p γ q0` is the first Picard iterate `q^{(n)}`, `n ≥ 1`, from the start `q0` whose
residual `‖q^{(n)} − F_{p,γ}(q^{(n)})‖₁` is at most `ε = 1/(KT²)`.

**Formalization Note.** The stopping index is `sInf {n | 1 ≤ n ∧ residual ≤ ε}`; that this set is
nonempty for every interior start, `p ∈ int ∆(V_self)` and `γ > 0` is the content of the Picard
residual milestone (the residual decays geometrically), so the iteration terminates. -/
noncomputable def picardFixed {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (p : Fin K → ℝ) (γ : ℝ) (q0 : Fin K → ℝ) : Fin K → ℝ :=
  picardIter E T p γ q0
    (sInf {n : ℕ | 1 ≤ n ∧ fixResidual E T p γ (picardIter E T p γ q0 n) ≤ epsFix K T})

end FirstOrderFG


