-- Prove2me | Definitions.Def_FirstOrderFG_gtilde
-- name    : FirstOrderFG_gtilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:07.758866+00:00
-- url     : https://prove2.me/theorems/982e7240-1344-4a88-9fac-b424832edb21
-- title:
--   Master loss estimate $\tilde g_t$ (Eq. (20))
-- statement:
--   The master's loss estimates are
--   $$
--   \tilde g_{t,0}=\frac{\ell_{t,I_t}\,\mathbb I\{B_t=0\}}{x_{t,0}},\qquad \tilde g_{t,i}=\frac{\ell_{t,i}\,\mathbb I\{I_t\ne i\}}{1-x_{t,i}}\quad(i\in\bar V_{\mathrm{self}}).
--   $$
--   Under strong observability $\ell_{t,i}$ is observed whenever $I_t\neq i$ for $i\in\bar V_{\mathrm{self}}$.
--
--   **Formalization Note** $B_t=0$ iff $I_t\in V_{\mathrm{self}}$. The value at a non-master coordinate (`some i`, $i\in V_{\mathrm{self}}$) is set to $0$ and never read.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Eq. (20), p.8; Algorithm 2, line 12, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **The master loss estimate `g̃_t` (Eq. (20)).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Eq. (20), p.8, and Algorithm 2, line 12:
`g̃_{t,0} = ℓ_{t,I_t} 𝕀{B_t = 0} / x_{t,0}` and `g̃_{t,i} = ℓ_{t,i} 𝕀{I_t ≠ i} / (1 − x_{t,i})` for
`i ∈ V̄_self`.

**Formalization Note.** The meta-action `0` is `none`; `B_t = 0` iff `I_t ∈ V_self`. The value at
`some i` with `i ∈ V_self` (not a master action) is set to `0`; it is never read. -/
noncomputable def gtilde {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (lt : Fin K → ℝ)
    (x : Option (Fin K) → ℝ) (I : Fin K) : Option (Fin K) → ℝ
  | none => lt I * (if I ∈ Vself E then 1 else 0) / x none
  | some i => if i ∈ Vself E then 0 else lt i * (if I ≠ i then 1 else 0) / (1 - x (some i))

end FirstOrderFG


