-- Prove2me | Definitions.Def_MultiServerAppt_alphaInit
-- name    : MultiServerAppt_alphaInit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:02.84707+00:00
-- url     : https://prove2.me/theorems/fc65bbdd-84be-47fa-bd33-a88f75c8d1d5
-- title:
--   The initial vector $\alpha_s$
-- statement:
--   All $s$ servers start with a client, in independent phases with law $\alpha$. So $\alpha_s$ puts mass $\prod_{\ell=1}^s\alpha_{m_\ell}$ on the state $(s,m)$ and mass $0$ on every state with fewer than $s$ clients:
--
--   $$\alpha_s=(\alpha\otimes\cdots\otimes\alpha,\ \mathbf 0).$$
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.12

import Mathlib
import Definitions.Def_MultiServerAppt_State

namespace MultiServerAppt

/-- The initial vector `α_s = (α ⊗ ⋯ ⊗ α, 0)`: all `s` servers start with a client, in independent
phases with law `α`, and every state with fewer than `s` clients has mass `0`. Kuiper–Lee, Appointment
Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.12. -/
def alphaInit {ι : Type*} (α : ι → ℝ) (s : ℕ) : State ι s 0 → ℝ
  | .inl p => p.1.elim0
  | .inr p => if (p.1 : ℕ) + 1 = s then ∏ l, α (p.2 l) else 0

end MultiServerAppt


