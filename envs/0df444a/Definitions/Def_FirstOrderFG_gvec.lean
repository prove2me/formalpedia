-- Prove2me | Definitions.Def_FirstOrderFG_gvec
-- name    : FirstOrderFG_gvec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:14.562411+00:00
-- url     : https://prove2.me/theorems/480c7231-a830-455c-9b07-26f0837495d8
-- title:
--   Master loss vector $g_t$
-- statement:
--   The master's loss vector is $g_t\in\mathbb R^{\mathcal B}$ with
--   $$
--   g_{t,0}=\langle q_t,\ell_t\rangle\ \ (\text{when }0\in\mathcal B),\qquad g_{t,i}=\ell_{t,i}\ \ (i\in\bar V_{\mathrm{self}}).
--   $$
--   Then $\mathbb E_t[\ell_{t,I_t}]=\langle x_t,g_t\rangle$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §4.1, p.8

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **The master loss vector `g_t`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §4.1, p.8: "denote by `g_t ∈ ℝ^B` its loss vector,
with `g_{t,0} ≜ ⟨q_t, ℓ_t⟩` when `0 ∈ B` and `g_{t,i} ≜ ℓ_{t,i}` for `i ∈ V̄_self`."

**Formalization Note.** `⟨q_t, ℓ_t⟩` is the sum over `V_self`, the support of `q_t`. -/
def gvec {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (lt q : Fin K → ℝ) :
    Option (Fin K) → ℝ
  | none => ∑ i ∈ Vself E, q i * lt i
  | some i => lt i

end FirstOrderFG


