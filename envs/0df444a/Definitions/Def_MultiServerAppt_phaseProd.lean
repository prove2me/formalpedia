-- Prove2me | Definitions.Def_MultiServerAppt_phaseProd
-- name    : MultiServerAppt_phaseProd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:51.149723+00:00
-- url     : https://prove2.me/theorems/0c25bb13-6151-4d49-a5b2-48debaf8e3a8
-- title:
--   Product of a phase function over a state
-- statement:
--   For a function $h:\iota\to\mathbb R$ and a state with phase vector $m=(m_1,\dots,m_\xi)$, this is $\prod_{\ell=1}^{\xi}h(m_\ell)$.
--
--   **Formalization Note** The product depends only on the multiset of phases, so a statement that uses it does not assign clients to slots.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11

import Mathlib
import Definitions.Def_MultiServerAppt_State

namespace MultiServerAppt

/-- The product `∏ ℓ, h (m ℓ)` of a function of phases over the coordinates of the phase vector `m`
of a state `(j, m)`. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1,
p.11 (the vector `(m₁, …, m_ξ)`).

**Formalization Note** It depends only on the multiset of phases, so a statement using it does not
assign clients to slots: the page's slots are "without loss of generality". -/
def phaseProd {ι : Type*} {s i : ℕ} (h : ι → ℝ) : State ι s i → ℝ
  | .inl p => ∏ l, h (p.2 l)
  | .inr p => ∏ l, h (p.2 l)

end MultiServerAppt


