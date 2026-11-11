-- Prove2me | Definitions.Def_SybilClinch_trueUtil
-- name    : SybilClinch_trueUtil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:52.448396+00:00
-- url     : https://prove2.me/theorems/323a1966-42f8-4741-bb6d-43b941b62fd1
-- title:
--   True utility of a physical trader from aggregate net flows
-- statement:
--   Let a physical trader with true type $t$ control the identities $D$, and let $\Delta_X=R_X-S_X$, $\Delta_Y=R_Y-S_Y$ be its aggregate net changes in $X$ and $Y$ holdings (4). Its true utility is computed from these net flows, not from the identities' reported surpluses:
--
--   1. for a true sell-$Y$ type $(V,Q)$: $-\infty$ if $-\Delta_Y>Q$ or ($-\Delta_Y<0$ and $\Delta_X<0$), and $V\Delta_X+\Delta_Y$ otherwise (5);
--   2. for a true sell-$X$ type $(U,R)$: $-\infty$ if $-\Delta_X>R$ or ($-\Delta_X<0$ and $\Delta_Y<0$), and $\Delta_Y+U\Delta_X$ otherwise (6).
--
--   The catastrophic events are a net sale exceeding the true budget, and an aggregate trade strictly opposite to the trader's type.
--
--   **Formalization Note** Values in $\overline{\mathbb R}$ (`EReal`) with $-\infty$ the bottom element.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.2, (4)–(6), p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SybilClinch_flowX
import Definitions.Def_SybilClinch_flowY

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.2, (4)–(6), printed p.7 (PDF p.9): the true utility of a physical trader with true type
`t` whose identities are `D`, computed from its aggregate net flows `Δ_X = flowX D`,
`Δ_Y = −flowY D` (never from the identities' reported surpluses).

* True sell-`Y` type `(V, Q)`: `−∞` if `−Δ_Y > Q` or (`−Δ_Y < 0` and `Δ_X < 0`); else `V·Δ_X + Δ_Y`.
* True sell-`X` type `(U, R)`: `−∞` if `−Δ_X > R` or (`−Δ_X < 0` and `Δ_Y < 0`); else `Δ_Y + U·Δ_X`.

**Formalization Note.** Values in `EReal`, with `−∞ = ⊥`; no arithmetic is done in `EReal`. -/
noncomputable def trueUtil (t : Report) (D : Finset ℕ) (rep : ℕ → Report) (f : ℕ → Fill) :
    EReal :=
  match t.dir with
  | Dir.sellY =>
      if t.bud < flowY D rep f ∨ (flowY D rep f < 0 ∧ flowX D rep f < 0) then ⊥
      else ((t.val * flowX D rep f - flowY D rep f : ℝ) : EReal)
  | Dir.sellX =>
      if t.bud < - flowX D rep f ∨ (- flowX D rep f < 0 ∧ - flowY D rep f < 0) then ⊥
      else ((- flowY D rep f + t.val * flowX D rep f : ℝ) : EReal)

end SybilClinch


