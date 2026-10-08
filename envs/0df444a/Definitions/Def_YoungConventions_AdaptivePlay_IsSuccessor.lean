-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_IsSuccessor
-- name    : YoungConventions_AdaptivePlay_IsSuccessor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:40.367404+00:00
-- url     : https://prove2.me/theorems/ca0d55d5-9736-4c08-b099-f5e2c777e0d4
-- title:
--   Successor of a state (§3, p. 61)
-- statement:
--   A **successor** of a state $h \in H$ is any state $h' \in H$ obtained by deleting the left-most (oldest) element of $h$ and adjoining a new right-most element. In terms of positions,
--   $$h'_t = h_{t+1} \qquad \text{for } 0 \le t < m - 1,$$
--   while the right-most entry $h'_{m-1}$, the new play, is arbitrary.
--
--   Adaptive play moves from a state only to its successors.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §3, p. 61 (PDF p. 6), displayed definition 'Successor'

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History

namespace YoungConventions.AdaptivePlay

/-- **Successor of a state** (Young 1993, *The Evolution of Conventions*, Econometrica 61:57–84,
§3, p. 61, PDF p. 6, displayed definition "Successor"): "A *successor* of a state `h ∈ H` is any
state `h′ ∈ H` obtained by deleting the left-most element of `h` and adjoining a new right-most
element."

`IsSuccessor h h'` holds iff `h′ₜ = hₜ₊₁` for every position `t` with `t + 1 < m`; the right-most
entry `h′_{m−1}` (the new play) is arbitrary.

**Formalization Note.** Position `0` is the oldest play (see `History`). -/
def IsSuccessor {ι : Type*} {S : ι → Type*} {m : ℕ} (h h' : History S m) : Prop :=
  ∀ t : Fin m, ∀ ht : t.val + 1 < m, h' t = h ⟨t.val + 1, ht⟩

end YoungConventions.AdaptivePlay


