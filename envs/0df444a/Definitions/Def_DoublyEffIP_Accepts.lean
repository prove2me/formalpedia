-- Prove2me | Definitions.Def_DoublyEffIP_Accepts
-- name    : DoublyEffIP_Accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:08.100939+00:00
-- url     : https://prove2.me/theorems/6f9c8232-5b50-44d2-bee2-5b340915e8be
-- title:
--   Acceptance by a machine
-- statement:
--   A machine $M$ **accepts** the word $w$ if, started on $w$, it halts in the answer state $1$. For the verifier of a protocol, accepting is the output $\langle P(x),V(y;q)\rangle[\mathrm{pp}]\neq\bot$, and halting with answer $0$ is $\bot$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.11 (the verifier's output, ⊥)

import Mathlib
import Definitions.Def_DoublyEffIP_HaltsAt

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP

/-- **Acceptance** — the verifier's output `⟨P(x), V(y; q)⟩[pp] ≠ ⊥` in Chen–Hong–Kalai–Xi,
*Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02,
sha256 14d170db…), Section 3.4, p.11.

Started on `input`, the machine `M` halts in the answer state `true`.

**Formalization Note.** The verifier's output is its answer bit: `true` is "not `⊥`" (accept),
`false` is `⊥` (reject), and a machine that never halts does not accept. -/
def Accepts (M : PrimitiveMachine) (input : List Bool) : Prop :=
  ∃ (t : ℕ) (final : SqrtLogSpace.LocatedCfg M),
    HaltsAt M input t final ∧ final.config.state = Sum.inl true

end DoublyEffIP


