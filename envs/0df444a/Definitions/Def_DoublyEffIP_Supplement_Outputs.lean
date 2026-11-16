-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_Outputs
-- name    : DoublyEffIP_Supplement_Outputs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:33:08.784041+00:00
-- url     : https://prove2.me/theorems/9525e6ff-3657-45bc-b309-8f9ae74a5f8a
-- title:
--   The verifier outputs a word (does not reject)
-- statement:
--   A machine **outputs** the word $y$ on input $w$ if, started on $w$, it halts in the accepting answer state with exactly $y$ on its designated output tape. Halting in the rejecting answer state is the output $\bot$.
--
--   This expresses $\langle P(x),V\rangle[\mathrm{pp}]=\langle\Psi\rangle$ and $=(\langle Q\rangle,\langle\Psi\rangle)$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Definition 8, p.11; Definition 9, p.12

import Mathlib
import Definitions.Def_DoublyEffIP_HaltsAt

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **The verifier outputs a word (does not reject)** — `⟨P(x), V⟩[pp] = ⟨Ψ⟩` (Definition 8,
p.11) and `= (⟨Q⟩, ⟨Ψ⟩)` (Definition 9, p.12) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), with `⊥` for rejection (p.11).

Started on `input`, the machine `M` halts in the accepting answer state with exactly the word `y`
on its tape `out` (head on its first cell, blanks elsewhere).

**Formalization Note.** Halting in the answer state `false` is `⊥`. -/
def Outputs (M : PrimitiveMachine) (out : Fin M.tapeCount) (input y : List Bool) : Prop :=
  ∃ (t : ℕ) (final : SqrtLogSpace.LocatedCfg M), HaltsAt M input t final ∧
    final.config.state = Sum.inl true ∧ final.config.tapes out = Turing.Tape.mk₁ (y.map some)

end DoublyEffIP.Supplement


