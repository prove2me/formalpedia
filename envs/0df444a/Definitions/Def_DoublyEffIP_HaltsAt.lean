-- Prove2me | Definitions.Def_DoublyEffIP_HaltsAt
-- name    : DoublyEffIP_HaltsAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:03.61737+00:00
-- url     : https://prove2.me/theorems/cad47c0b-5794-4a6d-835a-606d6b7c35bf
-- title:
--   A halting run of exactly $t$ steps
-- statement:
--   A machine $M$ **halts at step $t$** on an input word $w$ with final configuration $c$ if, started with $w$ on its input tape, it reaches $c$ after exactly $t$ steps and $c$ is a halting configuration (its state is an answer bit). A halting configuration has no successor, so $t$ is the running time of $M$ on $w$.
--
--   All time bounds of the mission are stated through this predicate.
--
--   **Formalization Note** The paper never fixes its machine model ("a Turing machine"). The machine is the published `PrimitiveMachine` of `SubexponentialSAT`: a deterministic multitape machine over the alphabet $\{\sqcup,0,1\}$; runs are tracked with `locatedStep`, which also records the visited cells of each tape.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3, p.8; Section 3.4, p.10 (machine model)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DoublyEffIP

/-- **A halting run of exactly `t` steps** — the machine model behind "a Turing machine" in
Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799 (version of
2026-11-02, sha256 14d170db…), Section 3, p.8, and Section 3.4, p.10.

Started on `input`, the machine `M` reaches the configuration `final` after exactly `t` steps, and
`final` is halted (its state is an answer `Sum.inl b`). Since a halted configuration has no
successor, `t` is the running time of `M` on `input`.

**Formalization Note.** The paper fixes no machine model. The model is the published
`SubexponentialSAT` one: `PrimitiveMachine`, a deterministic multitape machine over the tape
alphabet `Option Bool` (blank, 0, 1), whose input is written on its input tape; `locatedStep`
runs it while recording the visited cells of every tape. -/
def HaltsAt (M : PrimitiveMachine) (input : List Bool) (t : ℕ) (final : LocatedCfg M) : Prop :=
  Trace (locatedStep M) t (locatedInit M input) final ∧ ∃ b : Bool, final.config.state = Sum.inl b

end DoublyEffIP


