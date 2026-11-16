-- Prove2me | Definitions.Def_TetraOT_Supplement_idealDealM
-- name    : TetraOT_Supplement_idealDealM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:37:24.587429+00:00
-- url     : https://prove2.me/theorems/f99ba213-471a-4902-b8b0-5be870507258
-- title:
--   The ideal $(2,1;1)$ deal with Alice's message announced to Bob
-- statement:
--   Let $\rho$ be a uniformly random permutation of $\{0,1,2,3\}$. The $(2,1;1)$ deal (Definition 2.2) gives Alice the ordered pair $(\rho(0),\rho(1))$, gives Bob the card $\rho(2)$, and discards $\rho(3)$. This functionality also gives Bob the message $M = A(\rho(0),\rho(1))_1$ that Alice's Tetrahedral table (Fig. 2) assigns to her hand. It is the law of
--   $$\big((\rho(0),\rho(1)),\ (\rho(2), M)\big).$$
--   Its marginal on $((\rho(0),\rho(1)),\rho(2))$ is the uniform $(2,1;1)$ deal.
--
--   It is the ideal functionality of the corrected Theorem 5.1. Without $M$ the bare deal cannot be realized by the inverted protocol against a semi-honest Bob, because $M$ is part of his view and reveals information about Alice's hand.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Definition 2.2, p.2; Theorem 5.1, p.5 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_tetrahedralRun

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- **The ideal (2, 1; 1) deal, with Alice's Tetrahedral message announced to Bob** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Definition 2.2,
p.2, and Theorem 5.1, p.5; p. = PDF page, the PDF has no printed page numbers). A uniform permutation
`ρ ∈ S₄` is drawn (the published `TetraOT.deal`); Alice receives `(ρ(0), ρ(1))`, Bob receives `ρ(2)`, and
`ρ(3)` is discarded: this is the (2, 1; 1) deal. In addition Bob receives `M = A(ρ(0), ρ(1)).1`, the
message of Alice's table (Fig. 2) on her hand.

`idealDealM` is the law of `((ρ(0), ρ(1)), (ρ(2), M))`. Its marginal on `((ρ(0), ρ(1)), ρ(2))` is the
(2, 1; 1) deal.

**Formalization Note.** Delivering `M` to Bob is the minimal correction of Theorem 5.1: in the protocol
of Fig. 10, Bob's view `(M, y₀y₁)` is in bijection with `(ρ(2), M)`, and `M` reveals information about
Alice's hand (with `ρ(2) = 0` and `M = Y` Alice never holds `{1, 3}`), so the bare deal is not realized
against a semi-honest Bob. -/
noncomputable def idealDealM : PMF ((Fin 4 × Fin 4) × (Fin 4 × Msg)) :=
  deal.map (fun ρ => ((ρ 0, ρ 1), (ρ 2, (aliceTable (ρ 0) (ρ 1)).1)))

end TetraOT.Supplement


