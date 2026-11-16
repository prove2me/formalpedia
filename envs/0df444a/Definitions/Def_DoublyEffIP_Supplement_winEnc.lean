-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_winEnc
-- name    : DoublyEffIP_Supplement_winEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:39:31.400248+00:00
-- url     : https://prove2.me/theorems/37cbd45c-e731-4522-825a-e69fbe7d8b4f
-- title:
--   A configuration as a bit string
-- statement:
--   A space-$S$ configuration is encoded as its state in one-hot form over $\mathrm{stateCount}+2$ positions (rejecting answer, accepting answer, then the control states), followed, for each tape and each window cell, by three bits: the head is here, the cell is non-blank, the cell's value. Its length is $w(M,S)$.
--
--   The encoding is injective and local: each bit of a successor configuration depends on a bounded number of bits.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4.1, p.14 (configurations as strings in {0,1}^S)

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_WinCfg
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **A configuration as a bit string** — the configurations as strings in `{0,1}^{S(n)}` of
Section 4.1 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.14.

The state in one-hot form over `stateCount + 2` positions (answer `false`, answer `true`, then the
control states), then for each tape and each window cell three bits: head here, cell non-blank,
cell value. Its length is `winWidth M S`.

**Formalization Note.** The encoding is injective and local (each bit of a successor configuration
depends on a bounded number of bits), the property the source's circuits for transitions use. -/
def winEnc {M : PrimitiveMachine} {S : ℕ} (c : WinCfg M S) : List Bool :=
  List.ofFn (fun r : Fin (M.stateCount + 2) =>
      decide ((match c.state with
        | .inl false => 0
        | .inl true => 1
        | .inr q => q.val + 2) = r.val)) ++
    (List.ofFn fun i : Fin M.tapeCount => (List.ofFn fun j : Fin (2 * S + 1) =>
      [decide (c.head i = j), (c.cells i j).isSome, (c.cells i j).getD false]).flatten).flatten

end DoublyEffIP.Supplement


