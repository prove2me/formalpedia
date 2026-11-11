-- Prove2me | Definitions.Def_PermInvCC_Rpub
-- name    : PermInvCC_Rpub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:25:48.096947+00:00
-- url     : https://prove2.me/theorems/dc9331ae-99c8-4778-b8d9-de98d14c896d
-- title:
--   Public-coin randomized communication complexity $R^{\mathrm{pub}}(f)$
-- statement:
--   $R^{\mathrm{pub}}(f)$ is the minimum worst-case number of communicated classical bits in an interactive public-coin protocol that computes $f$ with error at most $1/3$ on each promised input:
--   $$R^{\mathrm{pub}}(f)=\min\bigl\{\mathrm{cost}(\Pi):\ \Pr[\Pi(x,y)\ne f(x,y)]\le 1/3\ \text{whenever } f(x,y)\ne *\bigr\}.$$
--
--   It is the left-hand side of the main Theorem 1.1.
--
--   **Formalization Note** The protocol output is transcript-determined (both parties know it); this can only raise the complexity, by at most one bit. The defining set is nonempty for finite inputs (Alice can send her input).
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.1, p.9

import Mathlib
import Definitions.Def_PermInvCC_PubProtocol

namespace PermInvCC

/-- The **public-coin randomized communication complexity** `R^pub(f)` (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.1, p.9): the minimum worst-case
number of communicated bits of an interactive public-coin protocol that computes `f` with error at
most `1/3` on each promised input.

**Formalization Note.** The output is transcript-determined (both parties know it), which can
cost at most one more bit than Bob alone outputting (p.9). `sInf ∅ = 0` for natural numbers, but
the set is never empty on finite inputs (Alice sends her input bit by bit and the leaf holds the
answer). -/
noncomputable def Rpub {X Y : Type} (f : X → Y → Option Bool) : ℕ :=
  sInf {c : ℕ | ∃ P : PubProtocol X Y Bool, P.cost ≤ c ∧
    ∀ x y b, f x y = some b → P.prob x y (fun o => o ≠ b) ≤ 1 / 3}

end PermInvCC


