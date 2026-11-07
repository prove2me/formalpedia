-- Prove2me | Definitions.Def_NoPerfectRandComp_W
-- name    : NoPerfectRandComp_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:37.946825+00:00
-- url     : https://prove2.me/theorems/4cf05f89-492d-491b-9846-ca152ef81556
-- title:
--   The total outer function $W_q$ (Definition 4.7)
-- statement:
--   Fix a private cell encoding of the alphabet $\{0,1\}\times W_q^{c_q}$ in $36a_q$ bits. The **total outer function** $W_q(X, Y)$ is one if there exists an address $y \in \{0,1\}^{c_q}$ such that the cell $Y_y$ decodes to a flag of one and witnesses verifying $S_q(X_i) = y_i$ for every $i$; its value is zero otherwise.
--
--   It is a total Boolean rule: if any address accepts, all cores are defined and the accepting address is their answer vector. Weak evidence about the cores is cheap to obtain, while an exact certificate can be checked at the cost of one cell.
--
--   **Formalization Note** The encoding is a parameter of $W_q$ (see the encoding definition); the paper fixes one admissible choice.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Definition 4.7, p.16

import Mathlib
import Definitions.Def_NoPerfectRandComp_rq
import Definitions.Def_NoPerfectRandComp_witVerifies
import Definitions.Def_NoPerfectRandComp_Encoding
import Definitions.Def_NoPerfectRandComp_WCell
import Definitions.Def_NoPerfectRandComp_WIdx

namespace NoPerfectRandComp

open Classical in
/-- The total outer function `W_q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Definition 4.7, p.16): `W_q(X, Y) = 1` if there
exists an address `y ∈ {0,1}^{c_q}` such that the cell `Y_y` decodes to a flag of one and
witnesses verifying `S_q(X_i) = y_i` for every `i`; its value is zero otherwise.

**Formalization Note** The cell encoding `enc` (private linear map plus surjective decoder) is a
parameter; the paper fixes one admissible choice. `X_i` is the block `x (Sum.inl (i, ·))`. -/
noncomputable def W (q : ℕ) (enc : Encoding (aq q) (WCell q)) (x : WIdx q → Bool) : Bool :=
  decide (∃ y : Fin (cq q) → Bool,
    (enc.decode (fun t => x (Sum.inr (y, t)))).1 = true ∧
    ∀ i, witVerifies (kq q) (rq q) (uq q) (fun p => x (Sum.inl (i, p))) (y i)
      ((enc.decode (fun t => x (Sum.inr (y, t)))).2 i))

end NoPerfectRandComp


