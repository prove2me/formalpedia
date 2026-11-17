-- Prove2me | Definitions.Def_AvoidPlast_Supplement_oracleTable
-- name    : AvoidPlast_Supplement_oracleTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:59:40.582589+00:00
-- url     : https://prove2.me/theorems/7443cc45-2c4d-4ac9-afa7-050a9bdd1bd4
-- title:
--   Oracle access to $C_x$ as a read-only tape
-- statement:
--   The oracle $C_x$ is presented to a verifier as a read-only random-access tape: the cell with address $\langle a,i\rangle$ (Cantor pairing) holds bit $i$ of $C_x(y_a)$, where $y_a$ is the $\ell_{in}(|x|)$-bit string of $a$.
--
--   **Formalization Note** In the source the verifier writes a query on its work tape and reads the $m(n)$-bit answer once. Here it writes the address $\langle a,i\rangle$ on the index tape of the oracle tape (work space as well) and jumps to it. The two models simulate each other with polynomial time overhead and $O(\log n)$ extra space when $\ell_{out}(n)\le n$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.1 item 1 and footnote 21, p.21; footnote 22, p.23

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_strOf

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The oracle `C_x` as a read-only random-access tape (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.1 item 1 and
footnote 21, p.21; footnote 22, p.23): position `⟨a, i⟩` (Cantor pairing `Nat.pair`) holds bit
`i` of `C_x(y)`, where `y` is the `ℓin(|x|)`-bit string of `a`; positions outside the queries
hold `0`.

**Formalization Note** The source's oracle machine writes the query `y` on a work tape (so it
counts as space) and scans the answer read-once. Here the machine writes the address `⟨a, i⟩` on
the index tape of this tape (also work space) and jumps. The two models simulate each other with
polynomial time overhead and `O(log n)` extra space for `ℓout ≤ n`. -/
noncomputable def oracleTable (C : List Bool → List Bool → List Bool) (ℓin ℓout : ℕ → ℕ)
    (x : List Bool) : List Bool :=
  List.ofFn fun p : Fin ((2 ^ ℓin x.length + ℓout x.length) ^ 2) =>
    if (Nat.unpair p).1 < 2 ^ ℓin x.length then
      (C x (strOf (ℓin x.length) (Nat.unpair p).1)).getD (Nat.unpair p).2 false
    else false

end AvoidPlast.Supplement


