-- Prove2me | Definitions.Def_AvoidPlast_Supplement_strOf
-- name    : AvoidPlast_Supplement_strOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:59:10.293027+00:00
-- url     : https://prove2.me/theorems/f1739c36-f650-4e69-8b6a-0599377ce748
-- title:
--   The $k$-bit string of a number
-- statement:
--   The $k$-bit binary representation of $a$, least significant bit first; used to name the oracle query $y\in\{0,1\}^{\ell_{in}}$ with index $a$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), footnote 21, p.21

import Mathlib

namespace AvoidPlast.Supplement

/-- The `k`-bit binary string of the number `a`, least significant bit first (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
footnote 21, p.21: the oracle query `y ∈ {0,1}^{ℓin}`). -/
def strOf (k a : ℕ) : List Bool := List.ofFn fun j : Fin k => a.testBit j

end AvoidPlast.Supplement


