-- Prove2me | Definitions.Def_AvoidPlast_Supplement_blockOf
-- name    : AvoidPlast_Supplement_blockOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:56.673843+00:00
-- url     : https://prove2.me/theorems/f6dca403-d369-408f-b285-de28d793481c
-- title:
--   Blocks of a string
-- statement:
--   For $s=s_1\circ s_2\circ\cdots$ with blocks of $n$ bits, the block $s_{i+1}$ (blocks numbered from $0$).
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 6.5, 7.2, pp.34, 40

import Mathlib

namespace AvoidPlast.Supplement

/-- The `i`-th `n`-bit block `s_{i+1}` of a string `s = s_1 ∘ s_2 ∘ …` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 6.5,
p.34; Theorem 7.2, p.40, the blocks of a generator's output). Blocks are numbered from `0`. -/
def blockOf (s : List Bool) (n i : ℕ) : List Bool := (s.drop (i * n)).take n

end AvoidPlast.Supplement


