-- Prove2me | Definitions.Def_OracleStateHSP_dotG
-- name    : OracleStateHSP_dotG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:39.503299+00:00
-- url     : https://prove2.me/theorems/0ac484cc-00c7-4c23-83e9-f0e057fc7e11
-- title:
--   Dot product $x \cdot y$ on $\mathbb Z_2^r \oplus \mathbb Z_2^m$
-- statement:
--   For $x = (k, v)$ and $y = (k', v')$ in $G = \mathbb Z_2^r \oplus \mathbb Z_2^m$,
--   $$
--   x \cdot y = \sum_{i} k_i k'_i + \sum_j v_j v'_j \in \mathbb Z_2 ,
--   $$
--   the exponent of the Hadamard transform $H^{\otimes n}_{x,y} = 2^{-n/2}(-1)^{x \cdot y}$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.3, p.39 (Hadamard gates on the group register)

import Mathlib
import Definitions.Def_OracleStateHSP_V
import Definitions.Def_OracleStateHSP_K

namespace OracleStateHSP

/-- The dot product `x · y = ∑_i x_i y_i ∈ Z_2` on `G = Z_2^r ⊕ Z_2^m` (both blocks), the exponent
in the Hadamard transform `H^{⊗n}_{x,y} = 2^{−n/2} (−1)^{x·y}` of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.39. -/
def dotG {r m : ℕ} (x y : K r × V m) : ZMod 2 :=
  (∑ i, x.1 i * y.1 i) + ∑ j, x.2 j * y.2 j

end OracleStateHSP


