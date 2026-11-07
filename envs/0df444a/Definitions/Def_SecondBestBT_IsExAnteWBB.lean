-- Prove2me | Definitions.Def_SecondBestBT_IsExAnteWBB
-- name    : SecondBestBT_IsExAnteWBB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:36.233952+00:00
-- url     : https://prove2.me/theorems/ce595403-706a-4095-a76b-15b3c81a2d32
-- title:
--   Ex-ante weak budget balance
-- statement:
--   A mechanism is **ex-ante weakly budget balanced** (WBB) if the expected payment collected from the buyer is at least the expected payment to the seller:
--   $$
--   \int (p_B-p_S)\,dF_S\,dF_B\ \ge\ 0 .
--   $$
--   Independence of the two values is the product measure $F_S\otimes F_B$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Definition 2.1, p.4

import Mathlib
import Definitions.Def_SecondBestBT_Mechanism

open MeasureTheory

namespace SecondBestBT

/-- Ex-ante weak budget balance (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256
17184930…, Definition 2.1, p.4): the expected payment collected from the buyer is at least the
expected payment to the seller, `∫ (p_B − p_S) dF_S dF_B ≥ 0`.

**Formalization Note** Independence of the two values is the product measure `μS.prod μB`;
integrability of `p_B − p_S` is part of `WellDefined`. -/
def IsExAnteWBB (μS μB : Measure ℝ) (M : Mechanism) : Prop :=
  0 ≤ ∫ p : ℝ × ℝ, (M.pB p - M.pS p) ∂(μS.prod μB)

end SecondBestBT


