-- Prove2me | Definitions.Def_SecondBestBT_IsInterimIR
-- name    : SecondBestBT_IsInterimIR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:14.318967+00:00
-- url     : https://prove2.me/theorems/69b34153-ab9d-42df-9454-9678fb8d89c7
-- title:
--   Interim individual rationality on $T$
-- statement:
--   A mechanism is **interim individually rational** (IR) on the type set $T$ if both agents obtain nonnegative interim expected utility from participating:
--   $$
--   u_B(b,b)\ge0\quad\text{and}\quad u_S(s,s)\ge0\qquad\text{for every } b,s\in T .
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 2, p.4

import Mathlib
import Definitions.Def_SecondBestBT_uB
import Definitions.Def_SecondBestBT_uS

open MeasureTheory

namespace SecondBestBT

/-- Interim individual rationality on the type set `T` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 2, p.4): `u_B(b, b) ≥ 0` and `u_S(s, s) ≥ 0` for every
`b, s ∈ T`.

**Formalization Note** As for `IsBIC`, the constraints hold at every type of `T`. -/
def IsInterimIR (T : Set ℝ) (μS μB : Measure ℝ) (M : Mechanism) : Prop :=
  (∀ b ∈ T, 0 ≤ uB μS M b b) ∧ (∀ s ∈ T, 0 ≤ uS μB M s s)

end SecondBestBT


