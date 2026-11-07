-- Prove2me | Definitions.Def_QuantumLTF_Membership_IsFp
-- name    : QuantumLTF_Membership_IsFp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:01.045083+00:00
-- url     : https://prove2.me/theorems/e04b2aed-9a3b-45cd-af97-2e28a14dc821
-- title:
--   A number is exactly a $B$-bit signed fixed-point number
-- statement:
--   A real $x$ is a signed fixed-point number of $B$ bits with $f$ fractional bits if $f\le B$ and $x=k/2^f$ for an integer $k$ with $|k|<2^B$. This expresses the paper's "represented exactly in signed fixed-point form using $O(\log(L_\epsilon/\zeta))$ bits".
--
--   **Formalization Note** $f\le B$ because the bit count includes the fractional bits (Eq. (37)).
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.1, p. 21 (PDF p. 22); Eq. (37), p. 22 (PDF p. 23)

import Mathlib

namespace QuantumLTF.Membership

/-- **`x` is exactly a signed fixed-point number of `B` bits with `f` fractional bits.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331,
Theorem 3.1, p. 21 (PDF p. 22): "represented exactly in signed fixed-point form using O(log(L_ϵ/ζ))
bits"; Eq. (37), p. 22 (PDF p. 23), counts integer and fractional bits together.

**Formalization Note.** `f ≤ B`: the `B` bits include the `f` fractional ones. Without it a tiny value
could carry an unbounded `f`, and the address arithmetic of Theorem 3.2 could not be bounded. -/
def IsFp (B f : ℕ) (x : ℝ) : Prop :=
  f ≤ B ∧ ∃ k : ℤ, |k| < (2 : ℤ) ^ B ∧ x = (k : ℝ) / (2 : ℝ) ^ f

end QuantumLTF.Membership


