-- Prove2me | Definitions.Def_QuantumLTF_Membership_fpVal
-- name    : QuantumLTF_Membership_fpVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:01.250129+00:00
-- url     : https://prove2.me/theorems/94b3545d-d786-43d3-8ce5-81d09f7d28d2
-- title:
--   Signed fixed-point value of a bit string
-- statement:
--   A string $z$ of $\ell$ bits, read as the integer $N$ with wire $0$ most significant, denotes with $f$ fractional bits the signed fixed-point number
--   $$\mathrm{fp}_{\ell,f}(z)=\frac{N-2^{\ell}/2}{2^{f}}.$$
--   For $\ell\ge1$ the range is $[-2^{\ell-1},2^{\ell-1})/2^f$, a set containing $0$. The paper computes query addresses and heights in signed fixed-point arithmetic.
--
--   **Formalization Note** The paper fixes no encoding; this is offset binary. At $\ell=0$ the only value is $-2^{-f-1}$, which is one point and gives a circuit no extra power.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §3.1.1, Eq. (36), p. 22 (PDF p. 23); §3.1.2, Eq. (42), p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QuantumLTF.Membership

open QAlgorithms

/-- **Signed fixed-point value of a bit string.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §3.1.1, Eq. (36), p. 22 (PDF p. 23), and
§3.1.2, Eq. (42), p. 26 (PDF p. 27): the paper's numbers are "signed fixed-point". The string `z` of
`ℓ` bits, read as the integer `N = bitsToNat z` (wire `0` most significant), has the value
`(N − 2^ℓ / 2) / 2^f`, where `f` is the number of fractional bits. For `ℓ ≥ 1` the range is
`[−2^{ℓ−1}, 2^{ℓ−1}) / 2^f`, which contains `0`.

**Formalization Note.** The paper fixes no encoding; this one is offset binary. No natural-number
subtraction occurs. At `ℓ = 0` the only value is `−2^{−f−1}`, a single point, which gives a circuit
nothing it could not get from `ℓ = 1`. -/
noncomputable def fpVal (ℓ f : ℕ) (z : Qubits ℓ) : ℝ :=
  ((bitsToNat z : ℝ) - (2 : ℝ) ^ ℓ / 2) / (2 : ℝ) ^ f

end QuantumLTF.Membership


