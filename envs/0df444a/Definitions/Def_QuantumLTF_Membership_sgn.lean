-- Prove2me | Definitions.Def_QuantumLTF_Membership_sgn
-- name    : QuantumLTF_Membership_sgn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:31:45.094936+00:00
-- url     : https://prove2.me/theorems/ef352462-bce3-4f8a-96da-aa89275e8a4f
-- title:
--   The sign convention $\mathrm{sign}(0)=+1$
-- statement:
--   For a real number $t$,
--   $$\mathrm{sign}(t)=\begin{cases}1,&t\ge 0,\\-1,&t<0.\end{cases}$$
--   This convention decides the value of a linear threshold function on its boundary hyperplane, and the binary searches of the paper use it when a query lands exactly on the boundary.
--
--   **Formalization Note** This is not Mathlib's `Real.sign`, which is $0$ at $0$. The values are the integers $\pm 1$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §2.1, unnumbered, p. 15 (PDF p. 16)

import Mathlib

namespace QuantumLTF.Membership

/-- **The sign convention.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §2.1, unnumbered, p. 15 (PDF p. 16): "sign(t) := 1 for t ≥ 0, −1
for t < 0".

**Formalization Note.** Not `Real.sign`, which is `0` at `0`; the proofs on pp. 22 and 25 rely on
`sign(0) = +1`. Values are the integers `1` and `-1`. -/
noncomputable def sgn (t : ℝ) : ℤ := if 0 ≤ t then 1 else -1

end QuantumLTF.Membership


