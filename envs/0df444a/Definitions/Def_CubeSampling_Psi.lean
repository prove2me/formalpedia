-- Prove2me | Definitions.Def_CubeSampling_Psi
-- name    : CubeSampling_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:15.781666+00:00
-- url     : https://prove2.me/theorems/d6e41c7f-79bf-48e1-9d7f-d595bbf59637
-- title:
--   The uncertainty curve $\Psi(q) = \log 2 - H_2\bigl(\tfrac12 - \sqrt{q(1-q)}\bigr)$
-- statement:
--   With $H_2(u) = -u\log u - (1-u)\log(1-u)$ the binary entropy in natural logarithms ($0 \log 0 = 0$), the **uncertainty curve** is
--   $$
--   \Psi(q) = \log 2 - H_2\Bigl(\frac12 - \sqrt{q(1-q)}\Bigr), \qquad q \in [0, 1/2].
--   $$
--
--   **Formalization Note** $H_2$ is Mathlib's binary entropy `Real.binEntropy` (natural logarithm).
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.4

import Mathlib

namespace CubeSampling

/-- The uncertainty curve `Ψ(q) = log 2 − H₂(1/2 − √(q(1 − q)))`, `q ∈ [0, 1/2]` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.4),
with `H₂(u) = −u log u − (1 − u) log(1 − u)` the binary entropy in natural logarithms and
`0 log 0 = 0` (Mathlib's `Real.binEntropy`). -/
noncomputable def Psi (q : ℝ) : ℝ := Real.log 2 - Real.binEntropy (1 / 2 - Real.sqrt (q * (1 - q)))

end CubeSampling


