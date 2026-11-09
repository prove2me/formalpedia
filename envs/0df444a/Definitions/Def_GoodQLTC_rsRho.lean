-- Prove2me | Definitions.Def_GoodQLTC_rsRho
-- name    : GoodQLTC_rsRho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:45.214412+00:00
-- url     : https://prove2.me/theorems/b2c20a5f-d7bc-4715-b757-9f93de1242d4
-- title:
--   Product-expansion constant $\rho(t,\tau,\epsilon)$ (Equation (13.1))
-- statement:
--   With $m=t-2$, $c=t2^t$, $a=\lceil t\tau\rceil$, $p_0=0$, $p_d=dp_{d-1}+1$, and $B=2ta+4c\sum_{d=1}^md!(2a)^dt^{d-1}$, the integer $C=C(t,\tau)=taB^{p_m}$ (proof of Theorem 12.2), and
--   $$
--   \theta=\frac{\epsilon}{2^tC},\qquad \rho=\frac1t\Big(\frac\theta\tau\Big)^t. \tag{13.1}
--   $$
--   It is positive for $t\ge1$, $\tau\ge1$, $\epsilon>0$ (proved in the sanity file).
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Equation (13.1), p.48 (PDF p.51); C from the proof of Theorem 12.2, p.46 (PDF p.49)

import Mathlib

namespace GoodQLTC

/-- `p_0 := 0`, `p_d := d p_{d−1} + 1` (arXiv:2609.20780, proof of Theorem 12.2, p.46). -/
def pSeq : ℕ → ℕ
  | 0 => 0
  | d + 1 => (d + 1) * pSeq d + 1

/-- The integer `C = C(t, τ) ≥ 1` chosen in the proof of Theorem 12.2, Gay–Jeronimo,
arXiv:2609.20780 (held version), p.46: with `m := t − 2`, `c := t 2^t`, `a := ⌈tτ⌉`,
`B := 2ta + 4c ∑_{d=1}^{m} d! (2a)^d t^{d−1}`, it is `C := t a B^{p_m}`. -/
noncomputable def rsConstC (t : ℕ) (τ : ℝ) : ℕ :=
  let a := ⌈(t : ℝ) * τ⌉₊
  let c := t * 2 ^ t
  let B := 2 * t * a + 4 * c * ∑ d ∈ Finset.Icc 1 (t - 2), d.factorial * (2 * a) ^ d * t ^ (d - 1)
  t * a * B ^ pSeq (t - 2)

/-- The product-expansion constant of Equation (13.1), Gay–Jeronimo, arXiv:2609.20780 (held
version), p.48: `θ := ε/(2^t C)` and `ρ := (1/t)(θ/τ)^t`, with `C = C(t, τ)` from p.46. -/
noncomputable def rsRho (t : ℕ) (τ ε : ℝ) : ℝ :=
  (1 / (t : ℝ)) * ((ε / (2 ^ t * (rsConstC t τ : ℝ))) / τ) ^ t

end GoodQLTC


