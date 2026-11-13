-- Prove2me | Definitions.Def_SaglamGV_Params
-- name    : SaglamGV_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:47:37.738516+00:00
-- url     : https://prove2.me/theorems/11dcbf91-e8dd-46e4-9857-63c4a33aa570
-- title:
--   Redundancy $R=\ln(2^n/V)$ and $\tau=V2^{-m}$
-- statement:
--   With $V=|B_d|$ the **redundancy parameter** is
--
--   $$
--   R=\ln\frac{2^n}{V},
--   $$
--
--   and for an integer $m\ge 0$ (the number of rows of a random parity-check matrix) the expected number of surviving low-weight words is
--
--   $$
--   \tau=V\,2^{-m}.
--   $$
--
--   In §2 the paper fixes $0<\zeta<1$ and chooses $m$ with $(1-\zeta)R/2\le\tau<(1-\zeta)R$; here $\tau$ is defined for every $m$ and that constraint is a hypothesis where it is used.
--
--   **Formalization Note** $\ln$ is `Real.log`. When $V=0$ (i.e. $d\le 1$) Lean's conventions give $R=0$ and $\tau=0$; every statement using $R$ or $\tau$ assumes $d\ge 2$. The binary entropy $H_2$ used in Appendix A is the published definition `SelectiveDPT.H2`.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.2 (R, τ)

import Mathlib
import Definitions.Def_SaglamGV_Code

namespace SaglamGV

/-- The redundancy parameter `R = ln(2ⁿ / V)` (M. Saglam, *Linear codes exceeding the
Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.2: "Define the redundancy parameter
R := ln (2^n / V)"), with `V = |B_d|`.

**Formalization Note** `ln` is `Real.log`. When `V = 0` (that is `d ≤ 1`) Lean's division and
logarithm return `0`; every statement using `R` assumes `d ≥ 2`. -/
noncomputable def redund (n d : ℕ) : ℝ := Real.log ((2 : ℝ) ^ n / (vol n d : ℝ))

/-- `τ = V 2^{−m}` (Saglam, §2, p.2: "choose the integer m so that, with τ := V 2^{−m}, we have
(1 − ζ)R/2 ≤ τ < (1 − ζ)R"). Here `τ` is defined for every `m`; the constraint on `m` is a
hypothesis wherever the paper imposes it. -/
noncomputable def tau (n d m : ℕ) : ℝ := (vol n d : ℝ) / (2 : ℝ) ^ m

end SaglamGV


