-- Prove2me | Definitions.Def_ErlerGross_defs
-- name    : ErlerGross_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T19:12:00.086989+00:00
-- url     : https://prove2.me/theorems/9531cd45-b337-4333-a7e6-89d2b620171a
-- title:
--   Erler–Gross midpoint identity: Neumann constants $A_k$, $m_{2n}$, $\beta_k$, (B.3) terms, $\kappa$-integrand
-- statement:
--   Definitions for the midpoint identity (A.8) of Erler–Gross (hep-th/0406199).
--
--   * **$A_k$** (`neumannA`): the constants defined by the expansion $$\left(\frac{1+iz}{1-iz}\right)^{1/3}=\exp\left(\tfrac{2i}{3}\tan^{-1}z\right)=1+\sum_{n\ge1}A_{2n}z^{2n}+i\sum_{n\ge1}A_{2n-1}z^{2n-1}.$$ For real $z$ the left side is $\cos(\tfrac23\arctan z)+i\sin(\tfrac23\arctan z)$, so $A_k$ is the $k$-th Taylor coefficient at $0$ of $\cos(\tfrac23\arctan z)$ for even $k$ and of $\sin(\tfrac23\arctan z)$ for odd $k$ (written as $f^{(k)}(0)/k!$).
--   * **$m_{2n}$** (`neumannMEven n`): $m_{2n}=-\tfrac23\,A_{2n}/\sqrt{2n}$ (Appendix B, p. 44; the source's left side $m_{2m}$ is a typo for $m_{2n}$).
--   * **$\beta_k$** (`betaVec k`): $\beta_k=\cos(k\pi/2)/\sqrt{k}$ (Appendix A, below eq. A.1), used for $k\ge1$.
--   * **(B.3) term** (`b3Term n`): $\frac{2}{2n-1}-\frac{1}{2n-2/3}-\frac{1}{2n-4/3}$, used for $n\ge1$.
--   * **$\kappa$-integrand** (`kappaIntegrand`): $\frac{1-\cosh(\pi\kappa/2)}{1+2\cosh(\pi\kappa/2)}\cdot\frac{1}{2\kappa\sinh(\pi\kappa/2)}$ (Appendix B, p. 45); its value at the removable point $\kappa=0$ is Lean's junk value $0$, irrelevant for the integral.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix A (below eq. A.1, eq. A.8), Appendix B pp. 44-46 (formula for $m_{2n}$, expansion defining $A_n$, eq. B.3)

import Mathlib

/-!
# Erler–Gross (hep-th/0406199): definitions for the midpoint identity (A.8)

Definitions used by the statements in `RequestProject/ErlerGross/Statements.lean`.
Source: T. G. Erler, D. J. Gross, *Locality, Causality, and an Initial Value Formulation
for Open String Field Theory*, arXiv:hep-th/0406199v2, Appendix A (eqs. A.2, A.5, A.8)
and Appendix B.
-/

namespace ErlerGross

open Real

/-- The constants `A_k` of Appendix B, defined through the expansion
`((1 + i z)/(1 - i z))^{1/3} = exp((2i/3) arctan z) = 1 + ∑ A_{2n} z^{2n} + i ∑ A_{2n-1} z^{2n-1}`.
For real `z` the left side equals `cos((2/3) arctan z) + i sin((2/3) arctan z)`, so `A_k` is the
`k`-th Taylor coefficient at `0` of `cos((2/3) arctan z)` when `k` is even and of
`sin((2/3) arctan z)` when `k` is odd. (In particular `A_0 = 1`.) -/
noncomputable def neumannA (k : ℕ) : ℝ :=
  if Even k then
    iteratedDeriv k (fun x : ℝ => Real.cos (2 / 3 * Real.arctan x)) 0 / (k.factorial : ℝ)
  else
    iteratedDeriv k (fun x : ℝ => Real.sin (2 / 3 * Real.arctan x)) 0 / (k.factorial : ℝ)

/-- The even-mode Neumann vector `m_{2n} = -(2/3) A_{2n} / √(2n)` (Appendix B, p. 44; the
source prints the left side as `m_{2m}`, a typo for `m_{2n}`). The argument `n` is the
half-mode number, i.e. `neumannMEven n = m_{2n}`; only `n ≥ 1` is used. -/
noncomputable def neumannMEven (n : ℕ) : ℝ :=
  -(2 / 3) * neumannA (2 * n) / Real.sqrt (2 * n)

/-- The vector `β_k = cos(kπ/2)/√k` (Appendix A, below eq. A.1). Only `k ≥ 1` is used; at
`k = 0` Lean's convention `x / 0 = 0` gives the unused junk value `0`. -/
noncomputable def betaVec (k : ℕ) : ℝ :=
  Real.cos (k * π / 2) / Real.sqrt k

/-- The `n`-th term (`n ≥ 1`) of the series in eq. (B.3):
`2/(2n-1) - 1/(2n - 2/3) - 1/(2n - 4/3)`. -/
noncomputable def b3Term (n : ℕ) : ℝ :=
  2 / (2 * n - 1) - 1 / (2 * n - 2 / 3) - 1 / (2 * n - 4 / 3)

/-- The integrand of the `κ`-basis representation of `∑ 3 m_{2n} β_{2n}` (Appendix B, p. 45):
`(1 - cosh(πκ/2)) / (1 + 2 cosh(πκ/2)) · 1 / (2κ sinh(πκ/2))`. The integrand extends smoothly
to `κ = 0`; at that single point Lean's convention `x / 0 = 0` gives the value `0`, which does
not affect the integral. -/
noncomputable def kappaIntegrand (κ : ℝ) : ℝ :=
  (1 - Real.cosh (π * κ / 2)) / (1 + 2 * Real.cosh (π * κ / 2)) *
    (1 / (2 * κ * Real.sinh (π * κ / 2)))

end ErlerGross


