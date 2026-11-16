-- Prove2me | Definitions.Def_AFIsingKS_Supplement_secondMomentMain
-- name    : AFIsingKS_Supplement_secondMomentMain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:22:47.815188+00:00
-- url     : https://prove2.me/theorems/69e70f96-4ca5-4a61-9f89-64b4a69e1c6e
-- title:
--   Appendix B notation $h,\delta_2,K_\eta(\rho)$ and the main term of the second moment (129)
-- statement:
--   For $\beta\in\mathbb C$ put $p=e^\beta$, $q=e^{\bar\beta}$ (complex conjugate), $N=nd$,
--   $$h(\beta)=(1+p)(1+q),\qquad \delta_2(\beta)=\frac{p-1}{p+1}\cdot\frac{q-1}{q+1}=\Big|\tanh\frac\beta2\Big|^2 .$$
--   For $0<\eta<1$ and $\rho>0$, $K_\eta(\rho)=\{\beta\in\mathbb C:\operatorname{dist}(\beta,[0,(1-\eta)\beta_{\mathrm{KS}}])\le\rho\}$. The **main term** of the unconditioned truncated second moment is
--   $$R_n(\beta)=4^n\Big(\frac{h(\beta)}4\Big)^{N/2}\frac{\sqrt{h(\beta)}}{\sqrt{(d(p-1)+2)(d(q-1)+2)}}\cdot\frac1{\sqrt{1-(d-1)\delta_2(\beta)}} .$$
--
--   $R_n(\beta)$ is the right side of eq. (129) without its factor $1+O(1/n)$; at $\beta=0$ it equals $4^n$, the number of pairs of spin configurations.
--
--   **Formalization Note** Square roots are principal (`Complex.cpow` with exponent $1/2$). The radicands are $|1+e^\beta|^2$, $|d(e^\beta-1)+2|^2$ and $1-(d-1)|\tanh(\beta/2)|^2$, real and positive on $K_\eta(\rho)$ for small $\rho$, where the principal root is the positive root. $(h/4)^{N/2}$ is a natural power with exponent $nd/2$, exact when $nd$ is even.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Appendix B, p.66 (N, p, q, h, δ₂, K_η(ρ)); eq. (129), Theorem B.5, p.73

import Mathlib
import Definitions.Def_AFIsingKS_betaKS

open ComplexConjugate

namespace AFIsingKS.Supplement

/-- `h(β) = (1 + p)(1 + q)` with `p = e^β`, `q = e^{β̄}` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598
(held version, sha256 2a07c158…), Appendix B, p.66). It equals `|1 + e^β|²`. -/
noncomputable def hB (β : ℂ) : ℂ := (1 + Complex.exp β) * (1 + Complex.exp (conj β))

/-- `δ₂(β) = ((p − 1)/(p + 1)) · ((q − 1)/(q + 1)) = |tanh(β/2)|²`, `p = e^β`, `q = e^{β̄}`
(Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Appendix B, p.66).

**Formalization Note.** This is Appendix B's `δ₂`, with the conjugate in `q`; it is not the `δ_2` of p.10. -/
noncomputable def delta2B (β : ℂ) : ℂ :=
  (Complex.exp β - 1) / (Complex.exp β + 1) * ((Complex.exp (conj β) - 1) / (Complex.exp (conj β) + 1))

/-- `K_η(ρ) = {β ∈ ℂ : dist(β, [0, (1 − η) β_KS]) ≤ ρ}` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598
(held version, sha256 2a07c158…), Appendix B, p.66): the closed `ρ`-neighbourhood in `ℂ` of the real
segment. -/
def Keta (d : ℕ) (η ρ : ℝ) : Set ℂ :=
  {β | Metric.infDist β (((↑) : ℝ → ℂ) '' Set.Icc 0 ((1 - η) * betaKS d)) ≤ ρ}

/-- The main term of the unconditioned truncated second moment, the right side of eq. (129) without the
factor `1 + O(1/n)` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…),
Theorem B.5, p.73):
`4^n (h(β)/4)^{N/2} · √h(β) / √((d(p − 1) + 2)(d(q − 1) + 2)) · 1/√(1 − (d − 1) δ₂(β))`, `N = nd`.

**Formalization Note.** Square roots are `Complex.cpow · (1/2)`, the principal branch (the convention of the
base `firstMomentMain`). The three radicands are the real numbers `|1 + e^β|²`, `|d(e^β − 1) + 2|²` and
`1 − (d − 1)|tanh(β/2)|²`, positive on `K_η(ρ)` for small `ρ`, where the principal root is the positive one.
`(h/4)^{N/2}` is a natural power with exponent `(n * d) / 2`, exact when `nd` is even. -/
noncomputable def secondMomentMain (d n : ℕ) (β : ℂ) : ℂ :=
  (4 : ℂ) ^ n * (hB β / 4) ^ (n * d / 2) *
    (hB β ^ (1 / 2 : ℂ) /
      (((d : ℂ) * (Complex.exp β - 1) + 2) * ((d : ℂ) * (Complex.exp (conj β) - 1) + 2)) ^ (1 / 2 : ℂ)) *
    (1 / (1 - ((d : ℂ) - 1) * delta2B β) ^ (1 / 2 : ℂ))

end AFIsingKS.Supplement


