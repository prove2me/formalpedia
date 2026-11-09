-- Prove2me | Definitions.Def_PhiSobBayes_phiDiv
-- name    : PhiSobBayes_phiDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:20.328848+00:00
-- url     : https://prove2.me/theorems/facdf2d2-d9e3-48d5-8afa-9afb91be08eb
-- title:
--   $\Psi$-divergence $D_\Psi(\nu\|\mu)$
-- statement:
--   Let $\Psi:J\to\mathbb R$ be convex and $\nu\ll\mu$ probability measures such that $d\nu/d\mu$ takes values in $J$. The **$\Psi$-divergence** is
--   $$D_\Psi(\nu\|\mu)=\mathbb E_\mu\,\Psi\Big(\frac{d\nu}{d\mu}\Big).$$
--   For $\Psi(z)=(z-1)^2$ and $\Psi(z)=z\log z$ it is the $\chi^2$-divergence and the relative entropy.
--
--   It appears in the contraction milestone (Fact A.25), which drives the forward direction of the goal.
--
--   **Formalization Note** Defined as $\int\big(\Psi(r)-\Psi'(1)(r-1)\big)\,d\mu\in[0,\infty]$ with $r=d\nu/d\mu$ (`Measure.rnDeriv`). For probability measures $\nu\ll\mu$ one has $\mathbb E_\mu(r-1)=0$, so this equals $\mathbb E_\mu\Psi(r)$ whenever that integral is defined. The integrand is nonnegative when $r,1\in J$ and $\Psi$ is convex, so the truncation at $0$ removes nothing there.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 12, p.56 (PDF 56); Section 6.1, p.31 (PDF 31)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- The **Ψ-divergence** `D_Ψ(ν ‖ μ) = 𝔼_μ Ψ(dν/dμ)`, in `[0, ∞]`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Definition 12, p.56 (PDF 56): "For a convex Φ : 𝐽 → ℝ and probability measures 𝜈 ≪ 𝜇
such that d𝜈/d𝜇 takes values in 𝐽, the Φ-divergence is 𝐷Φ(𝜈∥𝜇) = 𝔼𝜇Φ(d𝜈/d𝜇)"; recalled with
`Ψ(1) = 0` in Section 6.1, p.31 (PDF 31).

**Formalization Note** Defined as `∫⁻ ofReal(Ψ(r) − Ψ′(1)(r − 1)) dμ` with `r = dν/dμ`. For
probability measures `ν ≪ μ`, `𝔼_μ(r − 1) = 0`, so this equals `𝔼_μ Ψ(r)` whenever that integral is
defined, and is its `[0, ∞]`-valued value otherwise. The integrand is `≥ 0` when `r ∈ J`, `1 ∈ J`
and `Ψ` is convex and differentiable at `1`, so `ofReal` clips nothing there. -/
noncomputable def phiDiv {α : Type*} [MeasurableSpace α] (Ψ : ℝ → ℝ) (ν μ : Measure α) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Ψ (ν.rnDeriv μ x).toReal - deriv Ψ 1 * ((ν.rnDeriv μ x).toReal - 1)) ∂μ

end PhiSobBayes


