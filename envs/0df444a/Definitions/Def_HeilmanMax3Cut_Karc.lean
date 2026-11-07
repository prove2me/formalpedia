-- Prove2me | Definitions.Def_HeilmanMax3Cut_Karc
-- name    : HeilmanMax3Cut_Karc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:08.277211+00:00
-- url     : https://prove2.me/theorems/caa67776-e85b-4331-baeb-4d2997606fef
-- title:
--   The opposing-arc overlap $K_a(p,q)$
-- statement:
--   Identify the circle with $\mathbb T=\mathbb R/2\pi\mathbb Z$ and let $d\mu(\theta)=d\theta/2\pi$. For $p,q\in[0,1]$ let $E_p=\{\theta:|\theta|\le\pi p\}$ and $F_q=\{\phi:|\phi-\pi|\le\pi q\}$ (modulo $2\pi$): arcs of normalized lengths $p$ and $q$ with opposite centres. For $a\in\mathbb R$,
--
--   $$K_a(p,q)=\iint_{E_p\times F_q}\frac{e^{a\cos(\theta-\phi)}}{I_0(a)}\,d\mu(\theta)\,d\mu(\phi),$$
--
--   where $I_0(a)=\sum_{\ell\ge0}(a/2)^{2\ell}/(\ell!)^2$ is the modified Bessel function of the first kind of order $0$. It is the conditional probability, given the two radii, that two correlated Gaussian points fall in the two opposing arcs.
--
--   **Formalization Note** The circle is the period $(-\pi,\pi]$; there $F_q=\{\phi:\pi(1-q)\le|\phi|\}$. $I_0$ is the published power series, which the paper states equal to its integral form (59).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (58), p.22; I_0 by (59)–(60), p.22

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI
open MeasureTheory Real QueueingFundamentals.Transient

namespace HeilmanMax3Cut

/-- **The opposing-arc overlap `K_a(p, q)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (58), p.22. Identify the circle with
`T = ℝ/(2πℤ)` and write `dμ(θ) = dθ/(2π)`; for `p, q ∈ [0, 1]` let
`E_p := {θ ∈ T : |θ| ≤ πp}` and `F_q := {ϕ ∈ T : |ϕ − π| ≤ πq}` (modulo `2π`), arcs of normalized
lengths `p` and `q` with opposing centres. Then

`K_a(p, q) := ∬_{E_p × F_q} e^{a cos(θ − ϕ)} / I₀(a) dμ(θ) dμ(ϕ)`,

where `I₀` is the modified Bessel function of the first kind of order `0`.

**Formalization Note.** `T` is represented by the period `(−π, π]`. On it `E_p = {θ : |θ| ≤ πp}`,
and since the circular distance from `ϕ ∈ (−π, π]` to `π` is `π − |ϕ|`,
`F_q = {ϕ : π(1 − q) ≤ |ϕ|}`. The measure `μ ⊗ μ` is `(2π)⁻² · dθ dϕ`. `I₀` is the published
`QueueingFundamentals.Transient.besselI 0`, the power series (60) of the paper, which agrees with
the integral form (59) (the paper states both). The formula is evaluated for every real `p, q`
(for `p, q ≥ 1` the arcs are the whole circle); the theorems use `p, q ∈ [0, 1]`. -/
noncomputable def Karc (a p q : ℝ) : ℝ :=
  (2 * π)⁻¹ ^ 2 *
    ∫ θ in {θ : ℝ | θ ∈ Set.Ioc (-π) π ∧ |θ| ≤ π * p},
      ∫ ϕ in {ϕ : ℝ | ϕ ∈ Set.Ioc (-π) π ∧ π * (1 - q) ≤ |ϕ|},
        Real.exp (a * Real.cos (θ - ϕ)) / besselI 0 a

end HeilmanMax3Cut


