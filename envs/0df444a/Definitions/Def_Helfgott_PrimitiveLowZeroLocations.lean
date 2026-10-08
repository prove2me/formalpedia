-- Prove2me | Definitions.Def_Helfgott_PrimitiveLowZeroLocations
-- name    : Helfgott_PrimitiveLowZeroLocations
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T03:12:29.591785+00:00
-- url     : https://prove2.me/theorems/8608776a-9e1a-4256-9546-9d373a7438fd
-- title:
--   Exact primitive low-zero location profile for the original three-prime Goldbach major arcs
-- statement:
--   For every primitive Dirichlet character $\chi$ of conductor $d\ge1$, put $Q_d=2d$ for odd $d$ and $Q_d=d$ for even $d$, and require $Q_d\le300000$. Write $H=L(s,\chi)$ for a nonprincipal character and use the pole-removed zeta function for the primitive principal character. Assume that every zero in $-1/2\le\Re\rho\le2$ is either the origin or on the critical line whenever its height is below either of the two relevant cutoffs: $200+75000000/Q_d$ for $\eta_+$ and $10^8/d$ for $\eta_*$. Then, for every integer $N\ge10^{27}$, with $x=N/(2+9/(196\sqrt{2\pi}))$, the original three-prime major-arc error satisfies
--   $$\left|\int_{\mathfrak M(8,150000,x)}S_{\eta_+}(\alpha,x)^2S_{\eta_*}(\alpha,x)e(-N\alpha)\,d\alpha-x^2M_{N,150000}\!\left(2+\frac9{196\sqrt{2\pi}}\right)\right|\le\frac{0.013}{49}x^2.$$
--   The full odd/even denominator and radius ranges, exact zero multiplicities, the possible trivial zero at zero, all high-zero tails, retained contours and finite-list completion are included. No weighted zero-mass budget is an additional hypothesis. The finite zero-location certificate is an independent remaining input; this theorem does not claim the full mission has been proved.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897, section 4.6. Complete finite explicit formula, conductor-scaled zero counting and contour tails, actual smoothing Sobolev estimates and sharper dyadic arc arithmetic. Written by Codex.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
open Complex
open scoped Classical
namespace Helfgott
def PrimitiveLowZeroLocations : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d),χ.IsPrimitive →
    let Q : ℕ := if Odd d then 2*d else d
    Q≤300000 →
    let H : ℂ → ℂ := if χ=1 then DirichletCharacter.LFunctionTrivChar₁ 1 else χ.LFunction
    (∀ ρ : ℂ,-(1/2 : ℝ)≤ρ.re → ρ.re≤2 → H ρ=0 →
      |ρ.im|<200+75000000/(Q : ℝ) → ρ=0 ∨ ρ.re=1/2) ∧
    (∀ ρ : ℂ,-(1/2 : ℝ)≤ρ.re → ρ.re≤2 → H ρ=0 →
      |ρ.im|<(10 : ℝ)^8/(d : ℝ) → ρ=0 ∨ ρ.re=1/2)
end Helfgott


