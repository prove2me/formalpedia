-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Supplement_SCSubroutine
-- name    : RollingProbeQN_Convex_Supplement_SCSubroutine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:42:03.760115+00:00
-- url     : https://prove2.me/theorems/0c0bc2a0-fb14-45df-b06f-6f64c2e5133f
-- title:
--   Weights (13) and Subroutine 2.1 of the strongly convex method
-- statement:
--   Fix $\mu>0$, $\sigma\in(0,1)$ and the bounds $L_1,L_2,R$.
--
--   1. **Weight (13).** For $A\ge0$ and $\lambda>0$, $a(\lambda)$ is the positive root of $a^2=\lambda[A(1+\mu A)+a(1+2\mu A)]$, namely $a=\tfrac12\big(\lambda\beta+\sqrt{\lambda^2\beta^2+4\lambda\gamma}\big)$ with $\beta=1+2\mu A$, $\gamma=A(1+\mu A)$. At $\mu=0$ it is the weight of (1).
--   2. **Brackets.** For $c>0$, the positive root of $\lambda c=\sigma\sqrt{1+\mu\lambda}$ is $\lambda=\big(\sigma^2\mu+\sigma\sqrt{\sigma^2\mu^2+4c^2}\big)/(2c^2)$; with $c=L_1$ it is the smoothness step $\underline\lambda$, with $c=\bar E_k$ the model step $\bar\lambda_k$.
--   3. **Test function (18)–(19).** With $A'(\lambda)=A_k+a(\lambda)$, $\zeta_k=\|z_k-x_k\|$, $g_k=\|\nabla f(x_k)\|$:
--   $$m_k(\lambda)=\frac{\lambda(1+\mu A_k)\zeta_k}{a(\lambda)},\quad \rho_k(\lambda)=\min\Big\{\lambda g_k+m_k(\lambda)\Big(1+\lambda\bar E_k+\frac{L_2\lambda}{2}m_k(\lambda)\Big),\;R\sqrt{\frac{\lambda}{(1-\sigma^2)A'(\lambda)}}\Big\},$$
--   $$\omega_k(\lambda)=\min\{L_1,\bar E_k+L_2(m_k(\lambda)+\rho_k(\lambda))\},\qquad \phi_k(\lambda)=\frac{\lambda\,\omega_k(\lambda)}{\sqrt{1+\mu\lambda}} .$$
--   4. **Subroutine 2.1.** Set $\lambda^-=\underline\lambda$, $\lambda^+=\bar\lambda_k$; while $\lambda^+/\lambda^->2^{1/4}$, set $\lambda=\sqrt{\lambda^-\lambda^+}$ and replace $\lambda^-$ by $\lambda$ if $\phi_k(\lambda)\le\sigma$, otherwise $\lambda^+$ by $\lambda$; return $\lambda_k=\lambda^-$.
--
--   These scalar formulas are evaluated on stored data only and make no gradient query.
--
--   **Formalization Note** The while loop is a guarded bisection pass iterated $\lceil 4\log(\bar\lambda_k/\underline\lambda)/\log2\rceil+1$ times, which is at least the number of iterations the loop performs; once the guard fails, further passes do nothing. The subroutine returns the final bracket $(\lambda^-,\lambda^+)$, so Theorem 4.2 can state that the loop has ended. The test is the non-strict $\phi_k\le\sigma$, so the published bisection of Subroutine 1.1 (strict test) is not reused.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, (13), p. 13; (18)–(19) and Subroutine 2.1, p. 14

import Mathlib

namespace RollingProbeQN.Convex.Supplement

/-- **The weight `a(λ)` of the strongly convex A-HPE recursion, (13).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, (13), p. 13: "Given a stepsize `λk > 0`,
the new weight `ak > 0` is chosen as the positive root of `ak² = λk[Ak(1 + μAk) + ak(1 + 2μAk)]`".

`aSC μ A λ = (λβ + √(λ²β² + 4λγ))/2` with `β = 1 + 2μA` and `γ = A(1 + μA)`, the positive root of
`a² − λβa − λγ = 0`. At `μ = 0` it is the weight `a(λ)` of (1). -/
noncomputable def aSC (μ A lam : ℝ) : ℝ :=
  (lam * (1 + 2 * μ * A) +
    Real.sqrt ((lam * (1 + 2 * μ * A)) ^ 2 + 4 * lam * (A * (1 + μ * A)))) / 2

/-- **The positive root of `λc = σ√(1 + μλ)`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §4.1, p. 14: "the smoothness step `λ`, the
positive root of `λL1 = σ√(1 + μλ)` […] and the model step `λ̄k`, the positive root of
`λĒk = σ√(1 + μλ)`".

`rootSC c σ μ = (σ²μ + σ√(σ²μ² + 4c²))/(2c²)`. With `c = L₁` it is the smoothness step `λ̲`
(underlined in the paper), with `c = Ē_k` the model step `λ̄_k`.

**Formalization Note.** For `c, σ > 0` and `μ ≥ 0` this is the positive solution of
`c²λ² − σ²μλ − σ² = 0`, which is the equation squared; both sides of the original equation are positive
there. -/
noncomputable def rootSC (c σ μ : ℝ) : ℝ :=
  (σ ^ 2 * μ + σ * Real.sqrt (σ ^ 2 * μ ^ 2 + 4 * c ^ 2)) / (2 * c ^ 2)

/-- **The scalar test function `φ_k` of Subroutine 2.1, (18)–(19).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, §4.1, p. 14: with `a(λ)`, `A′(λ) = Ak + a(λ)`
formed by (13)–(14), `ζk = ‖zk − xk‖`, `gk = ‖∇f(xk)‖`,
`mk(λ) = λ(1 + μAk)ζk/a(λ)`,
`ρk(λ) = min{λgk + mk(λ)(1 + λĒk + L2λ mk(λ)/2), R√(λ/((1 − σ²)A′(λ)))}` (18),
`ωk(λ) = min{L1, Ēk + L2(mk(λ) + ρk(λ))}`, `φk(λ) = λωk(λ)/√(1 + μλ)` (19).

`phiSC L₁ L₂ R σ μ A ζ g Ē λ` is `φ_k(λ)` for the inputs `A = A_k`, `ζ = ζ_k`, `g = g_k`, `Ē = Ē_k`.
Both branches of `ρ_k` (resolvent and energy) enter. -/
noncomputable def phiSC (L₁ L₂ R σ μ A ζ g Ebar lam : ℝ) : ℝ :=
  let a : ℝ := aSC μ A lam
  let A' : ℝ := A + a
  let m : ℝ := lam * (1 + μ * A) * ζ / a
  let ρ : ℝ := min (lam * g + m * (1 + lam * Ebar + L₂ * lam * m / 2))
    (R * Real.sqrt (lam / ((1 - σ ^ 2) * A')))
  let ω : ℝ := min L₁ (Ebar + L₂ * (m + ρ))
  lam * ω / Real.sqrt (1 + μ * lam)

/-- **One pass of Step 2 of Subroutine 2.1.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Subroutine 2.1, Step 2, p. 14: "While
`λ+/λ− > 2^{1/4}`: set `λ = √(λ−λ+)`; if `φk(λ) ≤ σ`, set `λ− = λ`, otherwise set `λ+ = λ`."

The state is the bracket `(λ−, λ+)`. A pass performs one iteration of the while loop if its guard holds
and does nothing otherwise.

**Formalization Note.** The test is `φ ≤ σ` (non-strict), unlike Subroutine 1.1 (`Ψ̂ < σ`), so the
published `bisectPass` is not reused. -/
noncomputable def bisectPassSC (φ : ℝ → ℝ) (σ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if (2 : ℝ) ^ ((1 : ℝ) / 4) < p.2 / p.1 then
    if φ (Real.sqrt (p.1 * p.2)) ≤ σ then (Real.sqrt (p.1 * p.2), p.2)
    else (p.1, Real.sqrt (p.1 * p.2))
  else p

/-- **Subroutine 2.1 (Stepsize selection).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Subroutine 2.1, p. 14: "Input: `Ak, ζk, gk,
Ēk`. Evaluate `φk` through (18)–(19). 1. Set `λ− = λ` and `λ+ = λ̄k`. 2. While `λ+/λ− > 2^{1/4}`: set
`λ = √(λ−λ+)`; if `φk(λ) ≤ σ`, set `λ− = λ`, otherwise set `λ+ = λ`. 3. Return `λk = λ−`."

`sub21 L₁ L₂ R σ μ A ζ g Ē` returns the final bracket `(λ−, λ+)`; the stepsize is its first entry. The
loop starts at `(λ̲, λ̄_k) = (rootSC L₁ σ μ, rootSC Ē σ μ)`.

**Formalization Note.** The while loop is `bisectPassSC` iterated `⌈4 log(λ̄_k/λ̲)/log 2⌉ + 1` times
(reading R8 of the base mission). Each executed pass halves `log(λ+/λ−)`, which starts at
`log(λ̄_k/λ̲)`, so this many passes reduce it below `log 2^{1/4}`; once the guard fails, further passes
change nothing. Theorem 4.2 asserts that the returned bracket has ratio at most `2^{1/4}`, so the
cut-off is not a hidden truncation. The subroutine takes scalars only and makes no gradient query. -/
noncomputable def sub21 (L₁ L₂ R σ μ A ζ g Ebar : ℝ) : ℝ × ℝ :=
  (bisectPassSC (phiSC L₁ L₂ R σ μ A ζ g Ebar) σ)^[
      ⌈4 * Real.log (rootSC Ebar σ μ / rootSC L₁ σ μ) / Real.log 2⌉₊ + 1]
    (rootSC L₁ σ μ, rootSC Ebar σ μ)

end RollingProbeQN.Convex.Supplement


