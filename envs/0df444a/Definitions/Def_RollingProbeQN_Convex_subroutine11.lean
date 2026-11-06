-- Prove2me | Definitions.Def_RollingProbeQN_Convex_subroutine11
-- name    : RollingProbeQN_Convex_subroutine11
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:41.188027+00:00
-- url     : https://prove2.me/theorems/2f0637c6-d4d4-46f8-b2d9-3412f358c9f3
-- title:
--   Subroutine 1.1: gradient-free bisection for the stepsize $\lambda_k$
-- statement:
--   **Subroutine 1.1 (Stepsize selection).** Input: $A_k,\zeta_k,g_k,\bar E_k$.
--
--   1. If $\widehat\Psi_k(\sigma/L_1)\ge\sigma$, return $\lambda_k=\sigma/L_1$.
--   2. Set $\lambda^-=\sigma/L_1$ and $\lambda^+=\sigma/\bar E_k$.
--   3. While $\lambda^+/\lambda^->2^{1/4}$: set $\lambda=\sqrt{\lambda^-\lambda^+}$; if $\widehat\Psi_k(\lambda)<\sigma$, set $\lambda^-=\lambda$, otherwise $\lambda^+=\lambda$.
--   4. Return $\lambda_k=\lambda^-$.
--
--   The definition returns $\lambda_k$ together with the number of evaluations of $\widehat\Psi_k$.
--
--   **Formalization Note** The loop is the guarded pass iterated $\lceil4\log(L_1/\bar E_k)/\log2\rceil+1$ times. Each pass halves $\log(\lambda^+/\lambda^-)$, which starts at $\log(L_1/\bar E_k)$, so the loop ends after at most this many passes; extra passes do nothing. The subroutine takes scalars only and therefore queries no gradient.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Subroutine 1.1, p. 10

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_surrogate
import Definitions.Def_RollingProbeQN_Convex_bisectPass

namespace RollingProbeQN.Convex

/-- **Subroutine 1.1 (Stepsize selection).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Subroutine 1.1, p. 10: "Input: `A_k, ζ_k, g_k, Ē_k`. Evaluate `Ψ̂_k` through (10) and (7).
1. If `Ψ̂_k(σ/L1) ≥ σ`, return `λ_k = σ/L1`. 2. Set `λ− = σ/L1` and `λ+ = σ/Ē_k`. 3. While
`λ+/λ− > 2^{1/4}`: set `λ = √(λ−λ+)`; if `Ψ̂_k(λ) < σ`, set `λ− = λ`, otherwise set `λ+ = λ`.
4. Return `λ_k = λ−`."

`subroutine11 L₁ L₂ σ A ζ g Ē` returns the pair `(λ_k, n)`, where `n` is the number of evaluations
of `Ψ̂_k` the subroutine performed.

**Formalization Note.** Reading R8: the while loop is `bisectPass` iterated
`⌈4 log(L₁/Ē)/log 2⌉ + 1` times. Each pass halves `log(λ+/λ−)`, which starts at `log(L₁/Ē)`, so the
loop ends after `⌈log₂ max{1, log(L₁/Ē)/log 2^{1/4}}⌉` passes (Lemma E.6), which is at most this
number; the remaining passes do nothing. The subroutine takes scalars only, so it makes no
gradient query. -/
noncomputable def subroutine11 (L₁ L₂ σ A ζ g Ebar : ℝ) : ℝ × ℕ :=
  if σ ≤ surrogate L₁ L₂ A ζ g Ebar (σ / L₁) then (σ / L₁, 1)
  else
    let p := (bisectPass (surrogate L₁ L₂ A ζ g Ebar) σ)^[⌈4 * Real.log (L₁ / Ebar) / Real.log 2⌉₊ + 1]
      (σ / L₁, σ / Ebar, 1)
    (p.1, p.2.2)

end RollingProbeQN.Convex


