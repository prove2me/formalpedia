-- Prove2me | Definitions.Def_BeckTeboulleMD_EMDA_emdaStep
-- name    : BeckTeboulleMD_EMDA_emdaStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:00:12.321486+00:00
-- url     : https://prove2.me/theorems/7c23a9b6-bacb-4d58-9dbb-16c35ddbf2d0
-- title:
--   Update of the entropic mirror descent algorithm (EDA)
-- statement:
--   Given a point $x\in\mathbb R^n$, a vector $g\in\mathbb R^n$ and a step $t\in\mathbb R$, the **EMDA update** is the vector $x^+$ with coordinates
--   $$
--   x^+_j=\frac{x_j\,e^{-t g_j}}{\sum_{i=1}^n x_i\,e^{-t g_i}},\qquad j=1,\dots,n .
--   $$
--   The entropic descent algorithm starts at $x^1$ in the relative interior of the unit simplex and sets $x^{k+1}$ to the update of $x^k$ with $g=f'(x^k)\in\partial f(x^k)$ and the step $t_k$.
--
--   This multiplicative update is the SANP step for the entropy $\psi_e$ on the simplex; its efficiency estimate is Theorem 5.1.
--
--   **Formalization Note** The step rule $t_k$ is not part of the definition; theorems state it. If the denominator vanishes (impossible when $x$ has positive coordinates), Lean's convention $a/0=0$ applies. Coordinates are indexed by $\{0,\dots,n-1\}$.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003) 167–175, doi:10.1016/s0167-6377(02)00231-6, §5, the EDA box, printed p. 174 (PDF p. 8)

import Mathlib

namespace BeckTeboulleMD.EMDA

/-- **The update of the entropic descent algorithm (EDA / EMDA).**
Beck & Teboulle, *Mirror descent and nonlinear projected subgradient methods for convex
optimization*, Oper. Res. Lett. 31 (2003), §5, the EDA box, printed p. 174 (PDF p. 8):
"Start with x¹ ∈ int Δ and generate for k = 1, …, the sequence {x^k} via:
x_j^{k+1} = x_j^k e^{−t_k f′_j(x^k)} / Σ_{j=1}^n x_j^k e^{−t_k f′_j(x^k)}, … where
f′(x) = (f′_1(x), …, f′_n(x))ᵀ ∈ ∂f(x)."

`emdaStep t x g` is the vector with coordinates `x j * exp (-t * g j) / ∑ i, x i * exp (-t * g i)`,
i.e. `x^{k+1}` computed from `x = x^k`, the subgradient vector `g = f′(x^k)` and the step `t = t_k`.

**Formalization Note.** The step size rule `t_k` is not part of this definition; theorems state
it. The formula is total: if the denominator vanishes (impossible when `x` has positive
coordinates) Lean's `a / 0 = 0` applies. Coordinates are indexed by `Fin n` (0-based). -/
noncomputable def emdaStep {n : ℕ} (t : ℝ) (x g : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j * Real.exp (-t * g j) / ∑ i, x i * Real.exp (-t * g i)

end BeckTeboulleMD.EMDA


