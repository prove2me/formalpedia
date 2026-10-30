-- Prove2me | Definitions.Def_BeckTeboulleMD_EMDA_entropy
-- name    : BeckTeboulleMD_EMDA_entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:55.80395+00:00
-- url     : https://prove2.me/theorems/5878355c-df84-402a-814a-c1e510386e2f
-- title:
--   Entropy function $\psi_e$, (5.27)
-- statement:
--   For $x\in\mathbb R^n$, the **entropy function** is
--   $$
--   \psi_e(x)=\sum_{j=1}^n x_j\ln x_j ,
--   $$
--   with the convention $0\ln 0=0$. The paper sets $\psi_e(x)=+\infty$ off the unit simplex $\Delta=\{x\in\mathbb R^n:\sum_j x_j=1,\ x\ge0\}$.
--
--   With $\psi=\psi_e$ the SANP step on $\Delta$ becomes the explicit multiplicative update of the entropic mirror descent algorithm, and $B_{\psi_e}$ is the Kullback–Leibler divergence on $\Delta$.
--
--   **Formalization Note** Lean's $\ln 0=0$ gives the convention $0\ln0=0$. The Lean function is the real-valued formula on all of $\mathbb R^n$; it is the paper's $\psi_e$ on $\Delta$, and every statement using it restricts to points of $\Delta$. Coordinates are indexed by $\{0,\dots,n-1\}$.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003) 167–175, doi:10.1016/s0167-6377(02)00231-6, §5, eq. (5.27), printed p. 173 (PDF p. 7)

import Mathlib

namespace BeckTeboulleMD.EMDA

/-- **The entropy function `ψ_e`, (5.27).**
Beck & Teboulle, *Mirror descent and nonlinear projected subgradient methods for convex
optimization*, Oper. Res. Lett. 31 (2003), §5, eq. (5.27), printed p. 173 (PDF p. 7):
"ψ_e(x) = Σ_{j=1}^n x_j ln x_j if x ∈ Δ, +∞ otherwise, where we adopt the convention 0 ln 0 ≡ 0."

`entropy x = ∑ j, x j * Real.log (x j)` for `x : Fin n → ℝ`.

**Formalization Note.** Mathlib's `Real.log 0 = 0`, so `0 * log 0 = 0` gives the convention
`0 ln 0 ≡ 0`. Off the unit simplex `Δ` the paper's value is `+∞`; this real-valued function is
the paper's `ψ_e` on `Δ` only, and every statement using it restricts to points of `Δ`
(`stdSimplex ℝ (Fin n)`). Coordinates are indexed by `Fin n` (0-based) instead of `1, …, n`. -/
noncomputable def entropy {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j, x j * Real.log (x j)

end BeckTeboulleMD.EMDA


