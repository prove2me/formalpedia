-- Prove2me | Definitions.Def_WHMultiplicativity_schattenNorm
-- name    : WHMultiplicativity_schattenNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:52.940993+00:00
-- url     : https://prove2.me/theorems/58b853d0-9923-4b58-a163-1473cb917a8d
-- title:
--   Schatten $p$-norm $\|X\|_p = (\operatorname{tr}|X|^p)^{1/p}$, with $\|\cdot\|_\infty$ the operator norm
-- statement:
--   For a complex square matrix $X$ and an exponent $1 \le p < \infty$, the standard **Schatten $p$-norm** is
--
--   $$
--   \|X\|_p = \big(\operatorname{tr}|X|^p\big)^{1/p}, \qquad |X| = (X^*X)^{1/2},
--   $$
--
--   and $\|X\|_\infty$ is the ordinary operator norm of $X$ acting on $\mathbb C^n$ with the Euclidean norm (the largest singular value). For a density matrix $\rho$ the value $\|\rho\|_p$ measures the purity of $\rho$: it equals $1$ exactly for pure states.
--
--   This is the norm in which Werner and Holevo measure output purity in the maximal output norm $\nu_p$.
--
--   **Formalization Note** The exponent is an extended nonnegative real $p \in [0,\infty]$, so one definition covers every real $p$ and $p = \infty$. For finite $p$ the value is $\big(\operatorname{Re}\operatorname{tr}(X^*X)^{p/2}\big)^{1/p}$, the power taken by the continuous functional calculus of the positive semidefinite matrix $X^*X$; this equals $\operatorname{tr}|X|^p$ for every matrix. For $p = \infty$ it is the norm of `Matrix.toEuclideanCLM X`. Values for $p < 1$ are not used anywhere in the mission.
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, §I.A, p.1 (after eq. (1)), and §I.B, p.1 (p = ∞ is the operator norm)

import Mathlib

open scoped Matrix ENNReal

namespace WHMultiplicativity

/-- Werner and Holevo, *Counterexample to an additivity conjecture for output purity of quantum
channels*, arXiv:quant-ph/0203003v1, §I.A, p.1 (after eq. (1)): the standard `p`-norm
`‖X‖_p = (tr |X|^p)^{1/p}`, and §I.B, p.1: `‖·‖_∞` is the ordinary operator norm.

For `p = ⊤` this is the operator norm of `X` acting on `ℂ^ι` with the Euclidean (`ℓ²`) norm.
For a finite `p` it is `(Re tr (XᴴX)^{p/2})^{1/p}`, the power `(XᴴX)^{p/2}` taken by the
continuous functional calculus of the positive semidefinite matrix `XᴴX`.

**Formalization Note.** The exponent is an extended nonnegative real `p : ℝ≥0∞`, so that one
definition covers every real `p` (entered as `ENNReal.ofReal p`) and `p = ∞` (`⊤`). Since
`|X| = (XᴴX)^{1/2}`, `tr |X|^p = tr (XᴴX)^{p/2}` for every matrix, Hermitian or not. The trace is
real and nonnegative; its real part is taken. The paper only uses `1 < p ≤ ∞`; for `p < 1` the
formula is not a norm, and at `p = 0` Lean's conventions (`x ^ 0 = 1`, `1 / 0 = 0`) give the
junk value `1`. Every statement of this mission assumes `1 ≤ p` or `1 < p`. -/
noncomputable def schattenNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ≥0∞)
    (X : Matrix ι ι ℂ) : ℝ :=
  if p = ⊤ then ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖
  else ((cfc (fun x : ℝ => x ^ (p.toReal / 2)) (Xᴴ * X)).trace.re) ^ (1 / p.toReal)

end WHMultiplicativity


