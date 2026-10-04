-- Prove2me | Definitions.Def_ShadowTomography_UpperBound_avgMarginal
-- name    : ShadowTomography_UpperBound_avgMarginal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:44:30.06112+00:00
-- url     : https://prove2.me/theorems/1f786042-7e45-4e45-a30a-1bb0eff67c32
-- title:
--   One-register marginals and the average marginal of a state on q registers
-- statement:
--   Let $\sigma$ be a matrix on $q$ registers, each with basis labels $n$. The **marginal** of $\sigma$ on register $r$ is the partial trace over the other $q-1$ registers:
--
--   $$
--   (\sigma_r)_{a,b} = \sum_{\substack{x,\,y:\ x_r=a,\ y_r=b,\\ x_s=y_s\ (s\ne r)}} \sigma_{x,y}.
--   $$
--
--   The **average marginal** is
--
--   $$
--   \bar\sigma = \frac1q\sum_{r=1}^{q} \sigma_r ,
--   $$
--
--   the $n$-dimensional state obtained by choosing a register of $\sigma$ uniformly at random and tracing out the remaining $q-1$ registers. In the proof of Theorem 2 the hypothesis $\rho_t$ is the average marginal of the amplified hypothesis $\rho^*_t$.
--
--   **Formalization Note** `marginal σ r` and `avgMarginal σ`; the latter is meaningful only for $q\ge1$ (at $q=0$ the factor $1/q$ is $0$ in Lean), and every statement using it assumes $q\ge1$.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 16 (definition of ρ_t from ρ^*_t)

import Mathlib

namespace ShadowTomography.UpperBound

open Classical in
/-- The one-register marginal of a state `σ` on `q` registers: the reduced state of register `r`,
obtained by tracing out the other `q - 1` registers. Its `(a, b)` entry is
`∑_{x, y} σ x y` over the tuples with `x r = a`, `y r = b` and `x s = y s` for every `s ≠ r`. -/
noncomputable def marginal {n : Type} [Fintype n] {q : ℕ}
    (σ : Matrix (Fin q → n) (Fin q → n) ℂ) (r : Fin q) : Matrix n n ℂ :=
  fun a b => ∑ x, ∑ y, if x r = a ∧ y r = b ∧ ∀ s, s ≠ r → x s = y s then σ x y else 0

/-- The average one-register marginal `(1/q) ∑_r Tr_{-r} σ`: the state obtained by choosing a
register of `σ` uniformly at random and tracing out the remaining `q - 1` registers.
Meaningful for `1 ≤ q` (at `q = 0` it is `0`). -/
noncomputable def avgMarginal {n : Type} [Fintype n] {q : ℕ}
    (σ : Matrix (Fin q → n) (Fin q → n) ℂ) : Matrix n n ℂ :=
  (1 / (q : ℂ)) • ∑ r, marginal σ r

end ShadowTomography.UpperBound


