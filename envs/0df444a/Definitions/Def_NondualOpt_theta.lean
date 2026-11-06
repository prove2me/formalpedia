-- Prove2me | Definitions.Def_NondualOpt_theta
-- name    : NondualOpt_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:37.699823+00:00
-- url     : https://prove2.me/theorems/a7e791aa-07a2-494a-8ff5-480a34fd9e27
-- title:
--   The rate exponent $\theta(p,q)=1/p-(1/q-1/2)_+$
-- statement:
--   For $p,q\in[1,\infty]$ set
--   $$
--   \theta(p,q)=\frac1p-\Big(\frac1q-\frac12\Big)_+,\qquad a_+=\max\{a,0\},
--   $$
--   with the convention $1/\infty=0$. Corollary 7 gives the optimization rate $\tilde O_{p,q}(T^{-\theta(p,q)})$, and Theorem 30 bounds the sequential fat-shattering dimension of $L^d_{p,q^*}$ through $\alpha^{-1/\theta}$. For $1\le p\le q$ one has $0\le\theta\le1$, with $\theta(1,2)=1$ and $\theta(\infty,\infty)=0$.
--
--   **Formalization Note** $p,q$ are extended nonnegative reals and $1/p$ is `p⁻¹.toReal`, so $1/\infty=0$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Corollary 7, p.12; §2, p.6

import Mathlib

open scoped ENNReal

namespace NondualOpt

/-- The rate exponent `θ(p, q) = 1/p − (1/q − 1/2)₊` of Corollary 7 and Theorem 30.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Corollary 7, p.12; `a₊ = max{a, 0}`, §2, p.6.

**Formalization Note.** `p, q ∈ [1, ∞]` are extended nonnegative reals; `1/p` is `p⁻¹.toReal`,
so `1/∞ = 0` as in the paper. -/
noncomputable def theta (p q : ℝ≥0∞) : ℝ :=
  p⁻¹.toReal - max (q⁻¹.toReal - 1 / 2) 0

end NondualOpt


