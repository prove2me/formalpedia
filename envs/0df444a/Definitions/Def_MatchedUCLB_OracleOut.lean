-- Prove2me | Definitions.Def_MatchedUCLB_OracleOut
-- name    : MatchedUCLB_OracleOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:26.203203+00:00
-- url     : https://prove2.me/theorems/41e14bc8-f7cb-41ae-ae1f-444be5e795b0
-- title:
--   The type of a $p$th-order oracle output $(a_0,\dots,a_p)$
-- statement:
--   A **$p$th-order oracle output** on $\mathbb R^d$ is a tuple $(a_0,a_1,\dots,a_p)$ in which $a_k$ is a continuous $k$-linear form on $\mathbb R^d$. The $0$-linear form $a_0$ is a number (the value), $a_1$ a linear form (the gradient), and $a_k$ for $k\ge2$ the $k$th derivative tensor. This is the shape of the oracle answer $O_s=(a_{s,0},\dots,a_{s,p})$ of (F.1).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, with the Euclidean inner product and norm.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition B.1, p.17; Eq. (F.1), p.98

import Mathlib

namespace MatchedUCLB

/-- **The type of a pth-order oracle output.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition B.1, p.17: "An oracle call at
`x` returns the oracle output `(F(x), ∇F(x), …, ∇^pF(x))`"; (F.1), p.98:
`O_s = (a_{s,0}, …, a_{s,p})`.

`OracleOut d p` is the type of families `(a_0, …, a_p)` in which `a_k` is a continuous `k`-linear
form on `ℝ^d`. A `0`-linear form is a constant: it records the value `F(x)`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. The `k`th entry is a
`ContinuousMultilinearMap` on `Fin k → ℝ^d`, the type of Mathlib's `iteratedFDeriv ℝ k F x`. -/
abbrev OracleOut (d p : ℕ) : Type :=
  (k : Fin (p + 1)) → ContinuousMultilinearMap ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin d)) ℝ

end MatchedUCLB


