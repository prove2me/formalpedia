-- Prove2me | Definitions.Def_AnchoredEP_Supplement_OracleOutput
-- name    : AnchoredEP_Supplement_OracleOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:10:58.12821+00:00
-- url     : https://prove2.me/theorems/bec32d02-bbb2-4738-9aa4-925845351eef
-- title:
--   Output type of a $p$th-order oracle on $\mathbb R^n$
-- statement:
--   A $p$th-order oracle for an operator $F:\mathbb R^n\to\mathbb R^n$, queried at a point $z$, returns the derivatives
--   $$
--   F(z),\ DF(z),\ \dots,\ D^{p-1}F(z),
--   $$
--   where $D^jF(z)$ is a continuous $j$-linear map $(\mathbb R^n)^j\to\mathbb R^n$ and $D^0F(z)=F(z)$. This definition is the type of such outputs: families indexed by $j\in\{0,\dots,p-1\}$ whose $j$-th entry is a continuous $j$-linear map.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Section 6, p.12

import Mathlib

namespace AnchoredEP.Supplement

/-- **The output of a `p`th-order oracle at one point.** Jiang–Yoon, arXiv:2609.30212, Section 6,
p.12: a `p`th-order oracle queried at `z` returns `D^jF(z)` for `0 ≤ j ≤ p − 1`, with `D⁰F = F`.

`OracleOutput p n` is the type of such outputs on `ℝ^n`: a family indexed by `j : Fin p` whose
`j`-th entry is a continuous `j`-linear map `(ℝ^n)^j → ℝ^n`.

**Formalization Note.** A `0`-linear map is a constant, identified with `F(z)`. -/
abbrev OracleOutput (p n : ℕ) : Type :=
  (j : Fin p) → ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))

end AnchoredEP.Supplement


