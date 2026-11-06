-- Prove2me | Definitions.Def_LawLocalComp_expNorm
-- name    : LawLocalComp_expNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:35.642195+00:00
-- url     : https://prove2.me/theorems/4b172be8-fa3b-4fab-b919-631073a21129
-- title:
--   Expected norm $\mathbb E g(L)$ of an independent load
-- statement:
--   For laws $X_1,\dots,X_n$, directions $a_1,\dots,a_n\in\mathbb R^d$ and a function $g$ on $\mathbb R^d$, with independent sizes $X_j$,
--   $$\mathbb E g(L),\qquad L=\sum_{j} X_j a_j,$$
--   computed as the finite sum $\sum_{x}\big(\prod_j\mathbb P(X_j=x_j)\big)\,g\big(\sum_j x_j a_j\big)$ over all atom profiles $x$.
--
--   Applying a map $\Phi$ to each job gives $\mathbb E g(\tilde L)$ with $\tilde L=\sum_j Y_ja_j$, $Y_j=\Phi(X_j)$ sampled independently per copy: identical laws get the same output law.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), §1, p.2

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The expected norm `E g(L)` of an independent load `L = ∑_j X_j a_j`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), §1, p.2 ("For independent sizes Xj, fixed aj ∈ Rd + and any norm g … write L = Σj Xj aj";
"Identical laws have the same output law, sampled independently per copy").

`expNorm g X a = ∑_x (∏_j P(X_j = x_j)) · g(∑_j x_j a_j)`, the sum over all atom profiles `x`.

**Formalization Note.** Independence is the product weight. Applying a map `Φ` to every job,
`expNorm g (fun j => Φ (X j)) a` is `E g(L̃)` with independent outputs sampled per copy. -/
noncomputable def expNorm {d n : ℕ} (g : (Fin d → ℝ) → ℝ) (X : Fin n → Law)
    (a : Fin n → Fin d → ℝ) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun j => (X j).w.support), (∏ j, (X j).w (x j)) * g (∑ j, x j • a j)

end LawLocalComp


