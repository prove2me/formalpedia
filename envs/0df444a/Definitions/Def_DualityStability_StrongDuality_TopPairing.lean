-- Prove2me | Definitions.Def_DualityStability_StrongDuality_TopPairing
-- name    : DualityStability_StrongDuality_TopPairing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:46.522038+00:00
-- url     : https://prove2.me/theorems/be2c9527-2902-44f1-81e5-2ee80393cebb
-- title:
--   Topologically paired real vector spaces (§2)
-- statement:
--   Let $X$ and $X'$ be real locally convex Hausdorff topological vector spaces. A **topological pairing** is a bilinear map $\langle\cdot,\cdot\rangle:X\times X'\to\mathbb R$ that is continuous in each argument and identifies each space with the full continuous linear dual of the other: every continuous linear functional on $X$ has a unique representing point of $X'$, and conversely.
--
--   $$
--   \forall \ell\in X^*,\ \exists!x'\in X'\ \forall x\in X,\ \ell(x)=\langle x,x'\rangle,
--   \qquad
--   \forall m\in (X')^*,\ \exists!x\in X\ \forall x'\in X',\ m(x')=\langle x,x'\rangle.
--   $$
--
--   This is the general paired-space setting of the paper. It supports conjugation and subgradients without choosing a norm topology or a finite-dimensional representation.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 169, §2

import Mathlib

namespace DualityStability.StrongDuality

/-- A pair of locally convex Hausdorff real spaces in duality as in §2, p. 169.
The two surjectivity-and-uniqueness clauses say that the pairing identifies either
space with the full continuous linear dual of the other. -/
structure TopPairing (E E' : Type*)
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
    [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E'] where
  pair : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ
  continuous_left : ∀ y : E', Continuous (fun x : E => pair x y)
  continuous_right : ∀ x : E, Continuous (fun y : E' => pair x y)
  represents_left : ∀ l : E →L[ℝ] ℝ, ∃! y : E', ∀ x : E, l x = pair x y
  represents_right : ∀ l : E' →L[ℝ] ℝ, ∃! x : E, ∀ y : E', l y = pair x y

end DualityStability.StrongDuality


