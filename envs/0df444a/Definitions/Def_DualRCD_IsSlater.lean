-- Prove2me | Definitions.Def_DualRCD_IsSlater
-- name    : DualRCD_IsSlater
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:27.626668+00:00
-- url     : https://prove2.me/theorems/e4cc3ce0-226a-4d65-8768-93b643213a7c
-- title:
--   Slater's condition for the collection $\{X_i\}$, Definition 2
-- statement:
--   Let $\{X_i\}_{i=1}^m$ be sets in $\mathbb R^n$, and let $0\le r\le m$. The collection satisfies Slater's condition with parameter $r$ if $X_{r+1},\dots,X_m$ are polyhedral and
--   $$
--   \Big(\bigcap_{i=1}^r\operatorname{ri}(X_i)\Big)\cap\Big(\bigcap_{i=r+1}^mX_i\Big)\ne\emptyset .
--   $$
--   This is the constraint qualification under which strong duality holds for the problem.
--
--   **Formalization Note.** Blocks are indexed from $0$, so the paper's $i\le r$ is `i.val < r`. The relative interior is Mathlib's `intrinsicInterior ℝ`. Closedness and convexity of the $X_i$ are separate hypotheses of each theorem, and the condition $1\le r$ of the paper's Theorem 2 is stated where it is used.
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, Definition 2, p.5, display (6)

import Mathlib
import Definitions.Def_DualRCD_IsPolyhedral

namespace DualRCD

/-- Slater's condition, Definition 2 of Necoara & Fercoq, arXiv:1911.06014v1, p.5: there is
`0 ≤ r ≤ m` such that `X_{r+1}, …, X_m` are polyhedral and
`(⋂_{i=1}^r ri(Xᵢ)) ∩ (⋂_{i=r+1}^m Xᵢ) ≠ ∅`, display (6).

**Formalization Note.** Blocks are `0`-based: the paper's `i ≤ r` is `i.val < r`, and its
`i ≥ r + 1` is `r ≤ i.val`. `ri` is Mathlib's `intrinsicInterior ℝ`. The closedness and convexity of
the `Xᵢ` (the preamble of Definition 2) are separate hypotheses of each theorem. Theorem 2 of the
paper additionally has `1 ≤ r`, stated where it is used. -/
def IsSlater {n m : ℕ} (X : Fin m → Set (EuclideanSpace ℝ (Fin n))) (r : ℕ) : Prop :=
  r ≤ m ∧ (∀ i : Fin m, r ≤ i.val → IsPolyhedral (X i)) ∧
    ∃ xbar : EuclideanSpace ℝ (Fin n),
      (∀ i : Fin m, i.val < r → xbar ∈ intrinsicInterior ℝ (X i)) ∧
      (∀ i : Fin m, r ≤ i.val → xbar ∈ X i)

end DualRCD


