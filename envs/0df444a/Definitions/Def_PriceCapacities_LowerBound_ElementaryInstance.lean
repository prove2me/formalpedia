-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_ElementaryInstance
-- name    : PriceCapacities_LowerBound_ElementaryInstance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:21:34.955406+00:00
-- url     : https://prove2.me/theorems/16635885-2976-4906-aadb-93c618961c7a
-- title:
--   The elementary instance of §10.6: $m$ circle points of radius $\tau$ around each $a_i=4e_i$
-- statement:
--   Let $k\ge1$ and $m\ge1$. In $\mathbb R^k\oplus\mathbb R^2$ let $e_1,\dots,e_k$ be the orthonormal coordinate vectors of the first block; the second block provides two new orthogonal coordinates. The **centers** are $a_i=4e_i$. Given vectors $w_{i,r}\in\mathbb R^2$ ($i\in[k]$, $r\in[m]$), the instance is the finite set
--   $$P=\{a_i+w_{i,r}:\ i\in[k],\ r\in[m]\},$$
--   where $w_{i,r}$ sits in the two new coordinates. When $\|w_{i,r}\|=\tau$ and $r\mapsto w_{i,r}$ is injective, $P$ consists of $m$ distinct points on the circle of radius $\tau$ around each $a_i$.
--
--   **Formalization Note.** Indices are `Fin k`, `Fin m` (0-based); the space is `EuclideanSpace ℝ (Fin k ⊕ Fin 2)`. The circle conditions are hypotheses of the theorem that uses the instance.
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 40, §10.6 (end of the proof of Lemma 10.4)

import Mathlib

open scoped BigOperators

namespace PriceCapacities.LowerBound

/-!
# The elementary instance of §10.6

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), p. 40, end of §10.6.

The space is `ℝ^{k} ⊕ ℝ^2`: orthonormal vectors `e_1, …, e_k` (the first block) and two new
orthogonal coordinates (the second block). The centers are `a_i = 4 e_i`. Around each `a_i` there
are `m` points `a_i + w_{i,r}`, `r = 1, …, m`, where `w_{i,r}` lies in the two new coordinates;
the statements using this instance require `‖w_{i,r}‖ = τ` and `r ↦ w_{i,r}` injective (`m` distinct
points on the circle of radius `τ` around `a_i`). Index base `0` for `i` and `r`.
-/

/-- The center `a_i = 4 e_i`. -/
noncomputable def elemCenter (k : ℕ) (i : Fin k) : EuclideanSpace ℝ (Fin k ⊕ Fin 2) :=
  WithLp.toLp 2 fun c =>
    match c with
    | Sum.inl i' => if i' = i then 4 else 0
    | Sum.inr _ => 0

/-- The point `a_i + w_{i,r}` (`w_{i,r}` in the two new coordinates). -/
noncomputable def elemPoint {k m : ℕ} (w : Fin k → Fin m → EuclideanSpace ℝ (Fin 2)) (i : Fin k)
    (r : Fin m) : EuclideanSpace ℝ (Fin k ⊕ Fin 2) :=
  WithLp.toLp 2 fun c =>
    match c with
    | Sum.inl i' => if i' = i then 4 else 0
    | Sum.inr l => w i r l

open Classical in
/-- The elementary instance: the finite set of all points `a_i + w_{i,r}`. -/
noncomputable def elemInstance {k m : ℕ} (w : Fin k → Fin m → EuclideanSpace ℝ (Fin 2)) :
    Finset (EuclideanSpace ℝ (Fin k ⊕ Fin 2)) :=
  (Finset.univ : Finset (Fin k × Fin m)).image fun p => elemPoint w p.1 p.2

end PriceCapacities.LowerBound


