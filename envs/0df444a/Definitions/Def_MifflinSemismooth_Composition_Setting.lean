-- Prove2me | Definitions.Def_MifflinSemismooth_Composition_Setting
-- name    : MifflinSemismooth_Composition_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:30.80964+00:00
-- url     : https://prove2.me/theorems/478dcf4c-6db1-45ab-9877-5404a426fa13
-- title:
--   Theorem 4 setting — component map, composite function, and generalized-gradient chain-rule set
-- statement:
--   Given component functions $f_i:\mathbb R^n\to\mathbb R$ and an outer function $E:\mathbb R^m\to\mathbb R$, the component map, composite function, and chain-rule candidate are
--
--   $$Y(x)=(f_1(x),\ldots,f_m(x)),\qquad F(x)=E(Y(x)),\qquad G(x)=\operatorname{conv}\left\{\sum_{i=1}^m w_i g^i:g^i\in\partial f_i(x),\ w\in\partial E(Y(x))\right\}. $$
--
--   These are the objects in Theorems 4 and 5. In $G(x)$, one vector $w$ is shared across all components.
--
--   **Formalization Note** The paper's matrix product $[g^1\cdots g^m]w$ is the finite sum $\sum_i w_i g^i$. The empty family $m=0$ is allowed and gives a constant composite function.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 12, Theorem 4

import Mathlib
import Definitions.Def_MifflinSemismooth_Extremal_Basic

namespace MifflinSemismooth.Composition

def Y {n m : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => f i x)

def compF {n m : ℕ} (E : EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  E (Y f x)

def G {n m : ℕ} (E : EuclideanSpace ℝ (Fin m) → ℝ)
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ {g | ∃ (gs : Fin m → EuclideanSpace ℝ (Fin n))
      (w : EuclideanSpace ℝ (Fin m)),
      (∀ i, gs i ∈ MifflinSemismooth.Extremal.genGrad (f i) x) ∧
      w ∈ MifflinSemismooth.Extremal.genGrad E (Y f x) ∧
      g = ∑ i, w i • gs i}

end MifflinSemismooth.Composition


