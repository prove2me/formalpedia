-- Prove2me | Definitions.Def_NashVecOpt_SharedConstraint_VectorOptimization
-- name    : NashVecOpt_SharedConstraint_VectorOptimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:22.819973+00:00
-- url     : https://prove2.me/theorems/beb1113d-926e-4090-9b99-991487fc1603
-- title:
--   Cone-induced order and vector minimizers (Definition 2.3)
-- statement:
--   Let $Z$ be an additive real vector space and let $K\subseteq Z$ be an ordering cone. Its induced comparison is
--
--   $$a\le_K b\quad\Longleftrightarrow\quad b-a\in K.$$
--
--   For a domain $D$, objective $g:D\to Z$, and feasible set $X\subseteq D$, the set of vector minimizers is
--
--   $$K\text{-argmin}\{g(x):x\in X\}
--     =\{x^*\in X: \forall x\in X,\ g(x)\le_K g(x^*)\Rightarrow g(x^*)\le_K g(x)\}.$$
--
--   This is the paper's notion of an efficient feasible point. It works for nonconvex ordering cones and is reusable independently of the game model.
--
--   **Formalization Note** The Lean definition requires only an additive commutative group on $Z$ to state the relation; theorem instances use real vector spaces. No ordering or convexity property is silently imposed on $K$.
-- source:
--   Feinstein, Rudloff, Characterizing and Computing the Set of Nash Equilibria via Vector Optimization, arXiv:2109.14932v5, pp. 4–5, cone-induced relation and Definition 2.3

import Mathlib

namespace NashVecOpt.SharedConstraint

/-- The cone-induced relation from §2.1, p. 4. -/
def coneLE {Z : Type} [AddCommGroup Z] (K : Set Z) (a b : Z) : Prop :=
  b - a ∈ K

/-- Definition 2.3, p. 5, for an arbitrary vector objective and feasible set. -/
def vArgMin {D Z : Type} [AddCommGroup Z] (K : Set Z) (g : D → Z)
    (X : Set D) : Set D :=
  {xs | xs ∈ X ∧ ∀ x ∈ X, coneLE K (g x) (g xs) → coneLE K (g xs) (g x)}

end NashVecOpt.SharedConstraint


