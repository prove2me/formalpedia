-- Prove2me | Definitions.Def_NashVecOpt_SharedConstraint_Model
-- name    : NashVecOpt_SharedConstraint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:12.546228+00:00
-- url     : https://prove2.me/theorems/869dd6a3-f6d4-4bcd-8866-bcfe6b6f0d9f
-- title:
--   Augmented game objective and ordering cones (5)–(7)
-- statement:
--   For a shared-constraint game, collect the costs into $f(x)=(f_i(x))_i$ and augment them with the whole joint strategy:
--
--   $$g(x)=(x,f(x))\in\left(\prod_i\mathcal X_i\right)\times\mathbb R^I.$$
--
--   The ordering cone of (6) and player cone of (7) are
--
--   $$C=\{(u,v):\exists i,\ u_j=0\text{ for all }j\ne i,\ v_i\ge0\},$$
--   $$C_i=\left(\prod_{j\ne i}\{0_{\mathcal X_j}\}\times\mathcal X_i\right)
--     \times\left(\mathbb R^{I\setminus\{i\}}\times\mathbb R_+\right),$$
--
--   where the second product formula specifies the $i$th coordinates of each ordered product and leaves the remaining cost coordinates unrestricted. These objects encode comparisons involving one player's cost while other players' strategies stay fixed.
--
--   **Formalization Note** The product cone is implemented coordinatewise: $u_j=0$ for $j\ne i$ and $v_i\ge0$. The full cone is independently defined by the existential formula of (6), so its equality with the union of the $C_i$ is a separate theorem.
-- source:
--   Feinstein, Rudloff, Characterizing and Computing the Set of Nash Equilibria via Vector Optimization, arXiv:2109.14932v5, pp. 5–6, objective (5) and cones (6)–(7)

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_VectorOptimization
import Definitions.Def_NashVecOpt_SharedConstraint_Game

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Objective (5), p. 6: retain strategies as well as every player's cost. -/
def obj (f : ι → (∀ j, E j) → ℝ) (x : ∀ j, E j) :
    (∀ j, E j) × (ι → ℝ) := (x, fun i => f i x)

/-- Ordering cone (6), p. 6: some player's cost coordinate is nonnegative and all other
strategy coordinates vanish. -/
def orderCone : Set ((∀ j, E j) × (ι → ℝ)) :=
  {z | ∃ i, (∀ j, j ≠ i → z.1 j = 0) ∧ 0 ≤ z.2 i}

/-- The player-indexed product cone (7), p. 6. -/
def coneI (i : ι) : Set ((∀ j, E j) × (ι → ℝ)) :=
  (Set.univ.pi fun j => if j = i then (Set.univ : Set (E j)) else {0}) ×ˢ
  (Set.univ.pi fun j => if j = i then Set.Ici (0 : ℝ) else Set.univ)

end NashVecOpt.SharedConstraint


