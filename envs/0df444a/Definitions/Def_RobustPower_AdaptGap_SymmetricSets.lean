-- Prove2me | Definitions.Def_RobustPower_AdaptGap_SymmetricSets
-- name    : RobustPower_AdaptGap_SymmetricSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:30:58.226993+00:00
-- url     : https://prove2.me/theorems/8d778187-9439-419f-a5fb-cec9e61957ff
-- title:
--   Symmetry and the coordinatewise bounding hypercube
-- statement:
--   A set $S$ is **symmetric about** $u\in S$ when $u+z\in S$ if and only if $u-z\in S$ for every displacement $z$. A set is symmetric when it has such a point. For a set of real vectors, its coordinatewise lower and upper endpoints are
--
--   $$x_j^l=\inf_{x\in S}x_j,\qquad x_j^h=\sup_{x\in S}x_j.$$
--
--   The bounding hypercube is $[x^l,x^h]$, with center $x^0=(x^l+x^h)/2$. The file also supplies the upper endpoints separately for uncertain right-hand sides and costs. These definitions fix the geometry used in Lemma 2.3 and Theorem 5.1.
--
--   **Formalization Note** Real infima and suprema have default values on empty or unbounded coordinate sets. The theorem hypotheses ensure the uncertainty set is nonempty and bounded; these definitions are used under those hypotheses.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 5, Definition 1.2; p. 12, (2.5)–(2.7)

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

namespace RobustPower.AdaptGap

/-- Display (2.5): coordinatewise upper endpoint of the bounding hypercube. -/
noncomputable def xh {ι : Type*} (S : Set (ι → ℝ)) : ι → ℝ :=
  fun j => sSup ((fun x : ι → ℝ => x j) '' S)

/-- Display (2.6): coordinatewise lower endpoint of the bounding hypercube. -/
noncomputable def xl {ι : Type*} (S : Set (ι → ℝ)) : ι → ℝ :=
  fun j => sInf ((fun x : ι → ℝ => x j) '' S)

/-- Display (2.7): the coordinatewise bounding hypercube. -/
noncomputable def boundingBox {ι : Type*} (S : Set (ι → ℝ)) : Set (ι → ℝ) :=
  Set.Icc (xl S) (xh S)

/-- Lemma 2.3: the midpoint of the bounding hypercube. -/
noncomputable def boxCenter {ι : Type*} (S : Set (ι → ℝ)) : ι → ℝ :=
  fun j => (xl S j + xh S j) / 2

/-- The upper cost coordinate of the bounding box of the scenario set. -/
noncomputable def costUpper {n₂ : ℕ} {Ω : Type*} (d : Ω → Fin n₂ → ℝ) : Fin n₂ → ℝ :=
  xh (Set.range d)

/-- The upper right-hand-side coordinate of the bounding box. -/
noncomputable def rhsUpper {m : ℕ} {Ω : Type*} (b : Ω → Fin m → ℝ) : Fin m → ℝ :=
  xh (Set.range b)

end RobustPower.AdaptGap


