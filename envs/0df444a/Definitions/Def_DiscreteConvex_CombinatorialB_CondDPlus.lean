-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_CondDPlus
-- name    : DiscreteConvex_CombinatorialB_CondDPlus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:32:37.376977+00:00
-- url     : https://prove2.me/theorems/6e909e36-a8b6-41cc-9672-390c6a7b4183
-- title:
--   Axiom (M♮-EXC+d[R]) / Theorem 2.12 condition (d+)
-- statement:
--   Axiom $(\mathrm{M}^\natural\text{-EXC}^+_d[\mathbb R])$: as $(\mathrm{M}^\natural\text{-EXC}_d[\mathbb R])$ with the inequality strict.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, and Theorem 2.12(d+), p.70.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, and Theorem 2.12(d+), p.70

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialB_DirDeriv
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69, axiom (M♮-EXC+d[R]) / Theorem 2.12
condition (d+), in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- Axiom **(M-natural-EXC+d[R])** / Theorem 2.12 condition **(d+)**: as `CondD`, with the
inequality `≤ 0` strengthened to `< 0`. -/
def CondDPlus {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : Prop :=
  ∀ x y : V → ℝ, ∀ i ∈ SuppPosR (x - y),
    (∃ j ∈ SuppNegR (x - y),
      DirDeriv M x (-(CharVec i) + CharVec j) + DirDeriv M y (CharVec i - CharVec j) < 0) ∨
    (DirDeriv M x (-(CharVec i)) + DirDeriv M y (CharVec i) < 0)

end DiscreteConvex.CombinatorialB


