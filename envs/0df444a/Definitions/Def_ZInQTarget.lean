-- Prove2me | Definitions.Def_ZInQTarget
-- name    : ZInQTarget
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T19:08:44.197556+00:00
-- url     : https://prove2.me/theorems/cc74d15a-e884-43c0-a5c5-d3f979e676a3
-- title:
--   The frozen target $\mathrm{FrozenTarget}$ (Theorem 1.1)
-- statement:
--   This bundle defines the proposition $\mathrm{FrozenTarget}$, the manuscript's Theorem 1.1. It asserts the existence of a multivariate polynomial $P$ with integer coefficients in $292\,890\,231\,905$ variables whose total degree is below $2\uparrow\uparrow 7$ and whose every coefficient has absolute value below $2\uparrow\uparrow 8$ (here $\uparrow\uparrow$ is tetration, written `hyperoperation 4 2 k` in Lean), such that for every rational $q$ there exist rational witnesses $\mathbf{w}\in\mathbb{Q}^{292890231904}$ with $P(q,\mathbf{w})=0$ if and only if $q$ is an integer. Evaluation substitutes $q$ for the first variable and $\mathbf{w}$ for the rest. This is the goal statement of the mission; the bounds are part of the source theorem.
-- source:
--   https://github.com/elliotglazer/diophantine-z-q/blob/964d7dd71f253091dbc5eac793b78cc56d1fcc73/ZInQKernel/Target.lean#L13-L26

import Mathlib

namespace ZInQ

/-- Theorem 1.1 of the manuscript: a bounded integer polynomial defining the integers in the rationals. -/
def FrozenTarget : Prop :=
  ∃ P : MvPolynomial (Fin 292890231905) Int,
    P.totalDegree < hyperoperation 4 2 7 ∧
    (∀ m : Fin 292890231905 →₀ Nat,
      (P.coeff m).natAbs < hyperoperation 4 2 8) ∧
    ∀ q : Rat,
      (∃ w : Fin 292890231904 → Rat,
        MvPolynomial.eval₂ (Int.castRingHom Rat) (Fin.cons q w) P = 0) ↔
      ∃ z : Int, (z : Rat) = q

end ZInQ


