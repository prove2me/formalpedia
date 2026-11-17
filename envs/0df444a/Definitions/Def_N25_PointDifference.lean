-- Prove2me | Definitions.Def_N25_PointDifference
-- name    : N25_PointDifference
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:17.778241+00:00
-- url     : https://prove2.me/theorems/b334d4b9-67ef-45b9-acc2-d26122af65e5
-- title:
--   Differences of equal-degree places
-- statement:
--   For places $P,Q$ of the same degree, defines the degree-zero divisor class $[P−Q]∈Pic^0$. This is the standard bridge from selected places, including cusps and reductions, to Jacobian and cuspidal-subgroup calculations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
set_option autoImplicit false
noncomputable section
namespace N25.Endgame

noncomputable def pointDiff
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (P Q : AlgebraicCurve.Place K F) (hdeg : P.deg = Q.deg) :
    AlgebraicCurve.Pic0 K F :=
  AlgebraicCurve.Pic0.mk
    ⟨Finsupp.single P 1 - Finsupp.single Q 1, by
      change AlgebraicCurve.Divisor.degree
        (Finsupp.single P 1 - Finsupp.single Q 1) = 0
      simp only [map_sub, AlgebraicCurve.Divisor.degree_single,
        one_mul, hdeg, sub_self]⟩

end N25.Endgame


