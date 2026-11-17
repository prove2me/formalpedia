-- Prove2me | Definitions.Def_N25_SelectedCusps
-- name    : N25_SelectedCusps
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:27.030871+00:00
-- url     : https://prove2.me/theorems/11d62a6a-7f07-4502-99a7-a193584360f9
-- title:
--   A selected five-cycle of cusps
-- statement:
--   Chooses a rational diamond automorphism and compatible rational and geometric places from one free orbit of the label-$13$ diamond action, producing five indexed cusps in each place space. This common orbit fixes the cusp labels used in modular-unit divisors and Galois comparisons.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_five_qPlaces_distinct
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
set_option autoImplicit false
noncomputable section

namespace N25.Endgame

/-- The rational automorphism and the two q-adic witnesses are selected from
one common free orbit of the label-thirteen diamond. -/
noncomputable def cuspChoice25 : CuspChoice25 where
  hQ := N25.five_qPlaces_distinct.choose
  hG := N25.five_qPlaces_distinct.choose_spec.choose
  tauQ := N25.five_qPlaces_distinct.choose_spec.choose_spec.choose

abbrev gammaF25 : FG ≃ₐ[Qbar] FG :=
  ModularCurve.diamondAutHBar 25 N25.H25
    (ZMod.unitOfCoprime 13 (by decide))

noncomputable def pQ25 (i : Fin 5) : QPlace :=
  (AlgebraicCurve.SemilinearAut.ofAlgAut cuspChoice25.tauQ)^i.val •
    ModularCurve.qInftyPlaceRat FQ cuspChoice25.hQ

noncomputable def pG25 (i : Fin 5) : GPlace :=
  (AlgebraicCurve.SemilinearAut.ofAlgAut gammaF25)^i.val •
    ModularCurve.qInftyPlaceBar Qbar FG cuspChoice25.hG

end N25.Endgame


