-- Prove2me | Definitions.Def_N25_CuspReduction
-- name    : N25_CuspReduction
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:53.168636+00:00
-- url     : https://prove2.me/theorems/d82dce80-46a0-47b6-955c-9d50234c0954
-- title:
--   The reduced $q$-infinity place in characteristic two
-- statement:
--   Given a reduction datum at $2$ with residue field $κ$, the file defines the $q$-adic infinity place of the characteristic-two level-$25$ modular function field over $κ$. This distinguished special-fibre place is the reduction of the chosen cusp and serves as the base point in the reduction and Frobenius calculations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_QAdicPlaceMod
set_option autoImplicit false
noncomputable section
namespace N25.Endgame

/-- The q-adic place on the characteristic-two modular function field. -/
noncomputable def qInfinitySpecial25 (D₂ : RedDatum25 2) :
    SpecialPlace D₂.A :=
  ModularCurve.qInftyPlaceMod (κ D₂.A)
    (jBase25 (κ D₂.A)).property

end N25.Endgame


