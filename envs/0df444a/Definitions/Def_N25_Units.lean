-- Prove2me | Definitions.Def_N25_Units
-- name    : N25_Units
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:54.300353+00:00
-- url     : https://prove2.me/theorems/b9a1a936-6d52-4360-8083-457b03a26856
-- title:
--   The five level-$25$ modular units in the function field
-- statement:
--   For every field $K$, the file defines five elements $U_i$ of the level-$25$ modular function field by equipping the normalized Laurent series with their membership certificates. Over $ℚ$ it introduces the corresponding abbreviated family. These are the actual function-field units used to generate the modular field and define the plane coordinates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic
set_option autoImplicit false
namespace N25

/-- The five modular units of level 25 as elements of the function field. The series always lies in that
field (`unitSeries25_mem`); the junk value `0` in the other case keeps this definition independent of that
theorem. Use `coe_U25C` to compute it. -/
noncomputable def U25C (K : Type*) [Field K] (i : Fin 5) :
    ↥(ModularCurve.xHFunctionFieldC K 25 N25.H25) :=
  open Classical in
  if h : unitSeries25 K i ∈ ModularCurve.xHFunctionFieldC K 25 N25.H25 then ⟨unitSeries25 K i, h⟩ else 0

noncomputable abbrev U25 := U25C ℚ

end N25


