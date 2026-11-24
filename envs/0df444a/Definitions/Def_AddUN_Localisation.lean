-- Prove2me | Definitions.Def_AddUN_Localisation
-- name    : AddUN_Localisation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:22:08.171411+00:00
-- url     : https://prove2.me/theorems/49df65c2-bb66-4f76-bba5-a27bde623bbc
-- title:
--   Localisation
-- statement:
--   Definitions and structural lemmas for Localisation, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Localisation.lean

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Separation.Profinite
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter Topology TopologicalSpace Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
namespace IdealInvariant
universe u
variable {X : Type u} {I : Set (Set X)}
end IdealInvariant
namespace AddUN
end AddUN


