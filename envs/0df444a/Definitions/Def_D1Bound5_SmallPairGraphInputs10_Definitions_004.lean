-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_004
-- name    : D1Bound5_SmallPairGraphInputs10_Definitions_004
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:26:44.065232+00:00
-- url     : https://prove2.me/theorems/78c8fbe7-e36b-4d66-ba2e-a0c6db1b52ec
-- title:
--   Small Pair Graph Inputs10 004
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `PairGraphPrepared10.colors`.
-- source:
--   D1Bound5/SmallPairGraphInputs10.lean, lines 2405-2405, SHA-256 219b2b1a4f7fcdb3fcd8d93c4768da1d8fb4cc3edb1c20b183f23c91353db0d1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000

open QuadInt








namespace PairGraphPrepared10

noncomputable def colors : ℕ := 26849761815154333312817562738918832811993577403707697762971062610480816923663109268357096804232092646693685346625296855815731958015055410203032461673465842514976876458587158977485933715987915604868284982110538847698436323006112087090663679816387015211672562640328031809246535905594587265131109269305742903415624731100470797665485356935516229005504019656168876

end PairGraphPrepared10
end D1Bound5
end


