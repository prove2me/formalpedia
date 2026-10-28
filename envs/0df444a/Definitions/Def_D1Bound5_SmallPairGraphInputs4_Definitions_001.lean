-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_001
-- name    : D1Bound5_SmallPairGraphInputs4_Definitions_001
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:22:09.790702+00:00
-- url     : https://prove2.me/theorems/41bf9edb-d606-4330-b67f-7d957c154056
-- title:
--   Small Pair Graph Inputs4 001
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `smallPairA_4`, `smallPairB_4`.
-- source:
--   D1Bound5/SmallPairGraphInputs4.lean, lines 8-8, SHA-256 e94fdc549f1b35309d7931cc4190675f4a3d8dbf9cf81a6a729a370d2beac0fc; D1Bound5/SmallPairGraphInputs4.lean, lines 9-9, SHA-256 e94fdc549f1b35309d7931cc4190675f4a3d8dbf9cf81a6a729a370d2beac0fc. Project: https://github.com/tomislav-math/d1-bound5-lean

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

noncomputable def smallPairA_4 : QuadInt 0 1 := ⟨-2,-1⟩
noncomputable def smallPairB_4 : QuadInt 0 1 := ⟨0,-1⟩





namespace PairGraphPrepared4



end PairGraphPrepared4
end D1Bound5
end


