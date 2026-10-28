-- Prove2me | Definitions.Def_D1Bound5_SmallPairRawSelectedData6LeftRows_Definitions
-- name    : D1Bound5_SmallPairRawSelectedData6LeftRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:50:40.070725+00:00
-- url     : https://prove2.me/theorems/ce652a96-f466-426e-959d-a9e201e4e4e0
-- title:
--   Small Pair Raw Selected Data6Left Rows
-- statement:
--   Exact row data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairSelectedPrepared6.leftRows`.
-- source:
--   D1Bound5/SmallPairRawSelectedData6LeftRows.lean, lines 8-667, SHA-256 e02a216124d19826b60d2c6bf81cd904f734fffb942a2d9967a64761e4ffbacc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
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

section
namespace D1Bound5.PairSelectedPrepared6
set_option maxRecDepth 100000

noncomputable def leftRows : List (ℕ × List ℕ) := _root_.D1Bound5.PairLightPrepared6.leftRows

end D1Bound5.PairSelectedPrepared6
end


