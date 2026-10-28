-- Prove2me | Definitions.Def_D1Bound5_SmallPairRawSelectedData6RightRows_Definitions
-- name    : D1Bound5_SmallPairRawSelectedData6RightRows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:37:29.542895+00:00
-- url     : https://prove2.me/theorems/d0d039f6-65a7-45c6-82fd-d12b608c71c7
-- title:
--   Small Pair Raw Selected Data6Right Rows
-- statement:
--   Exact row data used by the selected-floor tests on the finite small-pair vertex lists. The named objects in this bundle include `PairSelectedPrepared6.rightRows`.
-- source:
--   D1Bound5/SmallPairRawSelectedData6RightRows.lean, lines 8-666, SHA-256 b83809eb56414897ce29724d6956f935a2a8221ca84a7dcae5d14e8b60491e51. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
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

noncomputable def rightRows : List (ℕ × List ℕ) := _root_.D1Bound5.PairLightPrepared6.rightRows

end D1Bound5.PairSelectedPrepared6
end


