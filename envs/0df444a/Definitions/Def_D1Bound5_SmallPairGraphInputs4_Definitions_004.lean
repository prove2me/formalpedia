-- Prove2me | Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_004
-- name    : D1Bound5_SmallPairGraphInputs4_Definitions_004
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:14:37.322497+00:00
-- url     : https://prove2.me/theorems/d8592fb8-da87-4276-8ef1-6c09ab3b3e1e
-- title:
--   Small Pair Graph Inputs4 004
-- statement:
--   Exact anchor coordinates and finite vertex lists for the small-pair mutation graphs. The named objects in this bundle include `PairGraphPrepared4.colors`.
-- source:
--   D1Bound5/SmallPairGraphInputs4.lean, lines 2406-2406, SHA-256 e94fdc549f1b35309d7931cc4190675f4a3d8dbf9cf81a6a729a370d2beac0fc. Project: https://github.com/tomislav-math/d1-bound5-lean

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








namespace PairGraphPrepared4

noncomputable def colors : ℕ := 40668559523812208408337035224825992334383892317692251885049401568090107805101021341356660932007981839213016132130886622841464268437511960842616741446023438836418188480101445971072267306309955476783453259120560605202180962434406399442320441038112956850236775613791123633336102770506807065171466941622595501974403228218719671145830648861735141799830048347730332

end PairGraphPrepared4
end D1Bound5
end


