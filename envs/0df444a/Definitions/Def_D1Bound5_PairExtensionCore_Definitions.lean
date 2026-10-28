-- Prove2me | Definitions.Def_D1Bound5_PairExtensionCore_Definitions
-- name    : D1Bound5_PairExtensionCore_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:51:21.51804+00:00
-- url     : https://prove2.me/theorems/80b8b019-6580-4f19-a761-f3f83b83ea07
-- title:
--   Pair Extension Core
-- statement:
--   Common extensions retain zero and anchor coincidences. The named objects in this bundle include `PairExtension`, `pairSeedCandidate`, `pairSeedsCoveredBool`, `pairMutationPlus`, `pairMutationMinus`, `pairClosureBool`, `tripleExtensionFilterBool`.
-- source:
--   D1Bound5/PairExtensionCore.lean, lines 8-10, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f; D1Bound5/PairExtensionCore.lean, lines 39-44, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f; D1Bound5/PairExtensionCore.lean, lines 63-70, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f; D1Bound5/PairExtensionCore.lean, lines 110-113, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f; D1Bound5/PairExtensionCore.lean, lines 115-117, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f; D1Bound5/PairExtensionCore.lean, lines 163-171, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f; D1Bound5/PairExtensionCore.lean, lines 184-190, SHA-256 d45446b353f1adcd08c1943cfe73040bef48ad11485fc541c7388b34f9e5255f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt

/-- Common extensions retain zero and anchor coincidences. -/
def PairExtension {tau nu : ℤ} (a b z : QuadInt tau nu) : Prop :=
  (∃ r, r*r = a*z+1) ∧ (∃ s, s*s = b*z+1)





/-- Exact quotient (q²−1)/a computed by multiplying by the conjugate of a.
The candidate is subsequently checked, so divisibility is never assumed. -/
def pairSeedCandidate {tau nu : ℤ} (a q : QuadInt tau nu) : QuadInt tau nu :=
  let w := q*q-1
  ⟨((a.re+tau*a.im)*w.re+nu*a.im*w.im)/a.norm,
    (a.re*w.im-a.im*w.re)/a.norm⟩



/-- A finite root search checks all radius-33 seeds, including zero. -/
def pairSeedsCoveredBool {tau nu : ℤ} (a b : QuadInt tau nu)
    (roots vertices : List (QuadInt tau nu)) : Bool :=
  roots.all fun q =>
    let z := pairSeedCandidate a q
    if decide (q*q = a*z+1 ∧ z.norm ≤ 1089) then
      if hasSquareRoot (b*z+1) then decide (z ∈ vertices) else true
    else true







/-- The two canonical neighbors generate both root-sign choices. -/
def pairMutationPlus {tau nu : ℤ} (a b z : QuadInt tau nu) : QuadInt tau nu :=
  mutate a b z (rootCandidate (a*b+1))
    (rootCandidate (a*z+1)) (rootCandidate (b*z+1))

def pairMutationMinus {tau nu : ℤ} (a b z : QuadInt tau nu) : QuadInt tau nu :=
  mutate a b z (rootCandidate (a*b+1))
    (rootCandidate (a*z+1)) (-rootCandidate (b*z+1))





/-- A bounded closed list is checked at its own vertices, not by enumerating
the surrounding potentially enormous disk. -/
def pairClosureBool {tau nu : ℤ} (a b : QuadInt tau nu) (bound : ℤ)
    (vertices : List (QuadInt tau nu)) : Bool :=
  vertices.all fun z =>
    (if decide ((pairMutationPlus a b z).norm ≤ bound) then
      decide (pairMutationPlus a b z ∈ vertices) else true) &&
    (if decide ((pairMutationMinus a b z).norm ≤ bound) then
      decide (pairMutationMinus a b z ∈ vertices) else true)



/-- Filter a certified pair-extension list by the third anchor. -/
def tripleExtensionFilterBool {tau nu : ℤ} (a b c : QuadInt tau nu)
    (vertices allowed : List (QuadInt tau nu)) : Bool :=
  vertices.all fun z =>
    if decide (z ≠ 0 ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c) then
      if hasSquareRoot (c*z+1) then decide (z ∈ allowed) else true
    else true



end D1Bound5
end


