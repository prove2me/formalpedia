-- Prove2me | Definitions.Def_PricingWithTips3DM_4c74acf7ab61410b0782962b
-- name    : PricingWithTips3DM_4c74acf7ab61410b0782962b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:37:24.198033+00:00
-- url     : https://prove2.me/theorems/237387c2-1125-4549-950b-fb615f6c7d9f
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Sets.Matching3D.FromSat.Code
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_2b9b1ca3b5e0361c4e5bb9c7
import Definitions.Def_PricingWithTips3DM_b27b057a2325e62412e51b11
import Definitions.Def_PricingWithTips3DM_9b371543de0be5a588dc23d1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# SAT → 3-dimensional matching: the program

Garey–Johnson's three-component construction as a program of the builder
language. The mathematical layer (`Matching3D/FromSat.lean`) names elements by
*tagged tuples* — a truth-setting element is `(variable slot, clause,
polarity)`, an internal element is a tagged sum — while a concrete instance
can only name elements by *positions* of an element list. The program therefore
carries out the construction in a mixed-radix numbering of those tags:

* external elements are numbered `2 * (m * i + j) + b`, so the `(n + 1) * m * 2`
  of them fill the external list exactly;
* internal elements are numbered by the three components in turn — ring
  elements `m * i + j` first, then the `m` clause-testing elements, then the
  `m * n` garbage elements `n * j + i'`.

`Adequacy.lean` exhibits these numberings as *bijections* onto the positions of
the element lists, which is all the bridge needs: 3DM is invariant under
renaming the coordinate sets (`matching3D_iff_of_equiv`).

The element lists themselves are Cartesian products of lists the program
already has (`Code.cross`), which is how a certificate builds a list of a
prescribed length without a `range` primitive; their entries are ignored
labels, since elements *are* positions.
-/

namespace Hardness
namespace Cert

namespace SatToMatching3DCode

/-! ## The environment

Every gadget program needs the variable list (to find a literal's slot) and the
clause count `m` (the radix of the external numbering). The slot count `n` is
read off the variable list with `listLen`, so the environment carries just the
two. -/

/-- The environment threaded through the gadget programs: `(variables, m)`. -/
abbrev EnvTy : Ty := .pair (.list .nat) .nat

/-- One (ignored) label per clause — a list of length `m`, used to size the
element lists. -/
def clauseUnits : Code SatTy (.list .nat) := .listMap (.const .nat 0)

/-- The variable slots: one per variable, plus the dummy slot that literals of
absent variables land on (`varSlot`). Length `n + 1`. -/
def slotsCode : Code SatTy (.list .nat) :=
  .comp (.pair varsCode (.const (.list .nat) [0])) .listAppend

/-- The two polarities. -/
def polsCode : Code SatTy (.list .nat) := .const (.list .nat) [0, 1]

/-- The environment `(variables, m)`. -/
def envCode : Code SatTy EnvTy := .pair varsCode .listLen

variable {α : Ty}

/-- The clause count `m`, read off the environment. -/
def envM : Code (.pair EnvTy α) .nat := .comp .fst .snd

/-- The variable count `n`, recomputed from the environment's variable list. -/
def envN : Code (.pair EnvTy α) .nat := .comp (.comp .fst .fst) .listLen

/-! ## The element lists

Elements are positions, so the entries are ignored; only the lengths carry
information. Each list is assembled by `Code.cross` and `listAppend` from lists
the program already has. -/

/-- A list of `l₁.length * l₂.length` ignored labels. -/
def unitsProd (l₁ l₂ : Code SatTy (.list .nat)) : Code SatTy (.list .nat) :=
  .comp (.pair l₁ l₂) (.comp Code.cross (.listMap (.const .nat 0)))

/-- The external elements: one per (variable slot, clause, polarity), so
`(n + 1) * (m * 2)` of them. -/
def extElems : Code SatTy (.list .nat) :=
  unitsProd slotsCode (unitsProd clauseUnits polsCode)

/-- The internal elements: the `(n + 1) * m` truth-setting ring elements, then
the `m` clause-testing elements, then the `m * n` garbage-collection
elements. -/
def slotElems : Code SatTy (.list .nat) :=
  .comp (.pair (unitsProd slotsCode clauseUnits)
      (.comp (.pair clauseUnits (unitsProd clauseUnits varsCode)) .listAppend))
    .listAppend

/-! ## The numberings

The three arithmetic formulas that realize the mathematical layer's tags as
positions. -/

/-- The external element `(i, j, b)`, numbered `2 * (m * i + j) + b`. -/
def extIdxOf {σ : Ty} (m i j b : Code σ .nat) : Code σ .nat :=
  Code.add (Code.mul (.const .nat 2) (Code.add (Code.mul m i) j)) b

/-- The truth-setting ring element `(i, j)`, numbered `m * i + j`. -/
def ringIdxOf {σ : Ty} (m i j : Code σ .nat) : Code σ .nat :=
  Code.add (Code.mul m i) j

/-- The clause-testing element of clause `j`, numbered above every ring
element. -/
def testIdxOf {σ : Ty} (n m j : Code σ .nat) : Code σ .nat :=
  Code.add (Code.mul (Code.add n (.const .nat 1)) m) j

/-- The garbage-collection element `(j, i')`, numbered above every testing
element. -/
def junkIdxOf {σ : Ty} (n m j i : Code σ .nat) : Code σ .nat :=
  Code.add (Code.add (Code.mul (Code.add n (.const .nat 1)) m) m)
    (Code.add (Code.mul n j) i)

/-! ## The four families of triples -/

/-- The variable slot of a ring position `(i, j)`. -/
def ringI : Code (.pair EnvTy (.pair .nat .nat)) .nat := .comp .snd .fst

/-- The clause index of a ring position `(i, j)`. -/
def ringJ : Code (.pair EnvTy (.pair .nat .nat)) .nat := .comp .snd .snd

/-- The cyclic successor of the clause index — `Sat3dm.next` in closed form
(`next_val`): the ordinary successor, wrapping to zero at the end. This is the
shift that closes each truth-setting component into a ring. -/
def nextJ : Code (.pair EnvTy (.pair .nat .nat)) .nat :=
  .branch (.comp (.pair (Code.add ringJ (.const .nat 1)) envM) .natEq)
    (.const .nat 0) (Code.add ringJ (.const .nat 1))

/-- The "`i` is true" ring triple: it consumes the *negative* external
element. -/
def trueTripCode : Code (.pair EnvTy (.pair .nat .nat)) TripleTy :=
  .pair (extIdxOf envM ringI ringJ (.const .nat 0))
    (.pair (ringIdxOf envM ringI ringJ) (ringIdxOf envM ringI ringJ))

/-- The "`i` is false" ring triple: it consumes the positive external element
and takes the *next* ring element. -/
def falseTripCode : Code (.pair EnvTy (.pair .nat .nat)) TripleTy :=
  .pair (extIdxOf envM ringI ringJ (.const .nat 1))
    (.pair (ringIdxOf envM ringI ringJ) (ringIdxOf envM ringI nextJ))

/-- The ring positions `(i, j)`: every variable slot against every clause. -/
def ringPositions : Code SatTy (.list (.pair .nat .nat)) :=
  .comp (.pair (.comp slotsCode Code.indices) (.comp clauseUnits Code.indices)) Code.cross

/-- The "all true" halves of the truth-setting components. -/
def trueList : Code SatTy (.list TripleTy) :=
  .comp (.pair envCode ringPositions) (.listMapEnv trueTripCode)

/-- The "all false" halves of the truth-setting components. -/
def falseList : Code SatTy (.list TripleTy) :=
  .comp (.pair envCode ringPositions) (.listMapEnv falseTripCode)

/-- The satisfaction-testing triple of one literal `(v, pol)` of clause `j`:
it consumes the external element that the ring of `v`'s slot releases exactly
when the literal holds, together with the clause's private pair. -/
def litTripCode : Code (.pair (.pair EnvTy .nat) LitTy) TripleTy :=
  .pair
    (extIdxOf (.comp (.comp .fst .fst) .snd)
      (.comp (.pair (.comp (.comp .fst .fst) .fst) (.comp .snd .fst)) slotOfCode)
      (.comp .fst .snd)
      (.branch (.comp .snd .snd) (.const .nat 1) (.const .nat 0)))
    (.pair
      (testIdxOf (.comp (.comp (.comp .fst .fst) .fst) .listLen)
        (.comp (.comp .fst .fst) .snd) (.comp .fst .snd))
      (testIdxOf (.comp (.comp (.comp .fst .fst) .fst) .listLen)
        (.comp (.comp .fst .fst) .snd) (.comp .fst .snd)))

/-- The testing triples of one enumerated clause `(c, j)`. -/
def clauseTests : Code (.pair EnvTy (.pair ClauseTy .nat)) (.list TripleTy) :=
  .comp (.pair (.pair .fst (.comp .snd .snd)) (.comp .snd .fst))
    (.listMapEnv litTripCode)

/-- The satisfaction-testing component: one triple per literal occurrence. -/
def testList : Code SatTy (.list TripleTy) :=
  .comp (.pair envCode .listEnum) (.comp (.listMapEnv clauseTests) .listJoin)

/-- The garbage-collection triple joining the internal pair `(j, i')` to an
arbitrary external element `w`. -/
def junkTripCode : Code (.pair EnvTy (.pair (.pair .nat .nat) .nat)) TripleTy :=
  .pair (.comp .snd .snd)
    (.pair (junkIdxOf envN envM (.comp (.comp .snd .fst) .fst)
              (.comp (.comp .snd .fst) .snd))
      (junkIdxOf envN envM (.comp (.comp .snd .fst) .fst)
        (.comp (.comp .snd .fst) .snd)))

/-- The garbage-collection component: every internal pair against every
external element. -/
def junkList : Code SatTy (.list TripleTy) :=
  .comp
    (.pair envCode
      (.comp
        (.pair
          (.comp (.pair (.comp clauseUnits Code.indices) (.comp varsCode Code.indices))
            Code.cross)
          (.comp extElems Code.indices))
        Code.cross))
    (.listMapEnv junkTripCode)

/-- The available triples: the two halves of every truth-setting ring, the
testing triples of every literal occurrence, and the garbage-collection
triples. -/
def triplesCode : Code SatTy (.list TripleTy) :=
  .comp (.pair trueList
      (.comp (.pair falseList (.comp (.pair testList junkList) .listAppend)) .listAppend))
    .listAppend

end SatToMatching3DCode

open SatToMatching3DCode

/-- The SAT → 3-DIMENSIONAL MATCHING instance map as a program: the external
element list, the internal element list twice (the `X` and `Y` coordinates
share it), and the triples of the three components. -/
def satToMatching3DCode : Code SatTy Matching3DTy :=
  .pair extElems (.pair slotElems (.pair slotElems triplesCode))

/-- One clause, one positive literal `x₀`. There is one variable and one
clause, so two variable slots (the variable's and the dummy's), four external
elements `2 * (m * i + j) + b = 2 * i + b`, and four internal ones: the two
ring elements `0, 1`, the clause's testing element `2`, and the single garbage
element `3`. The ring of slot `i` contributes `(2i, i, i)` and `(2i+1, i, i)`
(the cyclic shift is the identity when there is one clause); the literal
contributes `(1, 2, 2)`; the garbage element pairs with every external
element. -/
example : satToMatching3DCode.eval [[(0, true)]] =
    ([0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
      [(0, 0, 0), (2, 1, 1), (1, 0, 0), (3, 1, 1), (1, 2, 2),
        (0, 3, 3), (1, 3, 3), (2, 3, 3), (3, 3, 3)]) := by rfl

/-- Two literals of distinct variables in one clause: three variable slots,
six external elements, and the two testing triples `(1, 3, 3)` and `(2, 3, 3)`
— the positive literal claims the external element its ring releases when true,
the negative one the element released when false. -/
example : satToMatching3DCode.eval [[(5, true), (7, false)]] =
    ([0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
      [(0, 0, 0), (2, 1, 1), (4, 2, 2), (1, 0, 0), (3, 1, 1), (5, 2, 2),
        (1, 3, 3), (2, 3, 3),
        (0, 4, 4), (1, 4, 4), (2, 4, 4), (3, 4, 4), (4, 4, 4), (5, 4, 4),
        (0, 5, 5), (1, 5, 5), (2, 5, 5), (3, 5, 5), (4, 5, 5), (5, 5, 5)]) := by rfl

/-- The empty clause: no literal claims the clause's testing element `1`, and
no triple in the instance covers it, so the output is a no-instance — matching
the unsatisfiability of `[[]]`. -/
example : satToMatching3DCode.eval [[]] =
    ([0, 0], [0, 0], [0, 0], [(0, 0, 0), (1, 0, 0)]) := by rfl

/-- The empty formula: no elements and no triples, and the empty matching
works — a yes-instance, as it must be. -/
example : satToMatching3DCode.eval [] = ([], [], [], []) := by rfl

end Cert
end Hardness


