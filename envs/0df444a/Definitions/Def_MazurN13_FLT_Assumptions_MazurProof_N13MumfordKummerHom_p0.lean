-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerHom_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerHom_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:21:20.196591+00:00
-- url     : https://prove2.me/theorems/f170e38b-622b-4cf4-9e87-234cdcfdfb7d
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordKummerHom source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordKummerHom

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordKummerHom
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerRelation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Infinity_p0

set_option autoImplicit false




/-!
# The N13 fake-Kummer homomorphism from balanced representatives

Principal-ideal invariance and its three-ideal multiplicativity theorem allow
the raw value `u(θ)` to descend to the oriented Picard group.  Only existence
of balanced representatives is needed: a noncomputable section of `classOf`
may be chosen, and the principal-relation theorems prove that the resulting
map is independent of this choice and additive.

In particular, uniqueness of Mumford normal forms and a transported group law
on the representation type are not prerequisites for the Kummer map.
-/

namespace MazurProof.N13MumfordKummerHom

noncomputable section

open SexticMumford

abbrev M : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ

abbrev O : SexticMumford.InfinityOrder M :=
  N13Infinity.positiveInfinityOrder ℚ

abbrev G : Type :=
  SexticMumford.ConcretePic M O

abbrev Target : Type :=
  N13MumfordKummerValue.FakeTarget

/-- A chosen balanced representative of each oriented Picard class. -/
def representative
    (hrep : Function.Surjective (classOf M O)) (P : G) :
    N13Mumford.Mumford ℚ :=
  Function.surjInv hrep P

@[simp] theorem classOf_representative
    (hrep : Function.Surjective (classOf M O)) (P : G) :
    classOf M O (representative hrep P) = P :=
  Function.surjInv_eq hrep P

/-- The fake-Kummer homomorphism obtained from any surjective balanced
Mumford representation. -/
def mumfordKummer
    (hrep : Function.Surjective (classOf M O)) :
    G →+ Target where
  toFun P :=
    N13MumfordKummerValue.mumfordFakeClass
      (representative hrep P)
  map_zero' := by
    have h :=
      N13MumfordKummerRelation.mumfordFakeClass_eq_of_classOf_eq
        O (representative hrep 0) (SexticMumford.zero M)
        (by rw [classOf_representative, classOf_zero])
    simpa using h
  map_add' P Q := by
    apply
      N13MumfordKummerRelation.mumfordFakeClass_add_of_class_add
        O (representative hrep P) (representative hrep Q)
          (representative hrep (P + Q))
    rw [classOf_representative, classOf_representative,
      classOf_representative]

@[simp] theorem mumfordKummer_apply
    (hrep : Function.Surjective (classOf M O)) (P : G) :
    mumfordKummer hrep P =
      N13MumfordKummerValue.mumfordFakeClass
        (representative hrep P) :=
  rfl

/-- The descended value agrees with the raw value of every balanced
representative, not only with the chosen section. -/
theorem mumfordKummer_classOf
    (hrep : Function.Surjective (classOf M O))
    (D : N13Mumford.Mumford ℚ) :
    mumfordKummer hrep (classOf M O D) =
      N13MumfordKummerValue.mumfordFakeClass D := by
  rw [mumfordKummer_apply]
  exact
    N13MumfordKummerRelation.mumfordFakeClass_eq_of_classOf_eq
      O (representative hrep (classOf M O D)) D
      (classOf_representative hrep (classOf M O D))

/-- Different choices of a surjectivity proof define the same Kummer
homomorphism. -/
theorem mumfordKummer_eq
    (hrep₁ hrep₂ : Function.Surjective (classOf M O)) :
    mumfordKummer hrep₁ = mumfordKummer hrep₂ := by
  apply AddMonoidHom.ext
  intro P
  exact
    N13MumfordKummerRelation.mumfordFakeClass_eq_of_classOf_eq
      O (representative hrep₁ P) (representative hrep₂ P)
      ((classOf_representative hrep₁ P).trans
        (classOf_representative hrep₂ P).symm)

end

end MazurProof.N13MumfordKummerHom


