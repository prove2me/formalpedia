-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LowDegreeKummerHom_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13LowDegreeKummerHom_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:17:29.012701+00:00
-- url     : https://prove2.me/theorems/db8f4d12-17cd-4e68-a072-25e41ef7b9a4
-- title:
--   FLT.Assumptions.MazurProof.N13LowDegreeKummerHom source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13LowDegreeKummerHom

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13LowDegreeKummerHom
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerRelation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13Infinity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordStructuralReduction_p0

set_option autoImplicit false




/-!
# The N13 fake-Kummer homomorphism from low-degree semirepresentatives

The fake Kummer value depends on the affine Mumford ideal and the polynomial
`u`, but not on the separate infinity-balance inequalities.  The structural
Cantor reduction already gives every oriented Picard class a semirepresentative
with `deg u ≤ 2`.

We therefore attach to such a semirepresentative an auxiliary balanced
Mumford datum with the same `(u,v)` and infinity coordinate zero.  This datum
is used only to reuse the existing `u(θ)` and principal-relation theorems; its
oriented class is not substituted for the original semirepresentative's
class.  Principal relations are extracted from the original oriented
classes, where their actual integer infinity coordinates are retained.

This removes infinity balancing from the dependency chain of the N13
fake-Kummer homomorphism.
-/

namespace MazurProof.N13LowDegreeKummerHom

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

abbrev LowRep : Type :=
  SexticMumford.LowDegreeSemi M

/-- Forget the original infinity coordinate only for evaluation of `u(θ)`.
The affine ideal and all its proofs are unchanged. -/
def asMumford (D : LowRep) : N13Mumford.Mumford ℚ where
  u := D.toSemi.u
  v := D.toSemi.v
  nInf := 0
  u_monic := D.toSemi.u_monic
  deg_u := D.degree_le_two
  v_reduced := D.toSemi.v_reduced
  curve_dvd := D.toSemi.curve_dvd
  infinity_bound := by
    simpa using D.degree_le_two

@[simp] theorem asMumford_u (D : LowRep) :
    (asMumford D).u = D.toSemi.u := rfl

@[simp] theorem asMumford_v (D : LowRep) :
    (asMumford D).v = D.toSemi.v := rfl

@[simp] theorem asMumford_nInf (D : LowRep) :
    (asMumford D).nInf = 0 := rfl

theorem mumfordIdealUnit_asMumford (D : LowRep) :
    mumfordIdealUnit M (asMumford D).toSemi =
      mumfordIdealUnit M D.toSemi := by
  apply Units.ext
  rfl

/-- The oriented class uses the original integer infinity coordinate. -/
def lowClass (D : LowRep) : G :=
  semiMumfordClass M O D.toSemi

/-- The raw fake value uses only the shared affine data `(u,v)`. -/
def lowFakeClass (D : LowRep) : Target :=
  N13MumfordKummerValue.mumfordFakeClass (asMumford D)

/-- The low-degree semirepresentative of the identity. -/
def zeroLow : LowRep where
  toSemi := (SexticMumford.zero M).toSemi
  degree_le_two := (SexticMumford.zero M).deg_u

@[simp] theorem lowClass_zero :
    lowClass zeroLow = 0 := by
  change
    semiMumfordClass M O (SexticMumford.zero M).toSemi = 0
  rw [semiMumfordClass_toSemi, classOf_zero]

@[simp] theorem lowFakeClass_zero :
    lowFakeClass zeroLow = 0 := by
  change
    N13MumfordKummerValue.mumfordFakeClass
        (asMumford zeroLow) =
      0
  change
    Additive.ofMul
        ((((N13MumfordKummerValue.uThetaUnit
          (asMumford zeroLow) :
            N13MumfordKummerValue.Lˣ))) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) =
      0
  have hu :
      N13MumfordKummerValue.uThetaUnit
          (asMumford zeroLow) = 1 := by
    apply Units.ext
    change
      N13MumfordKummerValue.uTheta (asMumford zeroLow) = 1
    simp [N13MumfordKummerValue.uTheta_eq_mk,
      asMumford, zeroLow]
  rw [hu]
  rfl

/-- Equality of original oriented classes gives equality of fake values.
Only the finite principal-ideal component is consumed by the existing
principal-relation theorem. -/
theorem lowFakeClass_eq_of_class_eq
    (D₁ D₂ : LowRep)
    (h : lowClass D₁ = lowClass D₂) :
    lowFakeClass D₁ = lowFakeClass D₂ := by
  obtain ⟨alpha, hIdeal, -⟩ :=
    (semiMumfordClass_eq_iff M O D₁.toSemi D₂.toSemi).mp h
  apply
    N13MumfordKummerRelation.mumfordFakeClass_eq_of_principal_relation
      (asMumford D₁) (asMumford D₂) alpha
  simpa only [mumfordIdealUnit_asMumford] using hIdeal

/-- Addition of original oriented classes gives multiplication of the
affine Mumford ideals modulo a principal ideal, hence addition of fake
values. -/
theorem lowFakeClass_add_of_class_add
    (D₁ D₂ D₃ : LowRep)
    (h : lowClass D₃ = lowClass D₁ + lowClass D₂) :
    lowFakeClass D₃ = lowFakeClass D₁ + lowFakeClass D₂ := by
  have hclass :
      QuotientGroup.mk'
          (principalOriented M O).range
          (semiMumfordRaw M D₁.toSemi *
            semiMumfordRaw M D₂.toSemi) =
        QuotientGroup.mk'
          (principalOriented M O).range
          (semiMumfordRaw M D₃.toSemi) := by
    rw [map_mul]
    exact h.symm
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  obtain ⟨z, hz, hmul⟩ := hclass
  obtain ⟨alpha, rfl⟩ := MonoidHom.mem_range.mp hz
  have hIdeal := congrArg Prod.fst hmul
  apply
    N13MumfordKummerRelation.mumfordFakeClass_add_of_product_principal_relation
      (asMumford D₁) (asMumford D₂) (asMumford D₃) alpha
  simpa only [semiMumfordRaw, principalOriented,
    MonoidHom.prod_apply, Prod.fst_mul,
    mumfordIdealUnit_asMumford] using hIdeal

/-- Phase I of structural reduction is already surjective onto the
oriented Picard group. -/
theorem lowClass_surjective :
    Function.Surjective lowClass := by
  intro P
  obtain ⟨D, hD⟩ :=
    exists_lowDegreeSemiRepresentative M O P
  exact ⟨D, hD⟩

/-- A chosen low-degree semirepresentative of an oriented Picard class. -/
def representative (P : G) : LowRep :=
  Function.surjInv lowClass_surjective P

@[simp] theorem lowClass_representative (P : G) :
    lowClass (representative P) = P :=
  Function.surjInv_eq lowClass_surjective P

/-- The N13 fake-Kummer homomorphism constructed without an infinity
balancing theorem. -/
def mumfordKummer : G →+ Target where
  toFun P := lowFakeClass (representative P)
  map_zero' := by
    have h :=
      lowFakeClass_eq_of_class_eq
        (representative 0) zeroLow
        (by rw [lowClass_representative, lowClass_zero])
    simpa using h
  map_add' P Q := by
    apply lowFakeClass_add_of_class_add
      (representative P) (representative Q)
        (representative (P + Q))
    rw [lowClass_representative, lowClass_representative,
      lowClass_representative]

@[simp] theorem mumfordKummer_apply (P : G) :
    mumfordKummer P = lowFakeClass (representative P) :=
  rfl

/-- The descended homomorphism agrees with every low-degree
semirepresentative, not only with the chosen section. -/
theorem mumfordKummer_lowClass (D : LowRep) :
    mumfordKummer (lowClass D) = lowFakeClass D := by
  rw [mumfordKummer_apply]
  exact lowFakeClass_eq_of_class_eq
    (representative (lowClass D)) D
    (lowClass_representative (lowClass D))

end

end MazurProof.N13LowDegreeKummerHom


