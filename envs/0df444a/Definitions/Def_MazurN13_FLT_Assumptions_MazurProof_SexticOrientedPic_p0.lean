-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticOrientedPic_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticOrientedPic_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:58:48.697621+00:00
-- url     : https://prove2.me/theorems/9dee0e68-51eb-4511-bfa8-08107f8a6881
-- title:
--   FLT.Assumptions.MazurProof.SexticOrientedPic source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticOrientedPic

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticOrientedPic
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordUnit_p0

set_option autoImplicit false




/-!
# The concrete oriented Picard group of a smooth sextic

The affine coordinate ring omits the two points at infinity.  An
`InfinityOrder` supplies the order at the chosen point before quotienting by
principal fractional ideals.  This file packages balanced Mumford data into
that oriented quotient for an arbitrary smooth monic sextic model.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

/-- The oriented Picard group attached to the affine sextic and the chosen
order at infinity. -/
abbrev ConcretePic : Type u :=
  OrientedPic M O

/-- The oriented invertible fractional ideal represented by balanced Mumford
data. -/
def mumfordRaw (D : Mumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D.toSemi,
    Multiplicative.ofAdd ((D.nInf : ℤ) - 1))

/-- The oriented Picard class of a balanced Mumford representative. -/
def classOf (D : Mumford M) : ConcretePic M O :=
  Additive.ofMul <|
    QuotientGroup.mk'
      (principalOriented M O).range
      (mumfordRaw M D)

theorem classOf_eq_iff (D₁ D₂ : Mumford M) :
    classOf M O D₁ = classOf M O D₂ ↔
      ∃ α : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁.toSemi *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
            mumfordIdealUnit M D₂.toSemi ∧
        Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) * O.ordPlus α =
            Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₁) =
      QuotientGroup.mk'
      (principalOriented M O).range
        (mumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hz
    refine ⟨α, ?_, ?_⟩
    · exact congrArg Prod.fst hmul
    · exact congrArg Prod.snd hmul
  · rintro ⟨α, hIdeal, hInf⟩
    refine ⟨principalOriented M O α,
      MonoidHom.mem_range.mpr ⟨α, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf

theorem zero_mumfordIdeal :
    mumfordIdeal M (zero M).u (zero M).v = ⊤ := by
  rw [zero_u, zero_v, mumfordIdeal]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp [xClass_one])

theorem mumfordIdealUnit_zero :
    mumfordIdealUnit M (zero M).toSemi = 1 := by
  apply Units.ext
  change (mumfordIdeal M 1 0 :
      FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 1
  rw [show mumfordIdeal M 1 0 = ⊤ from zero_mumfordIdeal M]
  rfl

@[simp] theorem classOf_zero : classOf M O (zero M) = 0 := by
  change Additive.ofMul
      (QuotientGroup.mk'
        (principalOriented M O).range
        (mumfordRaw M (zero M))) = 0
  have hraw : mumfordRaw M (zero M) = 1 := by
    apply Prod.ext
    · exact mumfordIdealUnit_zero M
    · simp [mumfordRaw]
  rw [hraw, map_one]
  rfl

end

end MazurProof.SexticMumford


