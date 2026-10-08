-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FullNormPair_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13FullNormPair_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:12:13.293469+00:00
-- url     : https://prove2.me/theorems/ce7fcdfb-8e3b-4178-bc9e-d07ab9998273
-- title:
--   FLT.Assumptions.MazurProof.N13FullNormPair source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13FullNormPair

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13FullNormPair
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_EvenSexticNormPair_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticIrreducible_p0

set_option autoImplicit false




/-!
# The full norm-pair target for N13

This file specializes the abstract even-sextic target to the sextic field
`L = ℚ[θ]`.  Its full target remembers `(α,s)` with `N(α)=s²`, before
forgetting `s` to obtain the existing fake square-class target.

The kernel of forgetting has at most the identity and the sign class
represented by `(1,-1)`.  This is target algebra only: it does not assert
the hard principal-genus theorem for the Picard Kummer map.
-/

namespace MazurProof.N13FullNormPair

noncomputable section

open N13SexticSquareclass

abbrev L : Type :=
  SexticAlgebra

local instance sexticAlgebraField : Field L :=
  N13SexticIrreducible.sexticAlgebraField

/-- The norm on units of the N13 sextic field. -/
def normUnits : Lˣ →* ℚˣ :=
  Units.map (Algebra.norm ℚ)

/-- Rational scalar units inside the sextic field. -/
def scalarUnits : ℚˣ →* Lˣ :=
  FakeSquareClass.scalarUnitsMap (algebraMap ℚ L)

theorem finrank_L :
    Module.finrank ℚ L = 6 := by
  change
    Module.finrank ℚ
      (AdjoinRoot N13SexticSquareclass.f) = 6
  rw [(AdjoinRoot.powerBasis
    (by
      simpa [N13SexticSquareclass.f] using
        (N13Mumford.f_monic (K := ℚ)).ne_zero)).finrank]
  change N13SexticSquareclass.f.natDegree = 6
  simpa [N13SexticSquareclass.f] using
    (N13Mumford.f_natDegree (K := ℚ))

/-- A rational scalar has sextic norm `q⁶`. -/
@[simp] theorem normUnits_scalarUnits (q : ℚˣ) :
    normUnits (scalarUnits q) = q ^ 6 := by
  apply Units.ext
  change
    Algebra.norm ℚ (algebraMap ℚ L (q : ℚ)) =
      (q : ℚ) ^ 6
  simpa [finrank_L] using
    (Algebra.norm_algebraMap (R := ℚ) (S := L) (q : ℚ))

abbrev NormPair : Type :=
  EvenSexticNormPair.NormPair normUnits

abbrev FullTarget : Type :=
  EvenSexticNormPair.FullTarget
    normUnits scalarUnits normUnits_scalarUnits

abbrev FakeTarget : Type :=
  FakeSquareClass.Target (algebraMap ℚ L)

/-- Forget the chosen rational square root of the norm. -/
abbrev forget : FullTarget →* FakeTarget :=
  EvenSexticNormPair.forget
    normUnits scalarUnits normUnits_scalarUnits

theorem minusOne_sq :
    (-1 : ℚˣ) ^ 2 = 1 := by
  simp

/-- The possible extra sign class in the full target. -/
abbrev signClass : FullTarget :=
  QuotientGroup.mk'
      (EvenSexticNormPair.fullGauge
        normUnits scalarUnits normUnits_scalarUnits)
    (EvenSexticNormPair.signPair normUnits (-1) minusOne_sq)

/-- The only rational units with square one are `1` and `-1`. -/
theorem ratUnit_sq_eq_one
    (ε : ℚˣ) (hε : ε ^ 2 = 1) :
    ε = 1 ∨ ε = -1 := by
  have hval : ((ε : ℚ) ^ 2) = 1 := by
    exact congrArg (fun u : ℚˣ => (u : ℚ)) hε
  have hfactor :
      ((ε : ℚ) - 1) * ((ε : ℚ) + 1) = 0 := by
    calc
      ((ε : ℚ) - 1) * ((ε : ℚ) + 1) =
          (ε : ℚ) ^ 2 - 1 := by ring
      _ = 0 := by rw [hval]; norm_num
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    apply Units.ext
    change (ε : ℚ) = 1
    exact sub_eq_zero.mp hminus
  · right
    apply Units.ext
    change (ε : ℚ) = -1
    exact eq_neg_of_add_eq_zero_left hplus

/-- The forgetting kernel has exactly the two displayed alternatives; the
theorem does not require proving that those alternatives are distinct. -/
theorem forget_eq_one_iff (z : FullTarget) :
    forget z = 1 ↔ z = 1 ∨ z = signClass := by
  exact
    EvenSexticNormPair.forget_eq_one_iff_eq_one_or_eq_sign
      normUnits scalarUnits normUnits_scalarUnits
      (-1 : ℚˣ) minusOne_sq ratUnit_sq_eq_one z

/-- The concrete full N13 target has exponent two. -/
@[simp] theorem fullTarget_sq_eq_one (z : FullTarget) :
    z ^ 2 = 1 :=
  EvenSexticNormPair.fullTarget_sq_eq_one
    normUnits scalarUnits normUnits_scalarUnits z

end

end MazurProof.N13FullNormPair


