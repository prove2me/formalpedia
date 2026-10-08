-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartPic_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartPic_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:15:55.629977+00:00
-- url     : https://prove2.me/theorems/29d83754-c057-4530-8794-634dfb7d5f96
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicAbelChartPic
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SmallMumfordRigidity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartData_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicCoordinateBaseChange_p0

set_option autoImplicit false




/-!
# The N13 two-adic Abel chart inside the oriented Picard group

Every pair in the two distinguished residue disks gives smooth integral
generalized Mumford data.  After extending coefficients and completing the
square, the resulting standard sextic semirepresentative already has degree
two and infinity balance zero.  It is therefore a balanced Mumford
representative over `ℚ₂`.

Unique balanced normal forms make the resulting map to the oriented Picard
group injective.  Translating by the distinguished base pair gives the
faithful chart centred at the identity.  Thus the remaining geometric input
for the formal-kernel argument is existence of representatives in this
chart, not their uniqueness.
-/

open Polynomial

namespace MazurProof.N13TwoAdicAbelChartPic

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev Q₂ : Type :=
  ℚ_[2]

abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair

abbrev Pic : Type :=
  SexticMumford.ConcretePic
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)

namespace DiskPair

variable (P : DiskPair)

theorem u_natDegree :
    P.u.natDegree = 2 := by
  rw [N13TwoAdicAbelChartData.DiskPair.u,
    Polynomial.natDegree_mul
      (monic_X_sub_C P.x₀).ne_zero
      (monic_X_sub_C P.x₁).ne_zero]
  simp

theorem sexticSemi_u_natDegree :
    (N13TwoAdicMumfordTransport.sexticSemi
      P.smoothMumford 0).u.natDegree = 2 := by
  rw [N13TwoAdicMumfordTransport.sexticSemi_u,
    N13TwoAdicAbelChartData.DiskPair.smoothMumford_u,
    N13TwoAdicMumfordTransport.mapPoly_apply,
    P.u_monic.natDegree_map]
  exact P.u_natDegree

/-- The standard sextic representative of a two-disk divisor is already
balanced: its affine degree is two and its infinity multiplicity is zero. -/
def mumford :
    N13Mumford.Mumford Q₂ := by
  let D :=
    N13TwoAdicMumfordTransport.sexticSemi
      P.smoothMumford 0
  exact
    { u := D.u
      v := D.v
      nInf := 0
      u_monic := D.u_monic
      deg_u := by
        rw [P.sexticSemi_u_natDegree]
      v_reduced := D.v_reduced
      curve_dvd := D.curve_dvd
      infinity_bound := by
        rw [P.sexticSemi_u_natDegree] }

@[simp] theorem mumford_u :
    P.mumford.u =
      N13TwoAdicMumfordTransport.mapPoly P.u := rfl

@[simp] theorem mumford_v :
    P.mumford.v =
      (N13TwoAdicMumfordTransport.sexticSemi
        P.smoothMumford 0).v := rfl

@[simp] theorem mumford_nInf :
    P.mumford.nInf = 0 := rfl

/-- The oriented Picard class of the two-disk divisor. -/
def pic : Pic :=
  SexticMumford.classOf
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
    P.mumford

/-- Distinct pairs in the two residue disks give distinct Picard classes.
The proof is global normal-form rigidity followed by faithfulness of
coefficient extension. -/
theorem pic_injective :
    Function.Injective DiskPair.pic := by
  intro P Q hPQ
  have hM : P.mumford = Q.mumford :=
    N13SmallMumfordRigidity.classOf_injective Q₂ hPQ
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  apply Polynomial.map_injective
    N13TwoAdicMumfordTransport.coeffMap
    (IsFractionRing.injective
      N13TwoAdicMumfordTransport.R₂ Q₂)
  simpa only [mumford_u,
    N13TwoAdicMumfordTransport.mapPoly_apply] using
    congrArg SexticMumford.Mumford.u hM

/-- Translate the chart so that the distinguished divisor is the identity. -/
def centeredPic : DiskPair → Pic :=
  fun P => P.pic -
    pic N13TwoAdicAbelChartData.basePair

@[simp] theorem centeredPic_basePair :
    centeredPic N13TwoAdicAbelChartData.basePair = 0 := by
  simp [centeredPic]

theorem centeredPic_injective :
    Function.Injective centeredPic := by
  intro P Q hPQ
  apply pic_injective
  exact sub_left_injective hPQ

end DiskPair

end

end MazurProof.N13TwoAdicAbelChartPic


