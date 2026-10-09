-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordCenteredDoublingAdapter_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordCenteredDoublingAdapter_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T20:02:55.547855+00:00
-- url     : https://prove2.me/theorems/ecb0b6c9-0380-48f9-9a09-976c21f41e60
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingAdapter source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingAdapter

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingAdapter
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordCenteredDoublingJet_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RationalKernelDoublingAdapter_p0

set_option autoImplicit false




/-!
# Cross-coefficient adapter for the N13 rational-kernel doubling law

For a recovered disk pair `P` and the pair `Q` selected for twice its Picard
class, the polynomial

`P.u² - uBase * Q.u`

measures failure of the proposed double to equal the centered square.  Only
its coefficients in degrees one and three are needed.  The centered
polynomial reducer turns those two quadratic memberships into literal disk
coordinate doubling, while the existing transition calculation identifies
the square transition with the same doubled coordinates.

This file performs that final subtraction.  It leaves the two
cross-coefficient memberships as the precise arithmetic input and introduces
no Picard-classification or separatedness assumption.
-/

namespace MazurProof.N13MumfordCenteredDoublingAdapter

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

open MazurProof.N13RationalKernelDoublingAdapter

/-- The pair selected at `2 • z` represents twice the centered Picard class
of the pair selected at `z`.  This is a formal consequence of pointwise
realization and additivity, independent of the coordinate calculation. -/
theorem centeredPic_pair_two_nsmul
    {H : AddSubgroup RationalPic}
    (F : NearBaseFamily H)
    (z : H) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (F.pair (2 • z)) =
      2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (F.pair z) := by
  calc
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
          (F.pair (2 • z)) =
        N13TwoAdicAbelChartSection.subgroupToPic H (2 • z) :=
      F.realize (2 • z)
    _ = 2 • N13TwoAdicAbelChartSection.subgroupToPic H z := by
      exact
        map_nsmul
          (N13TwoAdicAbelChartSection.subgroupToPic H) 2 z
    _ = 2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic
          (F.pair z) := by
      rw [F.realize z]

/-- The canonical disk pair recovered at `2 • z` is exactly the centered
Mumford-group double of the pair recovered at `z`.

This is representative-level wiring, not the missing Cantor coefficient
calculation.  Additivity first identifies the centered Picard classes; the
proved uniqueness of balanced N13 Mumford representatives then upgrades that
class equality to literal equality of Mumford data. -/
theorem recoveredPair_mumford_eq_centeredDouble
    {H : AddSubgroup RationalPic}
    (R : CanonicalMappedSpecialFamily H)
    (z : H) :
    N13TwoAdicAbelChartPic.DiskPair.mumford
        (R.recoveredPair (2 • z)) =
      2 • N13TwoAdicAbelChartPic.DiskPair.mumford
          (R.recoveredPair z) -
        N13TwoAdicAbelChartPic.DiskPair.mumford
          N13TwoAdicAbelChartData.basePair := by
  let P := R.recoveredPair z
  let Q := R.recoveredPair (2 • z)
  let B := N13TwoAdicAbelChartData.basePair
  have hP :
      N13TwoAdicAbelChartPic.DiskPair.pic P -
          N13TwoAdicAbelChartPic.DiskPair.pic B =
        N13TwoAdicAbelChartSection.subgroupToPic H z := by
    simpa only [P, B,
      N13TwoAdicAbelChartPic.DiskPair.centeredPic] using
      R.realize_recoveredPair z
  have hQ :
      N13TwoAdicAbelChartPic.DiskPair.pic Q -
          N13TwoAdicAbelChartPic.DiskPair.pic B =
        N13TwoAdicAbelChartSection.subgroupToPic H (2 • z) := by
    simpa only [Q, B,
      N13TwoAdicAbelChartPic.DiskPair.centeredPic] using
      R.realize_recoveredPair (2 • z)
  have hcenter :
      N13TwoAdicAbelChartPic.DiskPair.pic Q -
          N13TwoAdicAbelChartPic.DiskPair.pic B =
        2 • (N13TwoAdicAbelChartPic.DiskPair.pic P -
          N13TwoAdicAbelChartPic.DiskPair.pic B) := by
    calc
      N13TwoAdicAbelChartPic.DiskPair.pic Q -
          N13TwoAdicAbelChartPic.DiskPair.pic B =
          N13TwoAdicAbelChartSection.subgroupToPic H (2 • z) := hQ
      _ = 2 • N13TwoAdicAbelChartSection.subgroupToPic H z := by
        exact
          map_nsmul
            (N13TwoAdicAbelChartSection.subgroupToPic H) 2 z
      _ = 2 • (N13TwoAdicAbelChartPic.DiskPair.pic P -
          N13TwoAdicAbelChartPic.DiskPair.pic B) := by rw [hP]
  have hpic :
      N13TwoAdicAbelChartPic.DiskPair.pic Q =
        2 • N13TwoAdicAbelChartPic.DiskPair.pic P -
          N13TwoAdicAbelChartPic.DiskPair.pic B := by
    calc
      N13TwoAdicAbelChartPic.DiskPair.pic Q =
          (N13TwoAdicAbelChartPic.DiskPair.pic Q -
              N13TwoAdicAbelChartPic.DiskPair.pic B) +
            N13TwoAdicAbelChartPic.DiskPair.pic B := by abel
      _ = 2 • (N13TwoAdicAbelChartPic.DiskPair.pic P -
            N13TwoAdicAbelChartPic.DiskPair.pic B) +
          N13TwoAdicAbelChartPic.DiskPair.pic B := by rw [hcenter]
      _ = 2 • N13TwoAdicAbelChartPic.DiskPair.pic P -
          N13TwoAdicAbelChartPic.DiskPair.pic B := by
        simp only [two_nsmul]
        abel
  change
    N13TwoAdicAbelChartPic.DiskPair.mumford Q =
      2 • N13TwoAdicAbelChartPic.DiskPair.mumford P -
        N13TwoAdicAbelChartPic.DiskPair.mumford B
  apply N13SmallMumfordRigidity.classOf_injective ℚ_[2]
  simpa only [
      N13TwoAdicAbelChartPic.DiskPair.pic,
      sub_eq_add_neg,
      SexticMumford.classOf_add,
      SexticMumford.classOf_nsmul,
      SexticMumford.classOf_neg] using hpic

namespace FirstJetDoublingCompatibility

variable {H : AddSubgroup RationalPic}

/-- Cross coefficients one and three of the centered square supply the
existing first-jet comparison interface.

The hypotheses mention only the two recovered monic quadratics.  Coordinate
doubling follows from the denominator-free reducer; subtracting the existing
square-transition estimate then gives `coord(2z) - squareJet(z)` modulo the
moving coordinate ideal squared. -/
def ofCenteredCrossCoefficients
    (F : NearBaseFamily H)
    (h₁ :
      ∀ z,
        ((F.pair z).u ^ 2 -
          N13AbelChartBase.baseSmoothMumford.u *
            (F.pair (2 • z)).u).coeff 1 ∈
          N13TwoAdicKernelChart.coordIdeal F.coord z *
            N13TwoAdicKernelChart.coordIdeal F.coord z)
    (h₃ :
      ∀ z,
        ((F.pair z).u ^ 2 -
          N13AbelChartBase.baseSmoothMumford.u *
            (F.pair (2 • z)).u).coeff 3 ∈
          N13TwoAdicKernelChart.coordIdeal F.coord z *
            N13TwoAdicKernelChart.coordIdeal F.coord z) :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility F where
  compare z i := by
    let P := F.pair z
    let Q := F.pair (2 • z)
    let I := N13TwoAdicKernelChart.coordIdeal F.coord z
    have hcoord :
        F.coord (2 • z) i -
              (F.coord z i + F.coord z i) ∈
            I * I := by
      change
        N13TwoAdicAbelChartData.DiskPair.coord Q i -
              (N13TwoAdicAbelChartData.DiskPair.coord P i +
                N13TwoAdicAbelChartData.DiskPair.coord P i) ∈
            N13TwoAdicKernelChart.coordIdeal
                N13TwoAdicAbelChartData.DiskPair.coord P *
              N13TwoAdicKernelChart.coordIdeal
                N13TwoAdicAbelChartData.DiskPair.coord P
      apply
        N13MumfordCenteredDoublingJet.diskCoord_double_mod_sq_of_cross
          P Q
      · change
          ((F.pair z).u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u *
              (F.pair (2 • z)).u).coeff 1 ∈
            N13TwoAdicKernelChart.coordIdeal F.coord z *
              N13TwoAdicKernelChart.coordIdeal F.coord z
        exact h₁ z
      · change
          ((F.pair z).u ^ 2 -
            N13AbelChartBase.baseSmoothMumford.u *
              (F.pair (2 • z)).u).coeff 3 ∈
            N13TwoAdicKernelChart.coordIdeal F.coord z *
              N13TwoAdicKernelChart.coordIdeal F.coord z
        exact h₃ z
    have hsquare :
        F.squareJet z i -
              (F.coord z i + F.coord z i) ∈
            I * I := by
      simpa [I] using
        NearBaseFamily.squareJet_sub_double_coord_mem_sq F z i
    have hsub := (I * I).sub_mem hcoord hsquare
    convert hsub using 1
    ring

end FirstJetDoublingCompatibility

end

end MazurProof.N13MumfordCenteredDoublingAdapter


