-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFormalCech_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralFormalCech_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:34:45.214831+00:00
-- url     : https://prove2.me/theorems/c5455c22-736e-45b3-956b-d40a2ec1e7dd
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralFormalCech source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralFormalCech

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralFormalCech
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CechLaurentSeriesCore_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralCechObstruction_p0

set_option autoImplicit false




/-!
# The actual formal principal parts in the integral N13 Čech complex

The second N13 base point produces a regular tail containing
`1 / (1 + t)`.  This is why the proper/formal overlap must use Laurent
series rather than Laurent polynomials.

This file writes both integral principal parts as genuine formal Laurent
series, proves their cleared-denominator identities, and identifies their
classes with the finite connecting matrix already used by the
Čech--Nakayama argument.
-/

namespace MazurProof.N13IntegralFormalCech

noncomputable section

open HahnSeries
open scoped PowerSeries LaurentSeries

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralCechObstruction.R₂

abbrev Power : Type :=
  N13CechLaurentSeriesCore.Power (R := R₂)

abbrev Laurent : Type :=
  N13CechLaurentSeriesCore.Laurent (R := R₂)

abbrev Overlap : Type :=
  N13CechLaurentSeriesCore.Overlap (R := R₂)

abbrev Obstruction : Type :=
  N13IntegralCechObstruction.Obstruction

abbrev PrincipalParts : Type :=
  N13IntegralCechObstruction.PrincipalParts

/-- The Laurent monomial `tⁿ`. -/
def tPow (n : ℤ) : Laurent :=
  HahnSeries.single n 1

@[simp] theorem tPow_mul (m n : ℤ) :
    tPow m * tPow n = tPow (m + n) := by
  simp [tPow]

@[simp] theorem tPow_zero :
    tPow 0 = 1 := rfl

/-- The formal inverse of `1+t`, which exists because its constant
coefficient is one. -/
def invOnePlusT : Power :=
  PowerSeries.invOfUnit
    (1 + PowerSeries.X) 1

theorem onePlusT_mul_invOnePlusT :
    (1 + PowerSeries.X) * invOnePlusT = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp

/-- The regular inverse tail, included in the Laurent-series overlap. -/
def regularInvOnePlusT : Laurent :=
  (invOnePlusT : Laurent)

theorem one_add_t_mul_regularInvOnePlusT :
    (1 + tPow 1) * regularInvOnePlusT = 1 := by
  have h :=
    congrArg (fun f : Power => (f : Laurent))
      onePlusT_mul_invOnePlusT
  simpa [regularInvOnePlusT, tPow,
    PowerSeries.coe_add, PowerSeries.coe_one,
    PowerSeries.coe_mul, PowerSeries.coe_X] using h

theorem regularInvOnePlusT_coeff_of_neg
    (n : ℤ) (hn : n < 0) :
    regularInvOnePlusT.coeff n = 0 := by
  exact
    N13CechLaurentSeriesCore.includePower_coeff_of_neg
      invOnePlusT n hn

/-- The formal overlap function for the simple principal part at `(0,0)`.
Its scalar component is `t⁻² + 1 + t`; its `v` component is `t⁻²`. -/
def zeroPrincipalOverlap : Overlap :=
  (tPow (-2) + tPow 0 + tPow 1,
    tPow (-2))

/-- The formal overlap function for the simple principal part at
`(-1,0)`.  The nonnegative terms are the genuine `1/(1+t)` tails. -/
def negOnePrincipalOverlap : Overlap :=
  (tPow (-2) - tPow (-1) +
      (2 * tPow 0 + tPow 1) * regularInvOnePlusT,
    tPow (-2) - tPow (-1) +
      regularInvOnePlusT)

/-- The numerator `v + 1 + t² + t³`, represented in the basis `1,v`. -/
def conjugatePair : Overlap :=
  (tPow 0 + tPow 2 + tPow 3,
    tPow 0)

/-- Multiply both components of an overlap function by a scalar Laurent
series. -/
def scale (f : Laurent) (z : Overlap) : Overlap :=
  (f * z.1, f * z.2)

/-- Cleared transition identity for the principal part at `(0,0)`. -/
theorem zeroPrincipal_cleared :
    scale (tPow 2) zeroPrincipalOverlap =
      conjugatePair := by
  apply Prod.ext
  · simp [scale, zeroPrincipalOverlap, conjugatePair,
      mul_add, tPow_mul]
  · simp [scale, zeroPrincipalOverlap, conjugatePair,
      tPow_mul]

/-- Cleared transition identity for the principal part at `(-1,0)`. -/
theorem negOnePrincipal_cleared :
    scale (tPow 2 * (1 + tPow 1))
        negOnePrincipalOverlap =
      conjugatePair := by
  have hinv := one_add_t_mul_regularInvOnePlusT
  apply Prod.ext
  · change
      (tPow 2 * (1 + tPow 1)) *
          (tPow (-2) - tPow (-1) +
            (2 * tPow 0 + tPow 1) *
              regularInvOnePlusT) =
        tPow 0 + tPow 2 + tPow 3
    calc
      _ =
          tPow 2 * (1 + tPow 1) *
              (tPow (-2) - tPow (-1)) +
            tPow 2 * (2 * tPow 0 + tPow 1) *
              ((1 + tPow 1) * regularInvOnePlusT) := by
            ring
      _ =
          tPow 2 * (1 + tPow 1) *
              (tPow (-2) - tPow (-1)) +
            tPow 2 * (2 * tPow 0 + tPow 1) := by
            rw [hinv, mul_one]
      _ = tPow 0 + tPow 2 + tPow 3 := by
            simp [mul_add, add_mul, sub_eq_add_neg,
              tPow_mul]
            ring
  · change
      (tPow 2 * (1 + tPow 1)) *
          (tPow (-2) - tPow (-1) +
            regularInvOnePlusT) =
        tPow 0
    calc
      _ =
          tPow 2 * (1 + tPow 1) *
              (tPow (-2) - tPow (-1)) +
            tPow 2 *
              ((1 + tPow 1) * regularInvOnePlusT) := by
            ring
      _ =
          tPow 2 * (1 + tPow 1) *
              (tPow (-2) - tPow (-1)) +
            tPow 2 := by
            rw [hinv, mul_one]
      _ = tPow 0 := by
            simp [mul_add, add_mul, sub_eq_add_neg,
              tPow_mul]
            ring

@[simp] theorem obstruction_zeroPrincipalOverlap :
    N13CechLaurentSeriesCore.obstruction
        zeroPrincipalOverlap =
      ![(1 : R₂), 0] := by
  funext i
  fin_cases i <;>
    simp [N13CechLaurentSeriesCore.obstruction,
      zeroPrincipalOverlap, tPow]

@[simp] theorem obstruction_negOnePrincipalOverlap :
    N13CechLaurentSeriesCore.obstruction
        negOnePrincipalOverlap =
      ![(1 : R₂), -1] := by
  funext i
  fin_cases i
  · simp [N13CechLaurentSeriesCore.obstruction,
      negOnePrincipalOverlap, tPow,
      regularInvOnePlusT_coeff_of_neg]
  · simp [N13CechLaurentSeriesCore.obstruction,
      negOnePrincipalOverlap, tPow,
      regularInvOnePlusT_coeff_of_neg]

/-- The genuine formal principal-part map. -/
def principalOverlap :
    PrincipalParts →ₗ[R₂] Overlap where
  toFun a :=
    a 0 • zeroPrincipalOverlap +
      a 1 • negOnePrincipalOverlap
  map_add' a b := by
    simp only [Pi.add_apply, add_smul]
    module
  map_smul' c a := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    module

/-- The two actual formal principal parts induce exactly the integral
connecting matrix computed earlier. -/
theorem obstruction_principalOverlap
    (a : PrincipalParts) :
    N13CechLaurentSeriesCore.obstruction
        (principalOverlap a) =
      N13IntegralCechObstruction.connectingMap a := by
  calc
    N13CechLaurentSeriesCore.obstruction
        (principalOverlap a) =
        a 0 •
            N13CechLaurentSeriesCore.obstruction
              zeroPrincipalOverlap +
          a 1 •
            N13CechLaurentSeriesCore.obstruction
              negOnePrincipalOverlap := by
          simp [principalOverlap]
    _ =
        a 0 • ![(1 : R₂), 0] +
          a 1 • ![(1 : R₂), -1] := by
          rw [obstruction_zeroPrincipalOverlap,
            obstruction_negOnePrincipalOverlap]
    _ =
        N13IntegralCechObstruction.connectingMap a := by
          funext i
          fin_cases i <;>
            simp [N13IntegralCechObstruction.connectingMap]

/-- The actual formal principal overlap and the canonical obstruction
representative differ by the sum of the two chart images. -/
theorem principalOverlap_mod_chart_images
    (a : PrincipalParts) :
    principalOverlap a -
        (0,
          N13CechLaurentSeriesCore.obstructionRepresentative
            (N13IntegralCechObstruction.connectingMap a)) ∈
      N13CechLaurentSeriesCore.affineSections (R := R₂) ⊔
        N13CechLaurentSeriesCore.infinitySections (R := R₂) := by
  rw [← N13CechLaurentSeriesCore.ker_obstruction]
  apply LinearMap.mem_ker.mpr
  rw [map_sub, obstruction_principalOverlap]
  apply sub_eq_zero.mpr
  funext i
  fin_cases i <;>
    simp [N13CechLaurentSeriesCore.obstruction]

/-! ## The genuine formal Čech quotient -/

abbrev FormalStructureCechH1 : Type :=
  N13CechLaurentSeriesCore.StructureCechH1 (R := R₂)

/-- Pass an actual formal overlap function to its additive Čech class. -/
def overlapClass :
    Overlap →ₗ[R₂] FormalStructureCechH1 :=
  Submodule.mkQ
    (N13CechLaurentSeriesCore.affineSections (R := R₂) ⊔
      N13CechLaurentSeriesCore.infinitySections (R := R₂))

/-- The obstruction equivalence evaluates an actual overlap class by its
two missing coefficients. -/
theorem structureCechH1Equiv_overlapClass
    (z : Overlap) :
    N13CechLaurentSeriesCore.structureCechH1Equiv
        (overlapClass z) =
      N13CechLaurentSeriesCore.obstruction z := by
  rfl

/-- The actual formal principal-part connecting map. -/
def principalToFormalStructureCechH1 :
    PrincipalParts →ₗ[R₂] FormalStructureCechH1 :=
  overlapClass.comp principalOverlap

/-- On the genuine formal Čech quotient, the actual principal parts are
exactly the inverse image of the integral obstruction matrix. -/
theorem principalToFormalStructureCechH1_apply
    (a : PrincipalParts) :
    principalToFormalStructureCechH1 a =
      N13CechLaurentSeriesCore.structureCechH1Equiv.symm
        (N13IntegralCechObstruction.connectingMap a) := by
  apply
    N13CechLaurentSeriesCore.structureCechH1Equiv.injective
  rw [
    N13CechLaurentSeriesCore.structureCechH1Equiv.apply_symm_apply]
  simp only [principalToFormalStructureCechH1,
    LinearMap.comp_apply]
  rw [structureCechH1Equiv_overlapClass]
  exact obstruction_principalOverlap a

/-- Nonspeciality over `ℤ₂`, now for the actual formal overlap containing
all power-series tails. -/
def principalToFormalStructureCechH1Equiv :
    PrincipalParts ≃ₗ[R₂] FormalStructureCechH1 :=
  N13IntegralCechObstruction.connectingEquiv.trans
    N13CechLaurentSeriesCore.structureCechH1Equiv.symm

theorem principalToFormalStructureCechH1Equiv_apply
    (a : PrincipalParts) :
    principalToFormalStructureCechH1Equiv a =
      principalToFormalStructureCechH1 a := by
  exact (principalToFormalStructureCechH1_apply a).symm

theorem principalToFormalStructureCechH1_surjective :
    Function.Surjective principalToFormalStructureCechH1 := by
  intro z
  obtain ⟨a, ha⟩ :=
    principalToFormalStructureCechH1Equiv.surjective z
  exact
    ⟨a,
      (principalToFormalStructureCechH1Equiv_apply a).symm.trans
        ha⟩

theorem principalToFormalStructureCechH1_range_eq_top :
    LinearMap.range principalToFormalStructureCechH1 = ⊤ :=
  LinearMap.range_eq_top.mpr
    principalToFormalStructureCechH1_surjective

/-- Formal additive `H¹` after twisting by the integral base divisor. -/
abbrev FormalTwistedCechH1 : Type :=
  FormalStructureCechH1 ⧸
    LinearMap.range principalToFormalStructureCechH1

noncomputable instance formalTwistedCechH1_subsingleton :
    Subsingleton FormalTwistedCechH1 := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact principalToFormalStructureCechH1_range_eq_top

theorem formalTwistedCechH1_eq_zero
    (z : FormalTwistedCechH1) :
    z = 0 :=
  Subsingleton.elim _ _

end

end MazurProof.N13IntegralFormalCech


