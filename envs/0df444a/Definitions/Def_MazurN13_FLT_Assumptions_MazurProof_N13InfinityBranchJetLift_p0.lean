-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBranchJetLift_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityBranchJetLift_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:51:31.547582+00:00
-- url     : https://prove2.me/theorems/48ed81c0-5eea-4ec8-bc55-10a919ef922c
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityBranchJetLift source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityBranchJetLift

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityBranchJetLift
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBranchJets_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralModelContraction_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Lift arbitrary finite generic jets on BOTH actual N13 infinity branches.
The witness is an ordinary integral chart element after multiplying the
prescribed jet pair by one explicitly obtained nonzero two-adic scalar.
-/

namespace MazurProof.N13InfinityBranchJetLift

noncomputable section
open Polynomial N13InfinityBranchJets
open scoped nonZeroDivisors
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Q₂ := N13TwoAdicInfinityCompatibility.Q₂
abbrev cMap := N13TwoAdicInfinityCompatibility.coeffMap
abbrev r₀q := N13TwoAdicInfinityCompatibility.powerMap r₀
abbrev r₁q := N13TwoAdicInfinityCompatibility.powerMap r₁

def differenceUnit : QPˣ :=
  Units.map N13TwoAdicInfinityCompatibility.powerMap.toMonoidHom
    N13FormalInfinitySplit.branchDifferenceUnit

theorem differenceUnit_coe : (differenceUnit : QP) = r₀q - r₁q := by
  change N13TwoAdicInfinityCompatibility.powerMap
      (N13FormalInfinitySplit.branchDifferenceUnit : P) = _
  rw [N13FormalInfinitySplit.branchDifferenceUnit_coe, map_sub]

theorem inverse_difference_mul : (↑(differenceUnit⁻¹) : QP) * (r₀q - r₁q) = 1 := by
  rw [← differenceUnit_coe]
  exact Units.inv_mul differenceUnit

def interpolationV (r s : QP) : QP := (r - s) * (↑(differenceUnit⁻¹) : QP)
def interpolationU (r s : QP) : QP := r - interpolationV r s * r₀q

theorem interpolation_plus (r s : QP) :
    interpolationU r s + interpolationV r s * r₀q = r := by
  unfold interpolationU
  ring

theorem interpolation_minus (r s : QP) :
    interpolationU r s + interpolationV r s * r₁q = s := by
  calc
    interpolationU r s + interpolationV r s * r₁q =
        r - interpolationV r s * (r₀q - r₁q) := by unfold interpolationU; ring
    _ = r - (r - s) := by
      rw [interpolationV, mul_assoc, inverse_difference_mul, mul_one]
    _ = s := by ring

local instance «instAlgebraPolynomialR₂Q₂» : Algebra R₂[X] Q₂[X] := Polynomial.algebra R₂ Q₂
local instance «instIsLocalizationPolynomialR₂MapMonoidHomCNonZeroDivisorsQ₂» : IsLocalization
    ((nonZeroDivisors R₂).map (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom) Q₂[X] :=
  Polynomial.isLocalization (nonZeroDivisors R₂) Q₂

theorem clear_two_polynomials (p q : Q₂[X]) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ a b : R₂[X],
      p * C (cMap c) = a.map cMap ∧ q * C (cMap c) = b.map cMap := by
  obtain ⟨a, b, d, hp, hq⟩ := IsLocalization.surj₂
    ((nonZeroDivisors R₂).map (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom) Q₂[X] p q
  obtain ⟨c, hc, hd⟩ := d.property
  change C c = (d : R₂[X]) at hd
  rw [← hd] at hp hq
  rw [Polynomial.algebraMap_def] at hp hq
  refine ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp hc, a, b, ?_, ?_⟩
  · change p * C (algebraMap R₂ Q₂ c) = a.map (algebraMap R₂ Q₂)
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_C] using hp
  · change q * C (algebraMap R₂ Q₂ c) = b.map (algebraMap R₂ Q₂)
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_C] using hq

theorem generic_plus_base (p : R₂[X]) :
    N13InfinityChartMarking.positiveExpansion (base p) = (p.map cMap : QP) := by
  change N13TwoAdicInfinityCompatibility.powerMap (plus (base p)) = _
  rw [plus_base, beta_eq_coe]
  ext i
  simp [N13TwoAdicInfinityCompatibility.powerMap]

theorem generic_minus_base (p : R₂[X]) :
    N13InfinityChartMarking.negativeExpansion (base p) = (p.map cMap : QP) := by
  change N13TwoAdicInfinityCompatibility.powerMap (minus (base p)) = _
  rw [minus_base, beta_eq_coe]
  ext i
  simp [N13TwoAdicInfinityCompatibility.powerMap]

theorem generic_plus_v :
    N13InfinityChartMarking.positiveExpansion N13IntegralInfinityChart.vClass = r₀q := by
  change N13TwoAdicInfinityCompatibility.powerMap (plus N13IntegralInfinityChart.vClass) = _
  rw [plus_v]

theorem generic_minus_v :
    N13InfinityChartMarking.negativeExpansion N13IntegralInfinityChart.vClass = r₁q := by
  change N13TwoAdicInfinityCompatibility.powerMap (minus N13IntegralInfinityChart.vClass) = _
  rw [minus_v]

theorem trunc_error_dvd (f : QP) (n : ℕ) :
    (PowerSeries.X : QP) ^ n ∣ ((PowerSeries.trunc n f : Q₂[X]) : QP) - f := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro i hi
  simp [PowerSeries.coeff_trunc, hi]

/-- Concrete simultaneous finite-jet lifting for the actual generic branch
maps. The one scalar c clears the two truncated interpolation polynomials. -/
theorem exists_scaled_branch_jet_lift (n : ℕ) (r s : QP) :
    ∃ c : R₂, c ≠ 0 ∧ ∃ z : B,
      (PowerSeries.X : QP) ^ n ∣
        N13InfinityChartMarking.positiveExpansion z - PowerSeries.C (cMap c) * r ∧
      (PowerSeries.X : QP) ^ n ∣
        N13InfinityChartMarking.negativeExpansion z - PowerSeries.C (cMap c) * s := by
  let u := interpolationU r s
  let v := interpolationV r s
  obtain ⟨c, hc, p, q, hp, hq⟩ :=
    clear_two_polynomials (PowerSeries.trunc n u) (PowerSeries.trunc n v)
  let z : B := base p + base q * N13IntegralInfinityChart.vClass
  have hp' : (p.map cMap : QP) =
      (PowerSeries.trunc n u : QP) * PowerSeries.C (cMap c) := by
    rw [← hp]
    simp
  have hq' : (q.map cMap : QP) =
      (PowerSeries.trunc n v : QP) * PowerSeries.C (cMap c) := by
    rw [← hq]
    simp
  have hpz : N13InfinityChartMarking.positiveExpansion z =
      ((PowerSeries.trunc n u : QP) + (PowerSeries.trunc n v : QP) * r₀q) *
        PowerSeries.C (cMap c) := by
    dsimp only [z]
    rw [map_add, map_mul, generic_plus_base, generic_plus_base, generic_plus_v, hp', hq']
    ring
  have hmz : N13InfinityChartMarking.negativeExpansion z =
      ((PowerSeries.trunc n u : QP) + (PowerSeries.trunc n v : QP) * r₁q) *
        PowerSeries.C (cMap c) := by
    dsimp only [z]
    rw [map_add, map_mul, generic_minus_base, generic_minus_base, generic_minus_v, hp', hq']
    ring
  have hu := trunc_error_dvd u n
  have hv := trunc_error_dvd v n
  have hplus : u + v * r₀q = r := interpolation_plus r s
  have hminus : u + v * r₁q = s := interpolation_minus r s
  refine ⟨c, hc, z, ?_, ?_⟩
  · have h := (dvd_add hu (hv.trans (dvd_mul_right _ r₀q))).trans
      (dvd_mul_right _ (PowerSeries.C (cMap c)))
    convert h using 1
    rw [hpz, ← hplus]
    ring
  · have h := (dvd_add hu (hv.trans (dvd_mul_right _ r₁q))).trans
      (dvd_mul_right _ (PowerSeries.C (cMap c)))
    convert h using 1
    rw [hmz, ← hminus]
    ring

end
end MazurProof.N13InfinityBranchJetLift


