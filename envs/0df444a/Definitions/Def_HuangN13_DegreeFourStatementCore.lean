-- Prove2me | Definitions.Def_HuangN13_DegreeFourStatementCore
-- name    : HuangN13_DegreeFourStatementCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:50:11.657199+00:00
-- url     : https://prove2.me/theorems/bf5fce00-b093-4f78-9fc5-f19de1f2bd10
-- title:
--   Exact original statement data for comparison_infinity_order_balance, infinity_cleared_order_balance, infinity_sheet_difference…
-- statement:
--   Exactly the original definitions (and the lemmas their bodies need) that the statements of the listed N13 nodes refer to; no new mathematics.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Theorems.Thm_MazurProof_N13SpecialInfinityBranchJets_root_eval
import Theorems.Thm_MazurProof_N13SpecialLaurentBranches_root_relation

set_option autoImplicit false

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def r₀ : P := powerReduce N13FormalInfinityBranches.branchZero
end
end MazurProof.N13SpecialInfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def r₁ : P := powerReduce N13FormalInfinityBranches.branchOne
end
end MazurProof.N13SpecialInfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₀_relation : r₀ ^ 2 + h * r₀ - rhs = 0 := by
  have he := congrArg powerReduce N13FormalInfinityBranches.branchZero_relation
  simp only [map_sub, map_add, map_pow, map_mul, map_zero, reduce_h, reduce_rhs] at he
  exact he
end
end MazurProof.N13SpecialInfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₁_eq : r₁ = -h - r₀ := by
  simp [r₁, N13FormalInfinityBranches.branchOne, reduce_h, r₀]
end
end MazurProof.N13SpecialInfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem r₁_relation : r₁ ^ 2 + h * r₁ - rhs = 0 := by
  rw [r₁_eq]
  linear_combination r₀_relation
end
end MazurProof.N13SpecialInfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def plus : B →+* P := AdjoinRoot.lift beta r₀ (MazurProof.N13SpecialInfinityBranchJets.root_eval r₀ r₀_relation)
end
end MazurProof.N13SpecialInfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def minus : B →+* P := AdjoinRoot.lift beta r₁ (MazurProof.N13SpecialInfinityBranchJets.root_eval r₁ r₁_relation)
end
end MazurProof.N13SpecialInfinityBranchJets
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
def plus : R →+* L := AdjoinRoot.lift base
  (t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₀)
  (MazurProof.N13SpecialLaurentBranches.root_relation _ N13SpecialInfinityBranchJets.r₀_relation)
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
def minus : R →+* L := AdjoinRoot.lift base
  (t⁻¹ ^ 3 * includeSeries N13SpecialInfinityBranchJets.r₁)
  (MazurProof.N13SpecialLaurentBranches.root_relation _ N13SpecialInfinityBranchJets.r₁_relation)
end
end MazurProof.N13SpecialLaurentBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
def infinityBranch (negative : Bool) : B →+* P :=
  if negative then N13SpecialInfinityBranchJets.minus else N13SpecialInfinityBranchJets.plus
end
end MazurProof.N13SpecialOverlapBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialOverlapBranches
noncomputable section
open Polynomial N13SpecialLaurentBranches
open scoped nonZeroDivisors LaurentSeries
def affineBranch (negative : Bool) : R →+* L := if negative then minus else plus
end
end MazurProof.N13SpecialOverlapBranches
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
section
set_option autoImplicit false
namespace MazurProof.N13SpecialDivisorBranchOrders
noncomputable section
open Polynomial N13SpecialDivisorCharts
open N13SpecialLaurentBranches hiding K
open N13SpecialOverlapBranches N13SpecialComparisonFactorPair
open scoped Sym2
def tensorOrder (negative : Bool) (D E : EffectiveDivisorTwo) : ℕ :=
  divisorOrder negative D + divisorOrder negative E
end
end MazurProof.N13SpecialDivisorBranchOrders
end
end
end
end
end
end
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
def hAt (a : K) : K[X] := N13GoodCoordinateRingTwo.hPoly.comp (X + _root_.Polynomial.C a)
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
def rhsAt (a : K) : K[X] := N13GoodCoordinateRingTwo.rhsPoly.comp (X + _root_.Polynomial.C a)
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
theorem hAt_constant (a : K) : (hAt a).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, hAt, Polynomial.eval_comp]
  rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one a (ZMod.pow_card a) with ha | ha
  · subst a; simp [N13GoodCoordinateRingTwo.hPoly]
  · subst a; simp [N13GoodCoordinateRingTwo.hPoly]; decide
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
theorem rhsAt_constant (a : K) : (rhsAt a).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, rhsAt, Polynomial.eval_comp]
  rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one a (ZMod.pow_card a) with ha | ha
  · subst a; simp [N13GoodCoordinateRingTwo.rhsPoly]
  · subst a; simp [N13GoodCoordinateRingTwo.rhsPoly]; decide
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem beta_constant (p : K[X]) : PowerSeries.constantCoeff (beta p) = p.coeff 0 := by
  rw [beta_eq_coe, ← PowerSeries.coeff_zero_eq_constantCoeff]
  exact Polynomial.coeff_coe p 0
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def curvePoly (a : K) : P[X] := X ^ 2 + _root_.Polynomial.C (beta (hAt a)) * X - _root_.Polynomial.C (beta (rhsAt a))
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem curvePoly_monic (a : K) : (curvePoly a).Monic := by unfold curvePoly; monicity!
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem exists_root_zero (a : K) :
    ∃ r : P, (curvePoly a).IsRoot r ∧ r ∈ xIdeal := by
  have hrhs : beta (rhsAt a) ∈ xIdeal := by
    apply Ideal.mem_span_singleton.mpr
    apply PowerSeries.X_dvd_iff.mpr
    rw [beta_constant, rhsAt_constant]
  have hzero : (curvePoly a).eval 0 ∈ xIdeal := by
    simpa [curvePoly] using (xIdeal.neg_mem hrhs)
  have hder : (curvePoly a).derivative.eval 0 = beta (hAt a) := by simp [curvePoly]
  have hunit : IsUnit (Ideal.Quotient.mk xIdeal ((curvePoly a).derivative.eval 0)) := by
    rw [hder]
    have hu : IsUnit (beta (hAt a)) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, beta_constant, hAt_constant]
      exact isUnit_one
    exact hu.map (Ideal.Quotient.mk xIdeal)
  obtain ⟨r, hr, hr0⟩ := HenselianRing.is_henselian (curvePoly a) (curvePoly_monic a) 0 hzero hunit
  exact ⟨r, hr, by simpa using hr0⟩
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
def rootZero (a : K) : P := Classical.choose (exists_root_zero a)
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
def rootOne (a : K) : P := -beta (hAt a) - rootZero a
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem rootZero_relation (a : K) :
    rootZero a ^ 2 + beta (hAt a) * rootZero a - beta (rhsAt a) = 0 := by
  have h := (Classical.choose_spec (exists_root_zero a)).1
  rw [Polynomial.IsRoot.def] at h
  simp only [curvePoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at h
  exact h
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem rootOne_relation (a : K) :
    rootOne a ^ 2 + beta (hAt a) * rootOne a - beta (rhsAt a) = 0 := by
  unfold rootOne
  linear_combination rootZero_relation a
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem beta_comp (a : K) (p : K[X]) : beta (p.comp (X + _root_.Polynomial.C a)) = evalBase a p := by
  simp [beta, evalBase, Polynomial.eval₂_comp]
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
private theorem affine_root (a : K) (r : P)
    (hr : r ^ 2 + beta (hAt a) * r - beta (rhsAt a) = 0) :
    N13GoodCoordinateRingTwo.curvePoly.eval₂ (evalBase a) r = 0 := by
  simp only [N13GoodCoordinateRingTwo.curvePoly, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  simpa only [hAt, rhsAt, beta_comp] using hr
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
def branchZero (a : K) : N13GoodCoordinateRingTwo.CoordinateRing →+* P :=
  AdjoinRoot.lift (evalBase a) (rootZero a) (affine_root a _ (rootZero_relation a))
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
def branchOne (a : K) : N13GoodCoordinateRingTwo.CoordinateRing →+* P :=
  AdjoinRoot.lift (evalBase a) (rootOne a) (affine_root a _ (rootOne_relation a))
end
end MazurProof.N13SpecialFiniteBranchJets
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K plus minus
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
def sixOrders (z : R) : Fin 6 → ℤ := ![
  (includeSeries (branchZero 0 z)).order, (includeSeries (branchOne 0 z)).order,
  (includeSeries (branchZero 1 z)).order, (includeSeries (branchOne 1 z)).order,
  (plus z).order, (minus z).order]
end
end MazurProof.N13SpecialSixJetOrders
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialSixJetOrders
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K plus minus
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
def weightedLocalCode (z : R) : ZMod 19 :=
  (sixOrders z 0 : ZMod 19) - sixOrders z 1 +
    7 * (sixOrders z 2 : ZMod 19) - 7 * sixOrders z 3 +
    8 * (sixOrders z 4 : ZMod 19) - 8 * sixOrders z 5
end
end MazurProof.N13SpecialSixJetOrders
end
end


