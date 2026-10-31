-- Prove2me | Definitions.Def_HuangN13_SixLocalOrdersCore
-- name    : HuangN13_SixLocalOrdersCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:07:48.820102+00:00
-- url     : https://prove2.me/theorems/8ad567de-8604-4c9b-8f92-46aee25d1f3e
-- title:
--   Constructed finite branches and the six geometric local orders
-- statement:
--   The original Hensel-constructed finite branches, the small numerator function, its six geometric local orders, and their weighted combination in ZMod19. Supporting lemmas are only the original proofs needed to construct these branch maps.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact original compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13SpecialFiniteBranchJets
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialInfinityBranchJets hiding K
def hAt (a : K) : K[X] := N13GoodCoordinateRingTwo.hPoly.comp (X + C a)
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
def rhsAt (a : K) : K[X] := N13GoodCoordinateRingTwo.rhsPoly.comp (X + C a)
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
def curvePoly (a : K) : P[X] := X ^ 2 + C (beta (hAt a)) * X - C (beta (rhsAt a))
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
theorem beta_comp (a : K) (p : K[X]) : beta (p.comp (X + C a)) = evalBase a p := by
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
open N13SpecialInfinityBranchJets hiding K
open N13SpecialFiniteBranchJets
open N13SpecialLaurentBranches hiding K P
def function (a : Fin 5 → K) (b : Fin 2 → K) : R :=
  N13SpecialAffineNorm.linear (numerator a) (ordinate b)
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
open N13SpecialInfinityBranchJets hiding K
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
open N13SpecialInfinityBranchJets hiding K
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


