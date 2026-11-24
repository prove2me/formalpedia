-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:08:36.016387+00:00
-- url     : https://prove2.me/theorems/e5ef1e6b-3d7c-427d-8561-9c901496bf54
-- title:
--   Transfer Invariance Congruence
-- statement:
--   Definitions and structural lemmas for Transfer Invariance Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceCongruence.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
lemma hpart1_add (Z W : Mx k r) :
    hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  unfold hpart1
  rw [conjTranspose_add, mul_add, add_mul, ← smul_add]
  congr 1
  abel
lemma hpart2_add (Z W : Mx k r) :
    hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  unfold hpart2
  rw [conjTranspose_add, mul_add, add_mul, ← smul_add]
  congr 1
  abel
lemma hpart1_real (a : ℝ) (Z : Mx k r) :
    hpart1 (Hpk k r) ((a : ℂ) • Z) = (a : ℂ) • hpart1 (Hpk k r) Z := by
  unfold hpart1
  have hst : star (a : ℂ) = a := Complex.conj_ofReal a
  rw [conjTranspose_smul, hst, mul_smul_comm, smul_mul_assoc, ← smul_sub, smul_comm]
lemma hpart2_real (a : ℝ) (Z : Mx k r) :
    hpart2 (Hpk k r) ((a : ℂ) • Z) = (a : ℂ) • hpart2 (Hpk k r) Z := by
  unfold hpart2
  have hst : star (a : ℂ) = a := Complex.conj_ofReal a
  rw [conjTranspose_smul, hst, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_comm]
lemma hpart1_I (Z : Mx k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  unfold hpart1 hpart2
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hc : (1 / (2 * Complex.I) : ℂ) = -((1 / 2 : ℂ) * Complex.I) := by
    rw [one_div, mul_inv, Complex.inv_I]; ring
  rw [conjTranspose_smul, hI, hc]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_smul, smul_add, smul_sub, smul_neg, smul_smul,
    neg_add, neg_neg, sub_neg_eq_add]
lemma hpart2_I (Z : Mx k r) : hpart2 (Hpk k r) (Complex.I • Z) = hpart1 (Hpk k r) Z := by
  unfold hpart1 hpart2
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hc2 : (1 / (2 * Complex.I) : ℂ) * Complex.I = 1 / 2 := by
    rw [one_div, mul_inv, Complex.inv_I]
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  rw [conjTranspose_smul, hI]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, neg_smul, smul_add, smul_sub, smul_neg, smul_smul,
    ← sub_eq_add_neg, hc2]
section abelian₂
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def lam (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) : E :=
  Φ (g * hpart1 (Hpk k r) Z) + Complex.I • Φ (g * hpart2 (Hpk k r) Z)
lemma real_smul_mx (a : ℝ) (N : Mx k r) : (a : ℂ) • N = a • N := by
  ext i j
  simp [Complex.real_smul]
lemma lam_add (Φ : Mx k r →L[ℝ] E) (g Z W : Mx k r) : lam Φ g (Z + W) = lam Φ g Z + lam Φ g W := by
  unfold lam
  rw [hpart1_add, hpart2_add, mul_add, mul_add, map_add, map_add, smul_add]
  abel
lemma lam_real (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) (a : ℝ) :
    lam Φ g ((a : ℂ) • Z) = (a : ℂ) • lam Φ g Z := by
  unfold lam
  rw [hpart1_real, hpart2_real, mul_smul_comm, mul_smul_comm, real_smul_mx, real_smul_mx, map_smul, map_smul,
    ← Complex.coe_smul, ← Complex.coe_smul, smul_add, smul_comm Complex.I]
lemma lam_I (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) :
    lam Φ g (Complex.I • Z) = Complex.I • lam Φ g Z := by
  unfold lam
  rw [hpart1_I, hpart2_I, mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel
lemma lam_smul (Φ : Mx k r →L[ℝ] E) (g Z : Mx k r) (c : ℂ) :
    lam Φ g (c • Z) = c • lam Φ g Z := by
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
  rw [hc, add_smul, lam_add, mul_smul, lam_real, lam_real, lam_I, add_smul, mul_smul]
def lamL (Φ : Mx k r →L[ℝ] E) (g : Mx k r) : Mx k r →ₗ[ℂ] E where
  toFun := lam Φ g
  map_add' := lam_add Φ g
  map_smul' c Z := lam_smul Φ g Z c
end abelian₂
end Formalism.FourierDecayAlt.Q.TInvW


