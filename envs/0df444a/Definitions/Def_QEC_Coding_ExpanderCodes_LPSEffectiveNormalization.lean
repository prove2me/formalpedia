-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
-- name    : QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:50:19.296205+00:00
-- url     : https://prove2.me/theorems/7613600c-955b-49b5-b7e9-40314297cd09
-- title:
--   LPSEffective Normalization
-- statement:
--   Definitions and structural lemmas for LPSEffective Normalization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_degree_nonzero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
def lpsDegreeRootCandidate (a : LPSResiduePrime p) (n : ℕ) : Prop :=
  n < a.q ∧ ((n : ℕ) : ZMod a.q) ^ 2 = (p : ZMod a.q)
instance (a : LPSResiduePrime p) : DecidablePred (lpsDegreeRootCandidate a) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))
theorem exists_lpsDegreeRootCandidate (a : LPSResiduePrime p) :
    ∃ n, lpsDegreeRootCandidate a n := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff' a.q a.degree_nonzero).mp a.residue
  refine ⟨r.val, ZMod.val_lt r, ?_⟩
  rw [ZMod.natCast_zmod_val]
  simpa [pow_two] using hr.symm
def lpsEffectiveDegreeRootIndex (a : LPSResiduePrime p) : ℕ :=
  Nat.find (exists_lpsDegreeRootCandidate a)
def lpsEffectiveDegreeRoot (a : LPSResiduePrime p) : ZMod a.q :=
  (lpsEffectiveDegreeRootIndex a : ℕ)
theorem lpsEffectiveDegreeRoot_sq (a : LPSResiduePrime p) :
    lpsEffectiveDegreeRoot a ^ 2 = (p : ZMod a.q) :=
  (Nat.find_spec (exists_lpsDegreeRootCandidate a)).2
theorem lpsEffectiveDegreeRoot_ne_zero (a : LPSResiduePrime p) :
    lpsEffectiveDegreeRoot a ≠ 0 := by
  intro h
  have hs := lpsEffectiveDegreeRoot_sq a
  rw [h, zero_pow (by decide)] at hs
  exact a.degree_nonzero hs.symm
def lpsEffectiveQuaternionSL (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : SL(2, ZMod a.q) :=
  ⟨(lpsEffectiveDegreeRoot a)⁻¹ • lpsQuaternionMatrix a.q t, by
    have hdet : (lpsQuaternionMatrix a.q t).det = (p : ZMod a.q) := by
      rw [det_lpsQuaternionMatrix, ht]
      norm_cast
    rw [Matrix.det_smul, hdet]
    simp only [Fintype.card_fin]
    rw [← lpsEffectiveDegreeRoot_sq a]
    simp [lpsEffectiveDegreeRoot_ne_zero a]⟩
def lpsEffectiveQuaternionPSL (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) : PSL(2, ZMod a.q) :=
  QuotientGroup.mk (lpsEffectiveQuaternionSL a t ht)
end QEC.Coding.TannerLiftedProduct


