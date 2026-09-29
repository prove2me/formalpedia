-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_CorrectionIntegerLogTableKernel
-- name    : CK_GeneralCK_Certificates_CorrectionIntegerLogTableKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:27.352522+00:00
-- url     : https://prove2.me/theorems/f1159058-b426-48c7-aa99-a2ee992a8770
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.CorrectionIntegerLogTableKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.CorrectionIntegerLogTableKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.CorrectionIntegerLogTableKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.CorrectionIntegerLogTableKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/CorrectionIntegerLogTableKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicFastLog

-- ===== source module GeneralCK.Certificates.CorrectionIntegerLogTableKernel =====
section

/-!
# Integer data tables for correction logarithm endpoints

The generated certificate stores only signed integer inputs, reduction
exponents, and dyadic output endpoints.  One Boolean computation checks a
whole list.  The soundness theorem reflects that computation into the real
logarithm containment facts consumed by the proved-program kernel.
-/

namespace GeneralCK.Certificates.CorrectionIntegerLogTableKernel

open GeneralCK.Certificates

structure Datum where
  z : ℤ
  exponent : ℕ
  reciprocal : Bool
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

def Datum.output (d : Datum) : DyadicInterval 40 := ⟨d.lo, d.hi⟩

def lift40 (a : DyadicInterval 40) : DyadicInterval 64 :=
  ⟨a.lo * 16777216, a.hi * 16777216⟩

theorem lift40_contains {a : DyadicInterval 40} {x : ℝ} :
    (lift40 a).Contains x ↔ a.Contains x := by
  simp only [DyadicInterval.Contains, lift40, Int.cast_mul, Int.cast_ofNat]
  norm_num [DyadicInterval.scale]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

def Datum.check (d : Datum) : Bool :=
  if d.reciprocal then
    DyadicFastLog.check 1099511627776 d.z d.exponent 16 (lift40 d.output.neg)
  else
    DyadicFastLog.check d.z 1099511627776 d.exponent 16 (lift40 d.output)

def Datum.Sound (d : Datum) : Prop :=
  d.output.Contains (Real.log ((d.z : ℝ) / 1099511627776))

theorem Datum.sound_of_check {d : Datum} (h : d.check = true) : d.Sound := by
  unfold Datum.check at h
  split at h
  · have hc := lift40_contains.mp (DyadicFastLog.check_sound h)
    have hn := DyadicInterval.neg_sound hc
    rw [← Real.log_inv, inv_div] at hn
    simpa only [Datum.Sound, Datum.output, DyadicInterval.neg, neg_neg,
      Int.cast_ofNat] using hn
  · have hc := lift40_contains.mp (DyadicFastLog.check_sound h)
    simpa only [Datum.Sound, Datum.output, Int.cast_ofNat] using hc

def allCheck : List Datum → Bool
  | [] => true
  | d :: rest => d.check && allCheck rest

def AllSound : List Datum → Prop
  | [] => True
  | d :: rest => d.Sound ∧ AllSound rest

theorem allSound_of_allCheck {data : List Datum} (h : allCheck data = true) :
    AllSound data := by
  induction data with
  | nil => trivial
  | cons d rest ih =>
      have parts := Bool.and_eq_true_iff.mp h
      exact ⟨d.sound_of_check parts.1, ih parts.2⟩

#print axioms Datum.sound_of_check
#print axioms allSound_of_allCheck

end GeneralCK.Certificates.CorrectionIntegerLogTableKernel

end


