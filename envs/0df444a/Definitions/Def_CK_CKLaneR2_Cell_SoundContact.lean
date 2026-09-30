-- Prove2me | Definitions.Def_CK_CKLaneR2_Cell_SoundContact
-- name    : CK_CKLaneR2_Cell_SoundContact
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:48:19.006292+00:00
-- url     : https://prove2.me/theorems/90f17eea-795c-46f0-a65f-76bdb83b790d
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Cell.SoundContact` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Cell.SoundContact` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Cell.SoundContact` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Cell.SoundContact (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Cell/SoundContact.lean)

import Definitions.Def_CK_CKLaneR2_Cell_SoundImplicit
import Definitions.Def_CK_CKLaneN23_RSDefs

-- ===== source module CKLaneR2.Cell.SoundContact =====
section

/-!
# Lane C, RA-stat interior: soundness of the cell checker, part 3 (contact blocks and the eta block)

**Contact blocks.** The contact block `raysec Z iE ds de dde (contactFuncs Z (checkImplicit true Z V ρ))`
contains N23's `raySec s ds e de dde`. This requires:
* `Z` contains `s/e` and `iE` contains `1/e`;
* `Z ≥ 0`;
* `Z = 0 ⇒ ds = 0`.

**The eta block.** It contains `-(etaCurvature E · de² + etaSlope E · dde)`.
-/

namespace CKLaneR2.Cell

open CKLaneR2.TM3 GeneralCK GeneralCK.Certificates.Mixed

/-! ## Raw δ-functions of the contact block -/

noncomputable def cJ (δ : ℝ) : ℝ := (Real.log (δ + 1) - Real.log (1 - δ)) * (1 / Real.log 2)
noncomputable def cHn (δ : ℝ) : ℝ :=
  Real.log 2 - ((δ + 1) * Real.log (δ + 1) + (1 - δ) * Real.log (1 - δ)) / 2
noncomputable def cKap (δ : ℝ) : ℝ := Real.log 2 - (Real.log (δ + 1) + Real.log (1 - δ)) / 2
noncomputable def cOm (δ : ℝ) : ℝ := 1 - δ * δ
noncomputable def cF1 (δ : ℝ) : ℝ := cJ δ + 2 * (δ * cHn δ * ((cOm δ)⁻¹ * (cKap δ)⁻¹) * (1 / Real.log 2))
noncomputable def cF2 (z δ : ℝ) : ℝ :=
  4 * (cHn δ * cHn δ * (2 * cKap δ - δ * δ) *
    ((cOm δ)⁻¹ * (cOm δ)⁻¹ * ((cKap δ)⁻¹ * (cKap δ)⁻¹) * (z * cJ δ + 2)⁻¹) *
    (1 / Real.log 2 * (1 / Real.log 2)))

theorem C_jOfLogs {lp lm : TM} {df : ℝ → ℝ → ℝ → ℝ}
    (hlp : Contains one lp (fun x y z => Real.log (df x y z + 1)))
    (hlm : Contains one lm (fun x y z => Real.log (1 - df x y z))) :
    Contains one (jOfLogs lp lm) (fun x y z => cJ (df x y z)) :=
  C_mul (Contains.sub hlp hlm) invLc_contains

theorem C_contactFuncs {Z : TM} {zf : ℝ → ℝ → ℝ → ℝ} {I : Impl} {df : ℝ → ℝ → ℝ → ℝ}
    (hZ : Contains one Z zf) (hD : Contains one I.D df)
    (hlp : Contains one I.lp (fun x y z => Real.log (df x y z + 1)))
    (hlm : Contains one I.lm (fun x y z => Real.log (1 - df x y z))) :
    Contains one (contactFuncs Z I).F0 (fun x y z => zf x y z * cJ (df x y z)) ∧
    Contains one (contactFuncs Z I).F1 (fun x y z => cF1 (df x y z)) ∧
    Contains one (contactFuncs Z I).F2 (fun x y z => cF2 (zf x y z) (df x y z)) := by
  have hJ := C_jOfLogs hlp hlm
  have hhn : Contains one (TM.add Lc (TM.neg (mulc (TM.add (mul (TM.addc I.D ONEi) I.lp)
      (mul (TM.addc (TM.neg I.D) ONEi) I.lm)) half))) (fun x y z => cHn (df x y z)) := by
    have := Contains.add Lc_contains (Contains.neg (C_half (Contains.add (C_mul (C_addOne hD) hlp)
      (C_mul (C_oneSub hD) hlm))))
    refine Contains.congr this (fun x y z _ _ _ => ?_)
    unfold cHn; ring
  have hkap : Contains one (TM.add Lc (TM.neg (mulc (TM.add I.lp I.lm) half))) (fun x y z => cKap (df x y z)) := by
    have := Contains.add Lc_contains (Contains.neg (C_half (Contains.add hlp hlm)))
    refine Contains.congr this (fun x y z _ _ _ => ?_)
    unfold cKap; ring
  have hom : Contains one (TM.addc (TM.neg (mul I.D I.D)) ONEi) (fun x y z => cOm (df x y z)) := by
    have := C_oneSub (C_mul hD hD)
    refine Contains.congr this (fun x y z _ _ _ => ?_)
    unfold cOm; ring
  have hik := C_recip hkap
  have hiom := C_recip hom
  refine ⟨C_mul hZ hJ, ?_, ?_⟩
  · have := Contains.add hJ (Contains.scaleInt (C_mul (C_mul (C_mul hD hhn) (C_mul hiom hik)) invLc_contains) 2)
    refine Contains.congr this (fun x y z _ _ _ => ?_)
    unfold cF1; push_cast; ring
  · have hizj : Contains one (recip (TM.addc (mul Z (jOfLogs I.lp I.lm)) (2 * ONEi)))
        (fun x y z => (zf x y z * cJ (df x y z) + 2)⁻¹) := by
      have := C_recip (Contains.addc (C_mul hZ hJ) (2 * ONEi))
      refine Contains.congr this (fun x y z _ _ _ => ?_)
      have h2 : (((2 * ONEi : ℤ)) : ℝ) / (one : ℝ) = 2 := by
        rw [Int.cast_mul, mul_div_assoc, ONEi_div]; norm_num
      rw [h2]
    have hnum := C_mul (C_mul hhn hhn) (Contains.sub (Contains.scaleInt hkap 2) (C_mul hD hD))
    have hden := C_mul (C_mul (C_mul hiom hiom) (C_mul hik hik)) hizj
    have := Contains.scaleInt (C_mul (C_mul hnum hden) (C_mul invLc_contains invLc_contains)) 4
    refine Contains.congr this (fun x y z _ _ _ => ?_)
    unfold cF2; push_cast; ring

/-! ## Pointwise values for a positive contact -/

theorem log_two_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'

theorem contact_values {z : ℝ} (hz : 0 < z) :
    z * cJ (dC z) = F z 1 ∧ cF1 (dC z) = deriv (fun r => F r 1) z ∧
      cF2 z (dC z) = deriv (deriv (fun r => F r 1)) z := by
  have h1 : (0 : ℝ) < 1 := one_pos
  set v := radialContact z 1 with hv
  have hv0 : 0 < v := radialContact_pos hz h1
  have hv1 : v < 1 / 2 := radialContact_lt_half hz h1
  have hvc : 0 < 1 - v := by linarith
  have hδ : dC z = 1 - 2 * v := by unfold dC; rw [if_neg hz.ne']
  have hlp : Real.log (dC z + 1) = Real.log 2 + Real.log (1 - v) := by
    rw [hδ, show 1 - 2 * v + 1 = 2 * (1 - v) by ring, Real.log_mul two_ne_zero hvc.ne']
  have hlm : Real.log (1 - dC z) = Real.log 2 + Real.log v := by
    rw [hδ, show 1 - (1 - 2 * v) = 2 * v by ring, Real.log_mul two_ne_zero hv0.ne']
  have hL := log_two_ne
  have hJv : J v = (Real.log (1 - v) - Real.log v) / Real.log 2 := by
    unfold J; rw [Real.log_div hvc.ne' hv0.ne']
  have hcJ : cJ (dC z) = J v := by
    unfold cJ; rw [hlp, hlm, hJv]; ring
  have hcHn : cHn (dC z) = hn v := by
    unfold cHn hn; rw [hlp, hlm, hδ]; ring
  have hcKap : cKap (dC z) = kap v := by
    unfold cKap kap; rw [hlp, hlm, Real.log_mul hv0.ne' hvc.ne']; ring
  have hcOm : cOm (dC z) = 4 * v * (1 - v) := by
    unfold cOm; rw [hδ]; ring
  have hkp : 0 < kap v := kap_pos hv0 hv1
  have hJp : 0 < J v := J_pos hv0 hv1
  have hden : 0 < z * J v + 2 * 1 := by positivity
  have hF : F z 1 = z * J v := by unfold F; rw [if_neg hz.ne']
  refine ⟨?_, ?_, ?_⟩
  · rw [hcJ, hF]
  · rw [deriv_F_radius_slope hz h1, ← hv]
    unfold cF1 radialSlope
    rw [hcJ, hcHn, hcKap, hcOm, hδ]
    have hk0 := hkp.ne'
    have hv0' := hv0.ne'
    have hvc' := hvc.ne'
    field_simp
    ring
  · rw [(hasDerivAt_deriv_F_radius hz h1).deriv, ← hv]
    unfold cF2
    rw [hcJ, hcHn, hcKap, hcOm, hδ]
    have hk0 := hkp.ne'
    have hv0' := hv0.ne'
    have hvc' := hvc.ne'
    have hden' := hden.ne'
    have hH : H v = hn v / Real.log 2 := by
      rw [hn_eq_H_mul_log]; field_simp
    rw [hH]
    field_simp

theorem raySec_eq {s ds e de dde zf ief : ℝ} (he : 0 < e) (hzs : zf = s / e) (hief : ief = 1 / e)
    (hz0 : 0 ≤ zf) (hzds : zf = 0 → ds = 0) :
    (ds - zf * de) * (ds - zf * de) * ief * cF2 zf (dC zf) + -(zf * dde * cF1 (dC zf))
        + dde * (zf * cJ (dC zf))
      = CKLaneN23.RS.raySec s ds e de dde := by
  unfold CKLaneN23.RS.raySec
  rw [← hzs, hief]
  rcases eq_or_lt_of_le hz0 with h0 | hpos
  · have hds := hzds h0.symm
    rw [← h0, hds]
    simp [F]
  · obtain ⟨h1, h2, h3⟩ := contact_values hpos
    rw [h1, h2, h3]
    ring

/-- Raw value of a contact block (equals `raySec` whenever `z > 0` or `ds = 0`, see `raySec_eq`). -/
noncomputable def rawRS (z ie ds de dde : ℝ) : ℝ :=
  (ds - z * de) * (ds - z * de) * ie * cF2 z (dC z) + -(z * dde * cF1 (dC z)) + dde * (z * cJ (dC z))

/-- Soundness of one contact block (raw form). -/
theorem C_raysec_raw {Z iE ds de dde : TM} {zf ief dsf dfn ddfn : ℝ → ℝ → ℝ → ℝ} (V : Poly) (rho : ℕ)
    (hZ : Contains one Z zf) (hiE : Contains one iE ief) (hds : Contains one ds dsf)
    (hde : Contains one de dfn) (hdde : Contains one dde ddfn)
    (hz0 : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ zf x y z) :
    Contains one (raysec Z iE ds de dde (contactFuncs Z (checkImplicit true Z V rho)))
      (fun x y z => rawRS (zf x y z) (ief x y z) (dsf x y z) (dfn x y z) (ddfn x y z)) := by
  obtain ⟨hD, hlp, hlm⟩ := checkImplicit_contact hZ hz0 V rho
  obtain ⟨hF0, hF1, hF2⟩ := C_contactFuncs hZ hD hlp hlm
  have ha := Contains.sub hds (C_mul hZ hde)
  exact Contains.add (Contains.add (C_mul (C_mul (C_mul ha ha) hiE) hF2)
    (Contains.neg (C_mul (C_mul hZ hdde) hF1))) (C_mul hdde hF0)

/-! ## The eta block -/

noncomputable def eSlopeRaw (δ : ℝ) : ℝ :=
  -(4 * (δ * ((cOm δ)⁻¹ * (cJ δ)⁻¹) * (1 / Real.log 2))) + -2

noncomputable def eCurvRaw (δ : ℝ) : ℝ :=
  16 * ((((δ * δ + 1) * (Real.log 2 * cJ δ)) / 2 - δ) *
    ((cOm δ)⁻¹ * (cOm δ)⁻¹ * ((cJ δ)⁻¹ * (cJ δ)⁻¹ * (cJ δ)⁻¹)) * (1 / Real.log 2 * (1 / Real.log 2)))

theorem eta_values {E : ℝ} (h0 : 0 < E) (h1 : E < 1) :
    eSlopeRaw (dE E) = Scalar.etaSlope E ∧ eCurvRaw (dE E) = Scalar.etaCurvature E := by
  set m := entropyInverse E with hm
  have hm0 : 0 < m := entropyInverse_pos h0 h1.le
  have hm1 : m < 1 / 2 := entropyInverse_lt_half h0.le h1
  have hmc : 0 < 1 - m := by linarith
  have hδ : dE E = 1 - 2 * m := rfl
  have hlp : Real.log (dE E + 1) = Real.log 2 + Real.log (1 - m) := by
    rw [hδ, show 1 - 2 * m + 1 = 2 * (1 - m) by ring, Real.log_mul two_ne_zero hmc.ne']
  have hlm : Real.log (1 - dE E) = Real.log 2 + Real.log m := by
    rw [hδ, show 1 - (1 - 2 * m) = 2 * m by ring, Real.log_mul two_ne_zero hm0.ne']
  have hL := log_two_ne
  have hJm : J m = (Real.log (1 - m) - Real.log m) / Real.log 2 := by
    unfold J; rw [Real.log_div hmc.ne' hm0.ne']
  have hcJ : cJ (dE E) = J m := by unfold cJ; rw [hlp, hlm, hJm]; ring
  have hcOm : cOm (dE E) = 4 * m * (1 - m) := by unfold cOm; rw [hδ]; ring
  have hJp : 0 < J m := J_pos hm0 hm1
  have hJ0 := hJp.ne'
  have hm0' := hm0.ne'
  have hmc' := hmc.ne'
  constructor
  · unfold eSlopeRaw Scalar.etaSlope
    rw [← hm, hcJ, hcOm, hδ]
    field_simp
    ring
  · unfold eCurvRaw Scalar.etaCurvature Scalar.curvatureNumerator
    rw [← hm, hcJ, hcOm, hδ]
    field_simp
    ring

/-- Raw value of the eta block (equals the eta term when `E < 1`, see `eta_values`). -/
noncomputable def rawEta (E de dde : ℝ) : ℝ := -(eCurvRaw (dE E) * (de * de) + eSlopeRaw (dE E) * dde)

theorem C_etaBlock_raw {E de dde : TM} {ef dfn ddfn : ℝ → ℝ → ℝ → ℝ} (V : Poly) (rho : ℕ)
    (hE : Contains one E ef) (hde : Contains one de dfn) (hdde : Contains one dde ddfn)
    (he : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 < ef x y z ∧ ef x y z ≤ 1) :
    Contains one (etaBlock E de dde (checkImplicit false E V rho))
      (fun x y z => rawEta (ef x y z) (dfn x y z) (ddfn x y z)) := by
  obtain ⟨hD, hlp, hlm⟩ := checkImplicit_entropy hE he V rho
  have hJ := C_jOfLogs hlp hlm
  have hom : Contains one (TM.addc (TM.neg (mul (checkImplicit false E V rho).D (checkImplicit false E V rho).D)) ONEi)
      (fun x y z => cOm (dE (ef x y z))) := by
    have := C_oneSub (C_mul hD hD)
    refine Contains.congr this (fun x y z _ _ _ => ?_)
    unfold cOm; ring
  have hiom := C_recip hom
  have hiJ := C_recip hJ
  have hslope := Contains.addc (Contains.neg (Contains.scaleInt (C_mul (C_mul hD (C_mul hiom hiJ)) invLc_contains) 4))
      (-2 * ONEi)
  have hcn := Contains.sub (C_half (C_mul (C_addOne (C_mul hD hD)) (C_mul Lc_contains hJ))) hD
  have hcurv := Contains.scaleInt (C_mul (C_mul hcn (C_mul (C_mul hiom hiom) (C_mul (C_mul hiJ hiJ) hiJ)))
    (C_mul invLc_contains invLc_contains)) 16
  have h := Contains.neg (Contains.add (C_mul hcurv (C_mul hde hde)) (C_mul hslope hdde))
  refine Contains.congr h (fun x y z hx hy hz => ?_)
  have h2 : (((-2 * ONEi : ℤ)) : ℝ) / (one : ℝ) = -2 := by
    rw [Int.cast_mul, mul_div_assoc, ONEi_div]; norm_num
  unfold rawEta eCurvRaw eSlopeRaw
  rw [h2]
  push_cast
  ring

end CKLaneR2.Cell

end


