-- Prove2me | Definitions.Def_CK_GeneralCK_FCRayMain
-- name    : CK_GeneralCK_FCRayMain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:59:13.340978+00:00
-- url     : https://prove2.me/theorems/e006a1ce-8cab-4e0d-b53a-8beda8ff4a82
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCRayMain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCRayMain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCRayMain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCRayMain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCRayMain.lean)

import Definitions.Def_CK_GeneralCK_FCRay
import Definitions.Def_CK_GeneralCK_FCPilotFace

-- ===== source module GeneralCK.FCRayMain =====
section

/-!
# Lane F-C: the ray construction on the strict interior

With `zm = 1 - a - b > 0`, `r = b - a`, `za = 1 - 2a = r + zm`, `zb = 2b - 1 = r - zm`,
take the two phi-tangents at the RAY points `e0 = E·za/r`, `f0 = E·zb/r`.  Then
`e0 + f0 = 2E`; `(F za e0 + F zb f0)/2 = F r E` exactly by 1-homogeneity; the two
tangents share their `F`-slope because `za/e0 = zb/f0 = r/E`; convexity of `eta`
kills the parent term.  What is left is
`(eta' e0 - eta' f0)·(e0 - allocationLower)/2 ≤ F zm E`, and
`FCActive.active_forces_F_lower` pays for it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCRayMain

open GeneralCK
open GeneralCK.PsiAffineChildCertificate

theorem ray_certificate {a b E : ℝ}
    (ha : 0 < a) (hab : a < b) (hsum : a + b < 1) (hb : 1 / 2 < b)
    (hcut : a + (1 - b) < 1 / 10000)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hactive : psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E)
    (hray : E * (1 - 2 * a) / (b - a) < H a) :
    ∃ (L : EntropySupport a) (R : EntropySupport b),
      OppositeCornerPhiAffineCertificate.certificateInequality L R E := by
  -- geometry
  have hbb : b < 1 := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have ha1 : a < 1 := by linarith
  have ha2 : a < 1 / 2 := by linarith
  have hzm : (0 : ℝ) < 1 - a - b := by linarith
  have hr : (0 : ℝ) < b - a := by linarith
  have hza : (0 : ℝ) < 1 - 2 * a := by linarith
  have hzbpos : (0 : ℝ) < 2 * b - 1 := by linarith
  have hzble : (4999 : ℝ) / 5000 ≤ 2 * b - 1 := by linarith
  have hzale : 1 - 2 * a ≤ (1 : ℝ) := by linarith
  -- entropy caps
  have hHa : H a ≤ 1 / 500 := FCRay.H_small_upper ha.le (by linarith)
  have hHbc : H b = H (1 - b) := (H_complement b).symm
  have hHb : H b ≤ 1 / 500 := by
    rw [hHbc]; exact FCRay.H_small_upper (by linarith) (by linarith)
  have hHale : H a ≤ H b := by
    rw [hHbc]
    exact H_strictMonoOn.monotoneOn
      (show a ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨ha.le, by linarith⟩)
      (show (1 - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
      (by linarith)
  have hEsmall : E ≤ 1 / 500 := by linarith
  have hHann : 0 ≤ H a := H_nonneg ha.le (by linarith)
  have hHbnn : 0 ≤ H b := H_nonneg hb0.le hbb.le
  -- the ray reference entropies
  have he0pos : 0 < E * (1 - 2 * a) / (b - a) := by positivity
  have hf0pos : 0 < E * (2 * b - 1) / (b - a) := by positivity
  have hsum0 : E * (1 - 2 * a) / (b - a) + E * (2 * b - 1) / (b - a) = 2 * E := by
    field_simp; ring
  have hf0lt : E * (2 * b - 1) / (b - a) < E * (1 - 2 * a) / (b - a) := by
    have hnum : 0 < (E * (1 - 2 * a) - E * (2 * b - 1)) / (b - a) := by
      apply div_pos _ hr; nlinarith only [hE, hsum]
    rw [sub_div] at hnum; linarith
  have hf0ltE : E * (2 * b - 1) / (b - a) < E := by
    have hnum : 0 < (E * (b - a) - E * (2 * b - 1)) / (b - a) := by
      apply div_pos _ hr; nlinarith only [hE, hsum]
    rw [sub_div, mul_div_assoc, div_self hr.ne', mul_one] at hnum
    linarith
  have hf0cap : E * (2 * b - 1) / (b - a) < H b := by linarith
  have he0cap : E * (1 - 2 * a) / (b - a) < H a := hray
  have he0le : E * (1 - 2 * a) / (b - a) ≤ 1 / 500 := by linarith
  have he0lt1 : E * (1 - 2 * a) / (b - a) < 1 := by linarith
  have hf0lt1 : E * (2 * b - 1) / (b - a) < 1 := by linarith
  refine ⟨phiSupport a (E * (1 - 2 * a) / (b - a)) ha ha1 he0pos he0cap,
    phiSupport b (E * (2 * b - 1) / (b - a)) hb0 hbb hf0pos hf0cap, ?_⟩
  set e0 := E * (1 - 2 * a) / (b - a) with he0def
  set f0 := E * (2 * b - 1) / (b - a) with hf0def
  -- profile values
  have hphia : phi a e0 = eta e0 - F (1 - 2 * a) e0 := by
    unfold phi; rw [abs_of_pos hza]
  have hphib : phi b f0 = eta f0 - F (2 * b - 1) f0 := by
    unfold phi
    rw [show |1 - 2 * b| = 2 * b - 1 by
      rw [abs_of_neg (by linarith : (1 : ℝ) - 2 * b < 0)]; ring]
  have hphiM : phi ((a + b) / 2) E = eta E - F (1 - a - b) E := by
    unfold phi
    rw [show |1 - 2 * ((a + b) / 2)| = 1 - a - b by
      rw [show (1 : ℝ) - 2 * ((a + b) / 2) = 1 - a - b by ring, abs_of_pos hzm]]
  -- exact homogeneity on the rays
  have hFa : F (1 - 2 * a) e0 = ((1 - 2 * a) / (b - a)) * F (b - a) E := by
    have h := F_scale (b - a) E ((1 - 2 * a) / (b - a))
    rw [show ((1 - 2 * a) / (b - a)) * (b - a) = 1 - 2 * a by field_simp] at h
    rw [show ((1 - 2 * a) / (b - a)) * E = e0 by rw [he0def]; ring] at h
    exact h
  have hFb : F (2 * b - 1) f0 = ((2 * b - 1) / (b - a)) * F (b - a) E := by
    have h := F_scale (b - a) E ((2 * b - 1) / (b - a))
    rw [show ((2 * b - 1) / (b - a)) * (b - a) = 2 * b - 1 by field_simp] at h
    rw [show ((2 * b - 1) / (b - a)) * E = f0 by rw [hf0def]; ring] at h
    exact h
  have hFsum : (F (1 - 2 * a) e0 + F (2 * b - 1) f0) / 2 = F (b - a) E := by
    rw [hFa, hFb]; field_simp; ring
  -- convexity of eta at the midpoint
  have hcvx : eta E ≤ (eta e0 + eta f0) / 2 := by
    have h := Scalar.eta_convexOn_Ioc.2
      (show e0 ∈ Set.Ioc (0 : ℝ) 1 from ⟨he0pos, he0lt1.le⟩)
      (show f0 ∈ Set.Ioc (0 : ℝ) 1 from ⟨hf0pos, hf0lt1.le⟩)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
    simp only [smul_eq_mul] at h
    rw [show (1 : ℝ) / 2 * e0 + 1 / 2 * f0 = E by linarith [hsum0]] at h
    linarith
  -- coinciding F-slopes
  have hratio : (1 - 2 * a) / e0 = (2 * b - 1) / f0 := by
    rw [he0def, hf0def]
    field_simp
  have hFeq : deriv (F (1 - 2 * a)) e0 = deriv (F (2 * b - 1)) f0 :=
    FCRay.deriv_F_entropy_ray hza he0pos hzbpos hf0pos hratio
  have hda : deriv (phi a) e0 = deriv eta e0 - deriv (F (1 - 2 * a)) e0 :=
    FCRay.deriv_phi_sub ha ha2 he0pos he0lt1
  have hdb : deriv (phi b) f0 = deriv eta f0 - deriv (F (2 * b - 1)) f0 := by
    have hfun : phi b = phi (1 - b) := by funext t; exact (phi_complement b t).symm
    rw [hfun, FCRay.deriv_phi_sub (by linarith : (0 : ℝ) < 1 - b)
      (by linarith : 1 - b < 1 / 2) hf0pos hf0lt1]
    rw [show (1 : ℝ) - 2 * (1 - b) = 2 * b - 1 by ring]
  have hslopediff : deriv (phi a) e0 - deriv (phi b) f0 = deriv eta e0 - deriv eta f0 := by
    rw [hda, hdb, hFeq]; ring
  have hDnn : 0 ≤ deriv eta e0 - deriv eta f0 := by
    have h := FCRay.deriv_eta_mono hf0pos hf0lt.le he0lt1
    linarith
  have hDub : deriv eta e0 - deriv eta f0 ≤ (2 / f0 ^ 2) * (e0 - f0) :=
    FCRay.deriv_eta_increment hf0pos hf0lt.le he0le
  -- allocation interval
  have hlo_le_up : allocationLower a b E ≤ allocationUpper a b E := by
    unfold allocationLower allocationUpper
    refine max_le (le_min hHann (by linarith)) (le_min (by linarith) (by linarith))
  have hloe0 : allocationLower a b E ≤ e0 := by
    unfold allocationLower
    exact max_le he0pos.le (by linarith [hsum0, hf0cap])
  have hlonn : (0 : ℝ) ≤ allocationLower a b E := le_max_left _ _
  -- childFloor in closed form
  have hcf : childFloor (phiSupport a e0 ha ha1 he0pos he0cap)
      (phiSupport b f0 hb0 hbb hf0pos hf0cap) E
      = (phi a e0 + phi b f0) / 2
        - (deriv eta e0 - deriv eta f0) * (e0 - allocationLower a b E) / 2 := by
    unfold childFloor
    rw [FCPilot.phiSupport_intercept, FCPilot.phiSupport_intercept,
      FCPilot.phiSupport_slope, FCPilot.phiSupport_slope]
    rw [hslopediff]
    rw [min_eq_left (mul_le_mul_of_nonneg_left hlo_le_up hDnn)]
    rw [hda, hdb, hFeq]
    linear_combination ((deriv (F (2 * b - 1)) f0 - deriv eta f0) / 2) * hsum0
  -- the residue
  have hFlow : (16 / 5 : ℝ) * (1 - a - b) ≤ F (1 - a - b) E :=
    FCActive.active_forces_F_lower ha hb hsum hcut hE hEsmall hactive
  have hpen : (deriv eta e0 - deriv eta f0) * (e0 - allocationLower a b E) / 2
      ≤ F (1 - a - b) E := by
    have hstep1 : (deriv eta e0 - deriv eta f0) * (e0 - allocationLower a b E) / 2
        ≤ ((2 / f0 ^ 2) * (e0 - f0)) * e0 / 2 := by
      have hnn : (0 : ℝ) ≤ e0 - allocationLower a b E := by linarith
      have hc1 : (deriv eta e0 - deriv eta f0) * (e0 - allocationLower a b E)
          ≤ ((2 / f0 ^ 2) * (e0 - f0)) * (e0 - allocationLower a b E) :=
        mul_le_mul_of_nonneg_right hDub hnn
      have hc2 : ((2 / f0 ^ 2) * (e0 - f0)) * (e0 - allocationLower a b E)
          ≤ ((2 / f0 ^ 2) * (e0 - f0)) * e0 := by
        have hf : (0 : ℝ) ≤ (2 / f0 ^ 2) * (e0 - f0) := by
          have : (0 : ℝ) ≤ e0 - f0 := by linarith
          positivity
        nlinarith only [hf, hlonn]
      linarith
    have hval : ((2 / f0 ^ 2) * (e0 - f0)) * e0 / 2
        = 2 * (1 - a - b) * (1 - 2 * a) / (2 * b - 1) ^ 2 := by
      rw [he0def, hf0def]
      field_simp
      ring
    have hcmp : 2 * (1 - a - b) * (1 - 2 * a) / (2 * b - 1) ^ 2
        ≤ (16 / 5 : ℝ) * (1 - a - b) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * b - 1) ^ 2)]
      have hzb2 : (4999 / 5000 : ℝ) ^ 2 ≤ (2 * b - 1) ^ 2 := by
        nlinarith only [hzble, hzbpos]
      have hcore : 2 * (1 - 2 * a) ≤ (16 / 5 : ℝ) * (2 * b - 1) ^ 2 := by
        nlinarith only [hzale, hzb2]
      nlinarith only [hcore, hzm]
    linarith [hstep1, hval ▸ hstep1, hcmp, hFlow]
  -- assemble
  have hscf : F (b - a) E ≤ scalarCostFloor a b E := by
    unfold scalarCostFloor; exact le_max_left _ _
  show phi ((a + b) / 2) E
    - childFloor (phiSupport a e0 ha ha1 he0pos he0cap)
        (phiSupport b f0 hb0 hbb hf0pos hf0cap) E ≤ scalarCostFloor a b E
  rw [hcf, hphiM, hphia, hphib]
  have hkey : eta E - F (1 - a - b) E
      - ((eta e0 - F (1 - 2 * a) e0 + (eta f0 - F (2 * b - 1) f0)) / 2
        - (deriv eta e0 - deriv eta f0) * (e0 - allocationLower a b E) / 2)
      ≤ F (b - a) E := by
    have hF : (F (1 - 2 * a) e0 + F (2 * b - 1) f0) / 2 = F (b - a) E := hFsum
    linarith [hcvx, hpen, hF]
  linarith [hkey, hscf]

#check @ray_certificate
#print axioms ray_certificate

end GeneralCK.FCRayMain

end


