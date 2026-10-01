-- Prove2me | Definitions.Def_CK_GeneralCK_FCCapped
-- name    : CK_GeneralCK_FCCapped
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:31:33.887207+00:00
-- url     : https://prove2.me/theorems/576bc5b6-40a9-47bb-adf9-528e5b37c884
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCCapped` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCCapped` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCCapped` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCCapped (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCCapped.lean)

import Definitions.Def_CK_GeneralCK_FCRay
import Definitions.Def_CK_GeneralCK_FCPilotFace

-- ===== source module GeneralCK.FCCapped =====
section

/-!
# Lane F-C: the capped sub-case, structural part

In the capped region `H a ≤ E·(1-2a)/(b-a)` the ray tangent for child `a` runs
past its entropy cap, so the ray construction is unavailable.  The replacement is

  `L = zeroSupport a`   (intercept 0, slope 0)
  `R = psiSupport b (2E)`

which is FEASIBLE because the activity hypothesis forces `2E < zm ≤ H b / 3.999`,
and which gives `childFloor L R E = psi b (2E) / 2` EXACTLY: the allocation lower
endpoint is `0`, the min term selects it, and the tangent value at `2E` is `psi b (2E)`.

`capped_certificate_of_scalar` therefore reduces the capped sub-case to ONE scalar
inequality with no support data in it at all.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCCapped

open GeneralCK
open GeneralCK.PsiAffineChildCertificate

/-- `psi m h ≥ 4·(H m − h)`: the endpoint slope of `eta` at `1`, via `Scalar.P`. -/
theorem psi_ge_four_deficit {m h : ℝ} (hnn : 0 ≤ H m - h) (hlt : H m - h < 1) :
    4 * (H m - h) ≤ psi m h := by
  have hP := Scalar.four_mul_le_P hnn hlt
  have hval : Scalar.P (H m - h) = psi m h := by
    unfold Scalar.P psi
    rw [show (1 : ℝ) - (H m - h) = h + 1 - H m by ring]
  linarith [hP, hval]

/-- `deriv eta` is strictly negative on `(0,1)`. -/
theorem deriv_eta_neg {h : ℝ} (hh : 0 < h) (hh1 : h < 1) : deriv eta h ≤ -2 := by
  rw [deriv_eta hh hh1]
  have hv : 0 < entropyInverse h := entropyInverse_pos hh hh1.le
  have hvhalf : entropyInverse h < 1 / 2 := entropyInverse_lt_half hh.le hh1
  have hJ : 0 < J (entropyInverse h) := J_pos hv hvhalf
  have hden : 0 < Real.log 2 * entropyInverse h * (1 - entropyInverse h) *
      J (entropyInverse h) := by
    have h1 : (0 : ℝ) < 1 - entropyInverse h := by linarith
    have h2 : (0 : ℝ) < Real.log 2 := log_two_pos
    positivity
  have hnum : (0 : ℝ) ≤ 1 - 2 * entropyInverse h := by linarith
  have : (0 : ℝ) ≤ (1 - 2 * entropyInverse h) /
      (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) :=
    div_nonneg hnum hden.le
  change -2 - (1 - 2 * entropyInverse h) /
    (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) ≤ -2
  linarith

theorem deriv_psi_neg {m h : ℝ} (hlo : 0 < h + 1 - H m) (hhi : h + 1 - H m < 1) :
    deriv (psi m) h ≤ -2 := by
  have hshift : HasDerivAt (fun y : ℝ => y + 1 - H m) 1 h :=
    ((hasDerivAt_id h).add_const 1).sub_const (H m)
  have hcomp := (hasDerivAt_eta hlo hhi).comp h hshift
  rw [Function.comp_def, mul_one] at hcomp
  have hfun : psi m = fun x : ℝ => eta (x + 1 - H m) := rfl
  have hval : deriv (psi m) h = deriv eta (h + 1 - H m) := by
    rw [hfun, hcomp.deriv, (hasDerivAt_eta hlo hhi).deriv]
  rw [hval]
  exact deriv_eta_neg hlo hhi

/-- **Structural reduction of the capped sub-case.**  Everything about supports,
allocations and `childFloor` is discharged; one scalar inequality remains. -/
theorem capped_certificate_of_scalar {a b E : ℝ}
    (ha : 0 < a) (hab : a < b) (hsum : a + b < 1) (hb : 1 / 2 < b)
    (hcut : a + (1 - b) < 1 / 10000)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hactive : psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E)
    (hscalar : eta E - F (b - a) E ≤ F (1 - a - b) E + psi b (2 * E) / 2) :
    ∃ (L : EntropySupport a) (R : EntropySupport b),
      OppositeCornerPhiAffineCertificate.certificateInequality L R E := by
  have hbb : b < 1 := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hzm : (0 : ℝ) < 1 - a - b := by linarith
  have hzmsmall : 1 - a - b < 1 / 10000 := by linarith
  have hHa : H a ≤ 1 / 500 := FCRay.H_small_upper ha.le (by linarith)
  have hHbc : H b = H (1 - b) := (H_complement b).symm
  have hHb : H b ≤ 1 / 500 := by
    rw [hHbc]; exact FCRay.H_small_upper (by linarith) (by linarith)
  have hEsmall : E ≤ 1 / 500 := by
    have : H a ≤ H b := by
      rw [hHbc]
      exact H_strictMonoOn.monotoneOn
        (show a ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨ha.le, by linarith⟩)
        (show (1 - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
        (by linarith)
    linarith
  -- feasibility of the psi tangent at 2E
  have h2E : 2 * E < 1 - a - b :=
    FCActive.active_forces_two_E_lt ha hb hsum hcut hE hEsmall hactive
  have hHbig : 4 * (1 - a - b) * (1 - (1 - a - b)) < H (1 - a - b) :=
    H_gt_parabola hzm (by linarith)
  have hHbge : H (1 - a - b) ≤ H b := by
    rw [hHbc]
    exact H_strictMonoOn.monotoneOn
      (show (1 - a - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨hzm.le, by linarith⟩)
      (show (1 - b) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨by linarith, by linarith⟩)
      (by linarith)
  have h2EHb : 2 * E < H b := by
    have hstep : 1 - a - b ≤ 4 * (1 - a - b) * (1 - (1 - a - b)) := by
      nlinarith only [hzm, hzmsmall]
    linarith [hHbig, hHbge, h2E, hstep]
  have h2Epos : (0 : ℝ) < 2 * E := by linarith
  refine ⟨FCPilot.zeroSupport a, psiSupport b (2 * E) h2Epos h2EHb, ?_⟩
  -- childFloor
  have hRs : (psiSupport b (2 * E) h2Epos h2EHb).slope = deriv (psi b) (2 * E) := rfl
  have hRi : (psiSupport b (2 * E) h2Epos h2EHb).intercept
      = psi b (2 * E) - deriv (psi b) (2 * E) * (2 * E) := rfl
  have hsneg : deriv (psi b) (2 * E) ≤ -2 := by
    apply deriv_psi_neg
    · linarith [H_le_one b]
    · linarith
  have hlo : allocationLower a b E = 0 := by
    unfold allocationLower
    exact max_eq_left (by linarith)
  have hupnn : (0 : ℝ) ≤ allocationUpper a b E := by
    unfold allocationUpper
    exact le_min (H_nonneg ha.le (by linarith)) (by linarith)
  have hcf : childFloor (FCPilot.zeroSupport a) (psiSupport b (2 * E) h2Epos h2EHb) E
      = psi b (2 * E) / 2 := by
    unfold childFloor
    rw [FCPilot.zeroSupport_intercept, FCPilot.zeroSupport_slope, hRi, hRs, hlo]
    rw [min_eq_left (by nlinarith only [hsneg, hupnn])]
    ring
  -- assemble
  have hmid : |1 - 2 * ((a + b) / 2)| = 1 - a - b := by
    rw [show (1 : ℝ) - 2 * ((a + b) / 2) = 1 - a - b by ring]
    exact abs_of_pos hzm
  have hphiM : phi ((a + b) / 2) E = eta E - F (1 - a - b) E := by
    unfold phi; rw [hmid]
  have hscf : F (b - a) E ≤ scalarCostFloor a b E := by
    unfold scalarCostFloor; exact le_max_left _ _
  show phi ((a + b) / 2) E
    - childFloor (FCPilot.zeroSupport a) (psiSupport b (2 * E) h2Epos h2EHb) E
    ≤ scalarCostFloor a b E
  rw [hcf, hphiM]
  linarith [hscalar, hscf]

#check @psi_ge_four_deficit
#check @deriv_psi_neg
#check @capped_certificate_of_scalar
#print axioms psi_ge_four_deficit
#print axioms deriv_psi_neg
#print axioms capped_certificate_of_scalar

end GeneralCK.FCCapped

end


