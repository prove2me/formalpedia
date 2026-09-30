-- Prove2me | Definitions.Def_CK_CKLaneM03_Kernel
-- name    : CK_CKLaneM03_Kernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:51:41.901803+00:00
-- url     : https://prove2.me/theorems/fb6d58e7-7ef9-4fcb-8778-e027e3ec73e8
-- title:
--   Courtade–Kumar proof module `CKLaneM03.Kernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM03.Kernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM03.Kernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM03.Kernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM03/Kernel.lean)

import Definitions.Def_CK_GeneralCK_RadialConcavity
import Definitions.Def_CK_GeneralCK_RadialContact
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneSymmetric
import Definitions.Def_CK_GeneralCK_BellmanAssembly
import Definitions.Def_CK_GeneralCK_DeterministicCap
import Definitions.Def_CK_GeneralCK_SmallMeanAnalytic
import Definitions.Def_CK_GeneralCK_LogSum
import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneE_SlopeBounds
import Definitions.Def_CK_CKLaneD_FleetBase

-- ===== source module CKLaneM03.Kernel =====
section

/-!
# Lane M03: semantic kernel for the archived same-side `endpoint` method

Archived method (CK_GENERAL_COMPLETION/same_side/COVER.py, owner `endpoint`): on a leaf box
`x ∈ [xlo,xhi]`, `b ∈ [blo,bhi]`, `t ∈ [tlo,thi]` of the same-side cover
(`a = b 2^-x`, `E = t (H a + H b)/2`), accept iff `F(D, E⁺)/D² ≥ K p̄`, where
`Δ ≤ K d²`, `p̄ ≥ (P'(s) + P'(I))/2`, `D ≥ d = b - a`, `E⁺ ≥ E`.

`SBox`/`InSBox` state the exact archived box at law level (the ratio form
`2^-xhi ≤ a/b ≤ 2^-xlo` is `x ∈ [xlo,xhi]`; `tlo C ≤ E ≤ thi C` is `t ∈ [tlo,thi]`);
the children entropies are arbitrary (only the mean entropy is constrained).

`epCheck_sound : epCheck X w = true → Sem X` has no other hypothesis.  The checker recomputes
every enclosure: `2^-x` brackets (exact `Nat` powers), `H` at the box corners, the sharp
entropy-drop coefficient `K` via `Cn(z)/z²` monotonicity at rational points, the two slope
anchors, and the radial contact bracket.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM03

open GeneralCK CKLaneE.FP

/-! ## Boxes and the semantic statement -/

/-- An archived same-side box in `(x, b, t)` coordinates. -/
structure SBox where
  xlo : ℚ
  xhi : ℚ
  blo : ℚ
  bhi : ℚ
  tlo : ℚ
  thi : ℚ
  deriving Repr, DecidableEq

/-- Law-level membership of `(a, b, E)` in the exact archived box. -/
def InSBox (X : SBox) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(X.xhi : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(X.xlo : ℝ)) ∧
    (X.blo : ℝ) ≤ b ∧ b ≤ (X.bhi : ℝ) ∧
    (X.tlo : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (X.thi : ℝ) * ((H a + H b) / 2)

/-- Semantic Bellman statement for the psi candidate on the whole box. -/
def Sem (X : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InSBox X μ.a μ.b μ.meanEntropy →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- Untrusted certificate data. -/
structure EpCert where
  rlo : ℚ
  rhi : ℚ
  vS : ℚ
  vI : ℚ
  vc : ℚ
  useHm : Bool
  deriving Repr, DecidableEq

/-! ## Derived quantities (recomputed by the checker) -/

section Derived
variable (X : SBox) (w : EpCert)

def epAlo : ℚ := X.blo * w.rlo
def epAhi : ℚ := X.bhi * w.rhi
def epChi : ℚ := (Hhi (epAhi X w) + Hhi X.bhi) / 2
def epClo : ℚ := (Hlo (epAlo X w) + Hlo X.blo) / 2
def epSHi : ℚ := epChi X w * (1 - X.tlo)
def epEHi : ℚ := X.thi * epChi X w
def epMlo : ℚ := X.blo * (1 + w.rlo) / 2
def epMhi : ℚ := X.bhi * (1 + w.rhi) / 2
def epDhi : ℚ := X.bhi * (1 - w.rlo)
def epRho : ℚ := (1 - w.rlo) / (1 + w.rlo)
def epQR : ℚ := (1 - epRho w) / 2
def epKap : ℚ := epDhi X w / (2 * (1 - epMhi X w))
def epQK : ℚ := (1 - epKap X w) / 2
def epCR : ℚ := (1 - Hlo (epQR w)) / (epRho w * epRho w)
def epCK : ℚ := (1 - Hlo (epQK X w)) / (epKap X w * epKap X w)
def epK : ℚ := (epCR w / epMlo X w + epCK X w / (1 - epMhi X w)) / 4
def epIHi : ℚ :=
  if w.useHm then Hhi (epMhi X w) - X.tlo * epClo X w
  else epSHi X w + epK X w * (epDhi X w * epDhi X w)
def epPbar : ℚ := (P1up w.vS + P1up w.vI) / 2

end Derived

/-- Lower bound for `J v` from the log certificate. -/
def epJlo (v : ℚ) : ℚ := lamLo v / LqHi

/-- Entropy points needed only for the `H(m)` branch of the information bound. -/
def epHmOK (X : SBox) (w : EpCert) : Bool :=
  if w.useHm then ptOk (epAlo X w) && ptOk X.blo && ptOk (epMhi X w) else true

/-- The Boolean checker of the archived same-side `endpoint` inequality. -/
def epCheck (X : SBox) (w : EpCert) : Bool :=
  decide (0 ≤ X.xlo ∧ X.xlo ≤ X.xhi ∧ 0 < X.blo ∧ X.blo ≤ X.bhi ∧ 2 * X.bhi ≤ 1 ∧
    0 ≤ X.tlo ∧ X.tlo ≤ X.thi ∧ X.thi ≤ 1) &&
  decide (0 < w.rlo ∧ w.rlo ≤ w.rhi ∧ w.rhi ≤ 1) &&
  CKLaneD.pow2LowerOK w.rlo X.xhi && CKLaneD.pow2UpperOK w.rhi X.xlo &&
  ptOk (epAhi X w) && ptOk X.bhi && ptOk (epQR w) && ptOk (epQK X w) &&
  epHmOK X w &&
  decide (0 < epKap X w ∧ epKap X w ≤ 1 ∧ 0 ≤ epK X w) &&
  decide (epIHi X w < 1) &&
  anchorOk w.vS (epSHi X w) && anchorOk w.vI (epIHi X w) &&
  decide (0 ≤ epPbar w) &&
  ptOk w.vc &&
  decide (w.vc < 1 / 2 ∧ 0 ≤ lamLo w.vc ∧ 0 < epDhi X w) &&
  decide (epEHi X w * (1 - 2 * w.vc) ≤ epDhi X w * Hlo w.vc) &&
  decide (epK X w * epPbar w * epDhi X w ≤ epJlo w.vc)

/-! ## Analytic lemmas -/

/-- Monotonicity of `C(z)/z²`, `C(z) = 1 - H((1-z)/2)`, turned into a pointwise bound. -/
theorem ep_biasDeficit_le {z zh c : ℝ} (hz : 0 < z) (hzz : z ≤ zh) (hzh : zh ≤ 1)
    (hc : (1 - H ((1 - zh) / 2)) / zh ^ 2 ≤ c) :
    1 - H ((1 - z) / 2) ≤ z ^ 2 * c := by
  have hzh0 : 0 < zh := lt_of_lt_of_le hz hzz
  have hmono : SmallMean.Cn z / z ^ 2 ≤ SmallMean.Cn zh / zh ^ 2 :=
    SmallMean.Cn_ratio_monotone ⟨hz, hzz.trans hzh⟩ ⟨hzh0, hzh⟩ hzz
  unfold SmallMean.Cn at hmono
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 - H ((1 - z) / 2)) / z ^ 2 ≤ (1 - H ((1 - zh) / 2)) / zh ^ 2 := by
    rw [mul_div_assoc, mul_div_assoc] at hmono
    exact le_of_mul_le_mul_left hmono hL
  have hz2 : 0 < z ^ 2 := pow_pos hz 2
  have hzne : z ^ 2 ≠ 0 := hz2.ne'
  have e : 1 - H ((1 - z) / 2) = z ^ 2 * ((1 - H ((1 - z) / 2)) / z ^ 2) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (h1.trans hc) hz2.le

/-- Sharp normalized entropy-drop bound with box constants (archive `K`, `Δ/d² ≤ K`). -/
theorem ep_drop_le {a b ρh κh c1 c2 mL mH : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hρ : (b - a) / (a + b) ≤ ρh) (hρh : ρh ≤ 1) (hκ : (b - a) / (2 - a - b) ≤ κh)
    (hκh : κh ≤ 1)
    (hc1 : (1 - H ((1 - ρh) / 2)) / ρh ^ 2 ≤ c1) (hc2 : (1 - H ((1 - κh) / 2)) / κh ^ 2 ≤ c2)
    (hmL : 0 < mL) (hmL' : mL ≤ (a + b) / 2) (hmH : (a + b) / 2 ≤ mH) (hmH1 : mH < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (c1 / mL + c2 / (1 - mH)) / 4 * (b - a) ^ 2 := by
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hd : 0 < b - a := by linarith
  have hsne : a + b ≠ 0 := hs.ne'
  have htne : 2 - a - b ≠ 0 := ht.ne'
  have hchain := deterministic_entropy_chain ha (hab.trans hb) (ha.trans hab) hb
  have hρ0 : 0 < (b - a) / (a + b) := div_pos hd hs
  have hκ0 : 0 < (b - a) / (2 - a - b) := div_pos hd ht
  have hpa : a / (a + b) = (1 - (b - a) / (a + b)) / 2 := by
    field_simp; ring
  have hpb : (1 - b) / (2 - a - b) = (1 - (b - a) / (2 - a - b)) / 2 := by
    field_simp; ring
  rw [hchain, hpa, hpb]
  have h1 := ep_biasDeficit_le hρ0 hρ hρh hc1
  have h2 := ep_biasDeficit_le hκ0 hκ hκh hc2
  have hρh0 : 0 < ρh := lt_of_lt_of_le hρ0 hρ
  have hκh0 : 0 < κh := lt_of_lt_of_le hκ0 hκ
  have hH1 : H ((1 - ρh) / 2) ≤ 1 := H_le_one _
  have hH2 : H ((1 - κh) / 2) ≤ 1 := H_le_one _
  have hc10 : 0 ≤ c1 := le_trans (div_nonneg (by linarith) (by positivity)) hc1
  have hc20 : 0 ≤ c2 := le_trans (div_nonneg (by linarith) (by positivity)) hc2
  have hm0 : 0 < (a + b) / 2 := by linarith
  have hm1 : 0 < 1 - (a + b) / 2 := by linarith
  have hmH0 : 0 < 1 - mH := by linarith
  have e1 : (a + b) / 2 * (((b - a) / (a + b)) ^ 2 * c1) =
      (b - a) ^ 2 * (c1 / (4 * ((a + b) / 2))) := by
    field_simp; ring
  have e2 : (1 - (a + b) / 2) * (((b - a) / (2 - a - b)) ^ 2 * c2) =
      (b - a) ^ 2 * (c2 / (4 * (1 - (a + b) / 2))) := by
    rw [show 1 - (a + b) / 2 = (2 - a - b) / 2 by ring]
    field_simp
    try ring
  have k1 : (a + b) / 2 * (1 - H ((1 - (b - a) / (a + b)) / 2)) ≤
      (b - a) ^ 2 * (c1 / (4 * mL)) := by
    calc (a + b) / 2 * (1 - H ((1 - (b - a) / (a + b)) / 2))
        ≤ (a + b) / 2 * (((b - a) / (a + b)) ^ 2 * c1) := mul_le_mul_of_nonneg_left h1 hm0.le
      _ = (b - a) ^ 2 * (c1 / (4 * ((a + b) / 2))) := e1
      _ ≤ (b - a) ^ 2 * (c1 / (4 * mL)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact div_le_div_of_nonneg_left hc10 (by linarith) (by linarith)
  have k2 : (1 - (a + b) / 2) * (1 - H ((1 - (b - a) / (2 - a - b)) / 2)) ≤
      (b - a) ^ 2 * (c2 / (4 * (1 - mH))) := by
    calc (1 - (a + b) / 2) * (1 - H ((1 - (b - a) / (2 - a - b)) / 2))
        ≤ (1 - (a + b) / 2) * (((b - a) / (2 - a - b)) ^ 2 * c2) :=
          mul_le_mul_of_nonneg_left h2 hm1.le
      _ = (b - a) ^ 2 * (c2 / (4 * (1 - (a + b) / 2))) := e2
      _ ≤ (b - a) ^ 2 * (c2 / (4 * (1 - mH))) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact div_le_div_of_nonneg_left hc20 (by linarith) (by linarith)
  have hmLne : mL ≠ 0 := hmL.ne'
  have hmHne : 1 - mH ≠ 0 := hmH0.ne'
  have e3 : (c1 / mL + c2 / (1 - mH)) / 4 * (b - a) ^ 2 =
      (b - a) ^ 2 * (c1 / (4 * mL)) + (b - a) ^ 2 * (c2 / (4 * (1 - mH))) := by
    field_simp
    try ring
  rw [e3]
  linarith

/-- Radial endpoint bound: `F(d,E) ≥ d² J(v)/D` from a contact bracket at `(D, E⁺)`. -/
theorem ep_F_lower {d D E Eh v : ℝ} (hd : 0 < d) (hdD : d ≤ D) (hE : 0 < E) (hEE : E ≤ Eh)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) (hcont : Eh * (1 - 2 * v) ≤ D * H v) :
    d ^ 2 * (J v / D) ≤ F d E := by
  have hD : 0 < D := lt_of_lt_of_le hd hdD
  have hEh : 0 < Eh := lt_of_lt_of_le hE hEE
  have hanti : F D E / D ^ 2 ≤ F d E / d ^ 2 :=
    antitoneOn_F_div_sq hE (show d ∈ Set.Ioi (0 : ℝ) from hd)
      (show D ∈ Set.Ioi (0 : ℝ) from hD) hdD
  have hFD : F D E = D * J (radialContact D E) := by
    unfold F; rw [if_neg hD.ne']
  have hrc0 := radialContact_pos hD hE
  have h1 : radialContact D E ≤ radialContact D Eh := radialContact_mono_entropy hD hE hEE
  have h2 : radialContact D Eh ≤ v := (radialContact_le_iff hD hEh hv0 hv1).mpr hcont
  have hJ : J v ≤ J (radialContact D E) := J_antitone hrc0 hv1 (h1.trans h2)
  have hd2 : 0 < d ^ 2 := pow_pos hd 2
  have hD2 : 0 < D ^ 2 := pow_pos hD 2
  have hkey : d ^ 2 * (F D E / D ^ 2) ≤ F d E := by
    have h3 := mul_le_mul_of_nonneg_left hanti hd2.le
    have hdne : d ^ 2 ≠ 0 := hd2.ne'
    have e : d ^ 2 * (F d E / d ^ 2) = F d E := by field_simp
    rw [e] at h3
    exact h3
  have e2 : F D E / D ^ 2 = J (radialContact D E) / D := by
    rw [hFD, div_eq_div_iff hD2.ne' hD.ne']
    ring
  rw [e2] at hkey
  calc d ^ 2 * (J v / D) ≤ d ^ 2 * (J (radialContact D E) / D) := by
        apply mul_le_mul_of_nonneg_left _ hd2.le
        exact div_le_div_of_nonneg_right hJ hD.le
    _ ≤ F d E := hkey

theorem ep_Jlo_le {v : ℚ} (hpt : ptOk v = true) (hlam : 0 ≤ lamLo v) :
    ((epJlo v : ℚ) : ℝ) ≤ J (v : ℝ) := by
  obtain ⟨hl, _⟩ := lam_bounds hpt
  obtain ⟨_, hL2⟩ := log_two_mem
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlam' : (0 : ℝ) ≤ ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  unfold J
  have e : ((epJlo v : ℚ) : ℝ) = ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) := by
    simp only [epJlo]; push_cast; try ring
  rw [e]
  calc ((lamLo v : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((lamLo v : ℚ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_left hlam' hL hL2
    _ ≤ Real.log ((1 - (v : ℝ)) / v) / Real.log 2 := div_le_div_of_nonneg_right hl hL.le

theorem ep_H_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) : H x ≤ H y :=
  H_strictMonoOn.monotoneOn ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy

/-- Box geometry in real coordinates. -/
theorem ep_geom {a b rlo rhi blo bhi : ℝ} (hb0 : 0 < b) (hrlo : 0 < rlo)
    (hrr : rlo ≤ rhi) (hr1 : rhi ≤ 1) (hbl : blo ≤ b) (hbh : b ≤ bhi) (hbh2 : 2 * bhi ≤ 1)
    (hlo : rlo * b ≤ a) (hhi : a ≤ rhi * b) :
    a ≤ b ∧ a ≤ bhi * rhi ∧ bhi * rhi ≤ 1 / 2 ∧ blo * (1 + rlo) / 2 ≤ (a + b) / 2 ∧
      (a + b) / 2 ≤ bhi * (1 + rhi) / 2 ∧ bhi * (1 + rhi) / 2 ≤ 1 / 2 ∧
      b - a ≤ bhi * (1 - rlo) ∧ blo * rlo ≤ a := by
  have hrhi0 : 0 ≤ rhi := by linarith
  have hbhi0 : 0 < bhi := by linarith
  have h1 : rhi * b ≤ rhi * bhi := mul_le_mul_of_nonneg_left hbh hrhi0
  have h2 : rlo * blo ≤ rlo * b := mul_le_mul_of_nonneg_left hbl hrlo.le
  have h3 : rhi * bhi ≤ bhi := by nlinarith
  have h4 : rhi * b ≤ b := by nlinarith
  have h5 : (1 - rlo) * b ≤ (1 - rlo) * bhi := mul_le_mul_of_nonneg_left hbh (by linarith)
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem ep_rho_le {a b rlo : ℝ} (ha : 0 < a) (hb : 0 < b) (hrlo : 0 < rlo)
    (hlo : rlo * b ≤ a) : (b - a) / (a + b) ≤ (1 - rlo) / (1 + rlo) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem ep_kap_le {a b dh mh : ℝ} (hab : a < b) (hb : b < 1) (hd : b - a ≤ dh)
    (hm : (a + b) / 2 ≤ mh) (hmh : mh < 1) :
    (b - a) / (2 - a - b) ≤ dh / (2 * (1 - mh)) := by
  have hden1 : (0 : ℝ) < 2 - a - b := by linarith
  have hden2 : (0 : ℝ) < 2 * (1 - mh) := by linarith
  rw [div_le_div_iff₀ hden1 hden2]
  have hmm : 2 * (1 - mh) ≤ 2 - a - b := by linarith
  have hdd : (0 : ℝ) ≤ b - a := by linarith
  calc (b - a) * (2 * (1 - mh)) ≤ (b - a) * (2 - a - b) := mul_le_mul_of_nonneg_left hmm hdd
    _ ≤ dh * (2 - a - b) := mul_le_mul_of_nonneg_right hd hden1.le

theorem ep_sE {C Chi E tlo thi : ℝ} (hC : C ≤ Chi) (ht0 : 0 ≤ tlo)
    (htt : tlo ≤ thi) (ht1 : tlo ≤ 1) (hE1 : tlo * C ≤ E) (hE2 : E ≤ thi * C) :
    C - E ≤ Chi * (1 - tlo) ∧ E ≤ thi * Chi := by
  have h1 : (1 - tlo) * C ≤ (1 - tlo) * Chi := mul_le_mul_of_nonneg_left hC (by linarith)
  have h2 : thi * C ≤ thi * Chi := mul_le_mul_of_nonneg_left hC (by linarith)
  constructor <;> nlinarith

/-! ## Soundness -/

set_option maxHeartbeats 4000000 in
theorem epCheck_sound {X : SBox} {w : EpCert} (h : epCheck X w = true) : Sem X := by
  intro k μ hbox
  unfold InSBox at hbox
  unfold epCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, qb0, _, qb2, qt0, qtt, qt1, qr0, qrr, qr1, hp2l, hp2u, hpA, hpB, hpR, hpK,
    hhm, _, qkap1, qK0, hI1, hvS, hvI, hpbar, hpc, qvc2, qlam, qd0, hcont, hfin⟩ := h
  obtain ⟨hx1, hx2, hb1, hb2, hE1, hE2⟩ := hbox
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1' : μ.b < 1 := μ.b_interior.2
  have hEpos : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy; linarith [μ.e_pos, μ.f_pos]
  -- casts of the rational facts
  have rb0 : (0 : ℝ) < X.blo := by exact_mod_cast qb0
  have rbb2 : 2 * (X.bhi : ℝ) ≤ 1 := by exact_mod_cast qb2
  have rt0 : (0 : ℝ) ≤ X.tlo := by exact_mod_cast qt0
  have rtt : (X.tlo : ℝ) ≤ X.thi := by exact_mod_cast qtt
  have rt1 : (X.thi : ℝ) ≤ 1 := by exact_mod_cast qt1
  have rr0 : (0 : ℝ) < w.rlo := by exact_mod_cast qr0
  have rrr : (w.rlo : ℝ) ≤ w.rhi := by exact_mod_cast qrr
  have rr1 : (w.rhi : ℝ) ≤ 1 := by exact_mod_cast qr1
  -- ratio bounds: rlo * b ≤ a ≤ rhi * b
  have hrl := (CKLaneD.pow2LowerOK_sound hp2l).trans hx1
  have hru := hx2.trans (CKLaneD.pow2UpperOK_sound hp2u)
  have hab_lo : (w.rlo : ℝ) * μ.b ≤ μ.a := by
    have h' := mul_le_mul_of_nonneg_right hrl hb0.le
    rwa [div_mul_cancel₀ μ.a hb0.ne'] at h'
  have hab_hi : μ.a ≤ (w.rhi : ℝ) * μ.b := by
    have h' := mul_le_mul_of_nonneg_right hru hb0.le
    rwa [div_mul_cancel₀ μ.a hb0.ne'] at h'
  obtain ⟨hab, ha_ahi', hahi_half', hm_lo', hm_hi', hmhi_half', hd_hi', halo'⟩ :=
    ep_geom hb0 rr0 rrr rr1 hb1 hb2 rbb2 hab_lo hab_hi
  have hbhalf : μ.b ≤ 1 / 2 := by linarith only [hb2, rbb2]
  -- casts of the box points
  have eahi : ((epAhi X w : ℚ) : ℝ) = (X.bhi : ℝ) * w.rhi := by unfold epAhi; push_cast; try ring
  have ealo : ((epAlo X w : ℚ) : ℝ) = (X.blo : ℝ) * w.rlo := by unfold epAlo; push_cast; try ring
  have emlo : ((epMlo X w : ℚ) : ℝ) = (X.blo : ℝ) * (1 + w.rlo) / 2 := by
    unfold epMlo; push_cast; try ring
  have emhi : ((epMhi X w : ℚ) : ℝ) = (X.bhi : ℝ) * (1 + w.rhi) / 2 := by
    unfold epMhi; push_cast; try ring
  have edhi : ((epDhi X w : ℚ) : ℝ) = (X.bhi : ℝ) * (1 - w.rlo) := by
    unfold epDhi; push_cast; try ring
  have ha_ahi : μ.a ≤ ((epAhi X w : ℚ) : ℝ) := by rw [eahi]; exact ha_ahi'
  have hahi_half : ((epAhi X w : ℚ) : ℝ) ≤ 1 / 2 := by rw [eahi]; exact hahi_half'
  have hm_lo : ((epMlo X w : ℚ) : ℝ) ≤ (μ.a + μ.b) / 2 := by rw [emlo]; exact hm_lo'
  have hm_hi : (μ.a + μ.b) / 2 ≤ ((epMhi X w : ℚ) : ℝ) := by rw [emhi]; exact hm_hi'
  have hmhi_half : ((epMhi X w : ℚ) : ℝ) ≤ 1 / 2 := by rw [emhi]; exact hmhi_half'
  have hmlo0 : (0 : ℝ) < ((epMlo X w : ℚ) : ℝ) := by
    rw [emlo]
    have h1 : (0 : ℝ) < 1 + w.rlo := by linarith only [rr0]
    have h2 := mul_pos rb0 h1
    linarith only [h2]
  have hd_hi : μ.b - μ.a ≤ ((epDhi X w : ℚ) : ℝ) := by rw [edhi]; exact hd_hi'
  -- entropy enclosures at the law's means
  obtain ⟨_, hHA⟩ := H_bounds hpA
  obtain ⟨_, hHB⟩ := H_bounds hpB
  have hHa : H μ.a ≤ ((Hhi (epAhi X w) : ℚ) : ℝ) :=
    (ep_H_mono ha0.le ha_ahi hahi_half).trans hHA
  have hHb : H μ.b ≤ ((Hhi X.bhi : ℚ) : ℝ) :=
    (ep_H_mono hb0.le hb2 (by linarith only [rbb2])).trans hHB
  have eChi : ((epChi X w : ℚ) : ℝ) =
      (((Hhi (epAhi X w) : ℚ) : ℝ) + ((Hhi X.bhi : ℚ) : ℝ)) / 2 := by
    unfold epChi; push_cast; try ring
  have hC_hi : (H μ.a + H μ.b) / 2 ≤ ((epChi X w : ℚ) : ℝ) := by
    rw [eChi]; linarith only [hHa, hHb]
  -- deficit, entropy, information
  have hsdef : μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hΔdef : μ.entropyDrop = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hs0 : 0 ≤ μ.meanDeficit := μ.meanDeficit_mem.1
  have hΔ0 : 0 ≤ μ.entropyDrop := μ.entropyDrop_nonneg
  have esHi : ((epSHi X w : ℚ) : ℝ) = ((epChi X w : ℚ) : ℝ) * (1 - X.tlo) := by
    unfold epSHi; push_cast; try ring
  have eEhi : ((epEHi X w : ℚ) : ℝ) = (X.thi : ℝ) * ((epChi X w : ℚ) : ℝ) := by
    unfold epEHi; push_cast; try ring
  obtain ⟨hsE1, hsE2⟩ := ep_sE hC_hi rt0 rtt (rtt.trans rt1) hE1 hE2
  have hs_hi : μ.meanDeficit ≤ ((epSHi X w : ℚ) : ℝ) := by rw [hsdef, esHi]; exact hsE1
  have hE_hi : μ.meanEntropy ≤ ((epEHi X w : ℚ) : ℝ) := by rw [eEhi]; exact hsE2
  -- the entropy-drop coefficient
  have erho : ((epRho w : ℚ) : ℝ) = (1 - (w.rlo : ℝ)) / (1 + w.rlo) := by
    unfold epRho; push_cast; try ring
  have eqR : ((epQR w : ℚ) : ℝ) = (1 - ((epRho w : ℚ) : ℝ)) / 2 := by
    unfold epQR; push_cast; try ring
  have ekap : ((epKap X w : ℚ) : ℝ) =
      ((epDhi X w : ℚ) : ℝ) / (2 * (1 - ((epMhi X w : ℚ) : ℝ))) := by
    unfold epKap; push_cast; try ring
  have eqK : ((epQK X w : ℚ) : ℝ) = (1 - ((epKap X w : ℚ) : ℝ)) / 2 := by
    unfold epQK; push_cast; try ring
  have ecR : ((epCR w : ℚ) : ℝ) =
      (1 - ((Hlo (epQR w) : ℚ) : ℝ)) / (((epRho w : ℚ) : ℝ) * ((epRho w : ℚ) : ℝ)) := by
    unfold epCR; push_cast; try ring
  have ecK : ((epCK X w : ℚ) : ℝ) =
      (1 - ((Hlo (epQK X w) : ℚ) : ℝ)) / (((epKap X w : ℚ) : ℝ) * ((epKap X w : ℚ) : ℝ)) := by
    unfold epCK; push_cast; try ring
  have eK : ((epK X w : ℚ) : ℝ) =
      (((epCR w : ℚ) : ℝ) / ((epMlo X w : ℚ) : ℝ) +
        ((epCK X w : ℚ) : ℝ) / (1 - ((epMhi X w : ℚ) : ℝ))) / 4 := by
    unfold epK; push_cast; try ring
  have rK0 : (0 : ℝ) ≤ ((epK X w : ℚ) : ℝ) := by exact_mod_cast qK0
  have rkap1 : ((epKap X w : ℚ) : ℝ) ≤ 1 := by exact_mod_cast qkap1
  have hdrop : μ.entropyDrop ≤ ((epK X w : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · have hΔz : μ.entropyDrop = 0 := by
        rw [hΔdef, ← heq, show (μ.a + μ.a) / 2 = μ.a by ring]; ring
      rw [hΔz, ← heq, sub_self]
      simp
    · have hρ : (μ.b - μ.a) / (μ.a + μ.b) ≤ ((epRho w : ℚ) : ℝ) := by
        rw [erho]; exact ep_rho_le ha0 hb0 rr0 hab_lo
      have hρh1 : ((epRho w : ℚ) : ℝ) ≤ 1 := by
        rw [erho, div_le_one (by linarith only [rr0])]; linarith only [rr0]
      have hκ : (μ.b - μ.a) / (2 - μ.a - μ.b) ≤ ((epKap X w : ℚ) : ℝ) := by
        rw [ekap]; exact ep_kap_le hlt hb1' hd_hi hm_hi (by linarith only [hmhi_half])
      obtain ⟨hHR, _⟩ := H_bounds hpR
      obtain ⟨hHK, _⟩ := H_bounds hpK
      have hc1 : (1 - H ((1 - ((epRho w : ℚ) : ℝ)) / 2)) / ((epRho w : ℚ) : ℝ) ^ 2 ≤
          ((epCR w : ℚ) : ℝ) := by
        rw [ecR, ← eqR, sq]
        apply div_le_div_of_nonneg_right _ (mul_self_nonneg _)
        linarith only [hHR]
      have hc2 : (1 - H ((1 - ((epKap X w : ℚ) : ℝ)) / 2)) / ((epKap X w : ℚ) : ℝ) ^ 2 ≤
          ((epCK X w : ℚ) : ℝ) := by
        rw [ecK, ← eqK, sq]
        apply div_le_div_of_nonneg_right _ (mul_self_nonneg _)
        linarith only [hHK]
      have hd := ep_drop_le ha0 hlt hb1' hρ hρh1 hκ rkap1 hc1 hc2 hmlo0 hm_lo hm_hi
        (by linarith only [hmhi_half])
      rw [hΔdef, eK]
      exact hd
  -- information range
  have hI_hi : μ.entropyDrop + μ.meanDeficit ≤ ((epIHi X w : ℚ) : ℝ) := by
    unfold epIHi
    split_ifs with hu
    · simp only [epHmOK, if_pos hu, Bool.and_eq_true] at hhm
      obtain ⟨⟨hpal, hpbl⟩, hpm⟩ := hhm
      obtain ⟨hHal, _⟩ := H_bounds hpal
      obtain ⟨hHbl, _⟩ := H_bounds hpbl
      obtain ⟨_, hHm⟩ := H_bounds hpm
      have halo_a : ((epAlo X w : ℚ) : ℝ) ≤ μ.a := by rw [ealo]; exact halo'
      have halo0 : (0 : ℝ) ≤ ((epAlo X w : ℚ) : ℝ) := by rw [ealo]; exact (mul_pos rb0 rr0).le
      have hHa_lo : ((Hlo (epAlo X w) : ℚ) : ℝ) ≤ H μ.a :=
        hHal.trans (ep_H_mono halo0 halo_a (by linarith only [ha_ahi, hahi_half]))
      have hHb_lo : ((Hlo X.blo : ℚ) : ℝ) ≤ H μ.b := hHbl.trans (ep_H_mono rb0.le hb1 hbhalf)
      have hHm_hi : H ((μ.a + μ.b) / 2) ≤ ((Hhi (epMhi X w) : ℚ) : ℝ) :=
        (ep_H_mono (by linarith only [ha0, hb0]) hm_hi hmhi_half).trans hHm
      have eClo : ((epClo X w : ℚ) : ℝ) =
          (((Hlo (epAlo X w) : ℚ) : ℝ) + ((Hlo X.blo : ℚ) : ℝ)) / 2 := by
        unfold epClo; push_cast; try ring
      have hClo : ((epClo X w : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
        rw [eClo]; linarith only [hHa_lo, hHb_lo]
      have htC : (X.tlo : ℝ) * ((epClo X w : ℚ) : ℝ) ≤ μ.meanEntropy :=
        (mul_le_mul_of_nonneg_left hClo rt0).trans hE1
      push_cast
      rw [hΔdef, hsdef]
      linarith only [hHm_hi, htC]
    · push_cast
      have hd0 : 0 ≤ μ.b - μ.a := by linarith only [hab]
      have hsq : (μ.b - μ.a) ^ 2 ≤ ((epDhi X w : ℚ) : ℝ) * ((epDhi X w : ℚ) : ℝ) := by
        rw [sq]; exact mul_le_mul hd_hi hd_hi hd0 (hd0.trans hd_hi)
      have h' := mul_le_mul_of_nonneg_left hsq rK0
      linarith only [hdrop, hs_hi, h']
  have rI1 : ((epIHi X w : ℚ) : ℝ) < 1 := by exact_mod_cast hI1
  have hI1' : μ.entropyDrop + μ.meanDeficit < 1 := lt_of_le_of_lt hI_hi rI1
  -- split bound via trapezoid and slope anchors
  have htrap := CKLaneE.P_trapezoid hs0 (le_add_of_nonneg_left hΔ0) hI1'
  have hPS := anchorOk_sound hvS hs0 hs_hi
  have hPI := anchorOk_sound hvI (add_nonneg hΔ0 hs0) hI_hi
  have epbar : ((epPbar w : ℚ) : ℝ) = (((P1up w.vS : ℚ) : ℝ) + ((P1up w.vI : ℚ) : ℝ)) / 2 := by
    unfold epPbar; push_cast; try ring
  have rpbar : (0 : ℝ) ≤ ((epPbar w : ℚ) : ℝ) := by exact_mod_cast hpbar
  have hsplit : μ.splitBound ≤ μ.entropyDrop * ((epPbar w : ℚ) : ℝ) := by
    have e : μ.splitBound = Scalar.P (μ.entropyDrop + μ.meanDeficit) - Scalar.P μ.meanDeficit :=
      rfl
    rw [e, epbar]
    have h1 : μ.entropyDrop + μ.meanDeficit - μ.meanDeficit = μ.entropyDrop := by ring
    rw [h1] at htrap
    have h2 := mul_le_mul_of_nonneg_left (add_le_add hPS hPI) hΔ0
    linarith only [htrap, h2]
  have hgap := μ.psi_gap_le_splitBound
  have hmain : μ.entropyDrop * ((epPbar w : ℚ) : ℝ) ≤ μ.cost := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · -- diagonal: Δ = 0 and the cost is nonnegative
      have hΔz : μ.entropyDrop = 0 := by
        rw [hΔdef, ← heq, show (μ.a + μ.a) / 2 = μ.a by ring]; ring
      have hc := LogSum.cost_lower_bound μ
      have hz1 : interiorCost μ.a μ.b = 0 := by
        rw [← heq]; simp [interiorCost]
      have hz2 : (μ.a - μ.b) ^ 2 = 0 := by rw [← heq]; ring
      rw [hz1, hz2, zero_div, zero_mul, add_zero] at hc
      rw [hΔz, zero_mul]
      exact hc
    · -- radial endpoint bound
      have hcostF := PsiEndpointPlane.law_radial_lower μ hlt
      have hd0 : 0 < μ.b - μ.a := by linarith only [hlt]
      have hvc0 : (0 : ℝ) < w.vc := by exact_mod_cast (ptOk_pos hpc).1
      have hvc12 : (w.vc : ℝ) ≤ 1 / 2 := by
        have h' := (Rat.cast_lt (K := ℝ)).mpr qvc2
        push_cast at h'; linarith only [h']
      obtain ⟨hHvc, _⟩ := H_bounds hpc
      have rd0 : (0 : ℝ) < ((epDhi X w : ℚ) : ℝ) := by exact_mod_cast qd0
      have hcontR : ((epEHi X w : ℚ) : ℝ) * (1 - 2 * (w.vc : ℝ)) ≤
          ((epDhi X w : ℚ) : ℝ) * H (w.vc : ℝ) := by
        have h' := (Rat.cast_le (K := ℝ)).mpr hcont
        push_cast at h'
        have h'' := mul_le_mul_of_nonneg_left hHvc rd0.le
        linarith only [h', h'']
      have hF := ep_F_lower hd0 hd_hi hEpos hE_hi hvc0.le hvc12 hcontR
      have hJ := ep_Jlo_le hpc qlam
      have hfinR : ((epK X w : ℚ) : ℝ) * ((epPbar w : ℚ) : ℝ) * ((epDhi X w : ℚ) : ℝ) ≤
          ((epJlo w.vc : ℚ) : ℝ) := by exact_mod_cast hfin
      have hKp : ((epK X w : ℚ) : ℝ) * ((epPbar w : ℚ) : ℝ) ≤
          J (w.vc : ℝ) / ((epDhi X w : ℚ) : ℝ) := by
        rw [le_div_iff₀ rd0]; linarith only [hfinR, hJ]
      have hd2 : 0 ≤ (μ.b - μ.a) ^ 2 := sq_nonneg _
      calc μ.entropyDrop * ((epPbar w : ℚ) : ℝ)
          ≤ ((epK X w : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 * ((epPbar w : ℚ) : ℝ) :=
            mul_le_mul_of_nonneg_right hdrop rpbar
        _ = (μ.b - μ.a) ^ 2 * (((epK X w : ℚ) : ℝ) * ((epPbar w : ℚ) : ℝ)) := by ring
        _ ≤ (μ.b - μ.a) ^ 2 * (J (w.vc : ℝ) / ((epDhi X w : ℚ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hKp hd2
        _ ≤ F (μ.b - μ.a) μ.meanEntropy := hF
        _ ≤ μ.cost := hcostF
  exact hgap.trans (hsplit.trans hmain)

/-- Owner form: on the box and when psi is (weakly) active at the parent, `μ.gap ≤ μ.cost`. -/
theorem sem_gap_le_cost {X : SBox} (hX : Sem X) {k : ℕ} (μ : InteriorLaw (Fin k))
    (hbox : InSBox X μ.a μ.b μ.meanEntropy)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost :=
  (hybrid_gap_le_psi hact).trans (hX k μ hbox)

/-! ## Binding to archived paths -/

/-- Root of the archived same-side cover (`ADAPT_RESULT.json`). -/
def ssRoot : SBox := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

/-- One exact halving step (`COVER.reconstruct`: digit = 2·axis + side). -/
def ssStep (X : SBox) (d : ℕ) : SBox :=
  match d with
  | 0 => { X with xhi := (X.xlo + X.xhi) / 2 }
  | 1 => { X with xlo := (X.xlo + X.xhi) / 2 }
  | 2 => { X with bhi := (X.blo + X.bhi) / 2 }
  | 3 => { X with blo := (X.blo + X.bhi) / 2 }
  | 4 => { X with thi := (X.tlo + X.thi) / 2 }
  | 5 => { X with tlo := (X.tlo + X.thi) / 2 }
  | _ => X

/-- The exact leaf box of an archived path. -/
def ssBox (p : List ℕ) : SBox := p.foldl ssStep ssRoot

/-- Per-leaf acceptance bound to the archived path. -/
def epLeaf (p : List ℕ) (w : EpCert) : Bool := epCheck (ssBox p) w

theorem epLeaf_sound {p : List ℕ} {w : EpCert} (h : epLeaf p w = true) : Sem (ssBox p) :=
  epCheck_sound h

theorem epLeaves_sound (L : List (List ℕ × EpCert))
    (h : (L.all fun x => epLeaf x.1 x.2) = true) :
    ∀ x ∈ L, Sem (ssBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact epLeaf_sound (h x hx)

/-- Compact dyadic literal `n / 2^e` for witness data. -/
def dy (n : ℤ) (e : ℕ) : ℚ := (n : ℚ) / ((2 ^ e : ℕ) : ℚ)

end CKLaneM03

end


