-- Prove2me | Definitions.Def_CK_CKLaneN1c_Endpoint
-- name    : CK_CKLaneN1c_Endpoint
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:11:49.069003+00:00
-- url     : https://prove2.me/theorems/00eaa7e9-7a6f-4fcb-a664-5c54b7669c3e
-- title:
--   Courtade–Kumar proof module `CKLaneN1c.Endpoint` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1c.Endpoint` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1c.Endpoint` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1c.Endpoint (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1c/Endpoint.lean)

import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneD_Analytic
import Definitions.Def_CK_CKLaneN1_SubRows
import Definitions.Def_CK_CKLaneG1_CoverKit2

-- ===== source module CKLaneN1c.Endpoint =====
section

/-!
# Lane N1c-c: Boolean kernel for the transition `endpoint` owner

Archive: `CK_OPPOSITE_EXTENSION.zip` (sha256 3f4b121c…392a), `transition/TRANSITION.py`, `bound`,
owner `endpoint` (PROOF.md §2, (4)); result `TRANSITION_RESULT.json` (sha256 3ebdd33e…3b0c).
Box coordinates `(E, x, y)`, `x = d/E = (b-a)/E`, `y = q/E = (1-a-b)/E` (`CKLaneG1.InExy`).

Acceptance (all exact ℚ, lane E `CKLaneE.FP` log/entropy enclosures):

* `m ≤ mhi = (1 - y₀E₀)/2`, `a ≥ alo = (1 - min(4/5, x₁E₁ + min(2/5, y₁E₁)))/2`,
  `1 - b ≥ blo = (1 - max(0, x₁E₁ - y₀E₀))/2`;
* `H v₁ ≤ E₀ + 1 - H⁺(mhi)`  (so `η(E + C(q)) ≤ (1-2v₁) J(v₁)`),
  `E₁ + 1 - (H⁻(alo) + H⁻(blo))/2 ≤ H v₂`  (so `(1-2v₂) J(v₂) ≤ η(E + (C(d+q)+C(d-q))/2)`),
  `1 - 2 v_c ≤ x₀ H v_c`  (so `x₀ J(v_c) ≤ F(x₀,1)`);
* `(1-2v₁) J⁺(v₁) - (1-2v₂) J⁻(v₂) ≤ E₀ x₀ J⁻(v_c)`.

Soundness (`checkEP_sound`): the only premises are `checkEP B v₁ v₂ v_c = true`, membership of the law
in the exact leaf image `InExy B`, the canonical/central row hypotheses and strict psi-activity.  The
entropy split `e, f` is arbitrary; no stored margins, no real-variable hypotheses.
Chain: `gap ≤ ψ-gap` (`hybrid_gap_le_psi`) `≤ P(H m - E) - P((H a + H b)/2 - E)` (`CKLaneD.law_gap_le_P`,
η convexity) `≤ … ≤ E₀ x₀ J⁻(v_c) ≤ E F(x,1) = F(d,E) ≤ cost` (`PsiEndpointPlane.law_radial_lower`).
-/

set_option autoImplicit false

namespace CKLaneN1c

open GeneralCK CKLaneE.FP CKLaneN1 CKLaneG1

/-! ## Rational enclosures of `J` -/

/-- Lower bound of `J v = log((1-v)/v)/log 2`. -/
def JloQ (v : ℚ) : ℚ := if 0 ≤ lamLo v then lamLo v / LqHi else lamLo v / LqLo
/-- Upper bound of `J v`. -/
def JhiQ (v : ℚ) : ℚ := if 0 ≤ lamHi v then lamHi v / LqLo else lamHi v / LqHi

theorem LqHi_pos : (0 : ℝ) < ((LqHi : ℚ) : ℝ) :=
  LqLo_pos.trans_le (log_two_mem.1.trans log_two_mem.2)

theorem divLq_lo {N0 : ℚ} {N : ℝ} (h : (N0 : ℝ) ≤ N) :
    (((if 0 ≤ N0 then N0 / LqHi else N0 / LqLo : ℚ)) : ℝ) ≤ N / Real.log 2 := by
  have hL := log_two_pos
  obtain ⟨h1, h2⟩ := log_two_mem
  have hlo := LqLo_pos
  split_ifs with h0
  · push_cast
    have h0' : (0 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast h0
    calc (N0 : ℝ) / (LqHi : ℝ) ≤ (N0 : ℝ) / Real.log 2 := div_le_div_of_nonneg_left h0' hL h2
      _ ≤ N / Real.log 2 := div_le_div_of_nonneg_right h hL.le
  · push_cast
    have h0' : (N0 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h0)
    calc (N0 : ℝ) / (LqLo : ℝ) ≤ (N0 : ℝ) / Real.log 2 := by
          rw [div_le_div_iff₀ hlo hL]; nlinarith
      _ ≤ N / Real.log 2 := div_le_div_of_nonneg_right h hL.le

theorem divLq_hi {N1 : ℚ} {N : ℝ} (h : N ≤ (N1 : ℝ)) :
    N / Real.log 2 ≤ (((if 0 ≤ N1 then N1 / LqLo else N1 / LqHi : ℚ)) : ℝ) := by
  have hL := log_two_pos
  obtain ⟨h1, h2⟩ := log_two_mem
  have hlo := LqLo_pos
  have hhi := LqHi_pos
  split_ifs with h0
  · push_cast
    have h0' : (0 : ℝ) ≤ (N1 : ℝ) := by exact_mod_cast h0
    calc N / Real.log 2 ≤ (N1 : ℝ) / Real.log 2 := div_le_div_of_nonneg_right h hL.le
      _ ≤ (N1 : ℝ) / (LqLo : ℝ) := div_le_div_of_nonneg_left h0' hlo h1
  · push_cast
    have h0' : (N1 : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge h0)
    calc N / Real.log 2 ≤ (N1 : ℝ) / Real.log 2 := div_le_div_of_nonneg_right h hL.le
      _ ≤ (N1 : ℝ) / (LqHi : ℝ) := by
          rw [div_le_div_iff₀ hL hhi]; nlinarith

theorem J_bounds {v : ℚ} (h : ptOk v = true) :
    ((JloQ v : ℚ) : ℝ) ≤ J (v : ℝ) ∧ J (v : ℝ) ≤ ((JhiQ v : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := lam_bounds h
  have hJ : J (v : ℝ) = Real.log ((1 - (v : ℝ)) / (v : ℝ)) / Real.log 2 := rfl
  rw [hJ]
  exact ⟨divLq_lo h1, divLq_hi h2⟩

/-- Cast of a rational comparison `r ≤ 1/2`. -/
theorem cast_le_half {r : ℚ} (h : r ≤ 1 / 2) : ((r : ℚ) : ℝ) ≤ 1 / 2 := by
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  linarith

/-! ## The endpoint kernel -/

/-- `mhi = (1 - y₀E₀)/2 ≥ m`. -/
def epM (B : B3) : ℚ := (1 - B.c0 * B.a0) / 2
/-- `alo = (1 - min(4/5, x₁E₁ + min(2/5, y₁E₁)))/2 ≤ a`. -/
def epA (B : B3) : ℚ := (1 - min (4 / 5) (B.b1 * B.a1 + min (2 / 5) (B.c1 * B.a1))) / 2
/-- `blo = (1 - max(0, x₁E₁ - y₀E₀))/2 ≤ 1 - b`. -/
def epB (B : B3) : ℚ := (1 - max 0 (B.b1 * B.a1 - B.c0 * B.a0)) / 2

/-- Kernel acceptance test of the transition `endpoint` owner on an `(E, x, y)` box. -/
def checkEP (B : B3) (v1 v2 vc : ℚ) : Bool :=
  decide (0 < B.a0 ∧ B.a0 ≤ B.a1 ∧ 0 < B.b0 ∧ B.b0 ≤ B.b1 ∧ 0 ≤ B.c0 ∧ B.c0 ≤ B.c1) &&
  ptOk (epM B) && ptOk (epA B) && ptOk (epB B) &&
  decide (epM B ≤ 1 / 2 ∧ epA B ≤ 1 / 2 ∧ epB B ≤ 1 / 2) &&
  ptOk v1 && decide (v1 ≤ 1 / 2 ∧ Hhi v1 ≤ B.a0 + 1 - Hhi (epM B)) &&
  ptOk v2 && decide (v2 ≤ 1 / 2 ∧ B.a1 + 1 - (Hlo (epA B) + Hlo (epB B)) / 2 ≤ Hlo v2) &&
  ptOk vc && decide (vc ≤ 1 / 2 ∧ 1 - 2 * vc ≤ B.b0 * Hlo vc) &&
  decide ((1 - 2 * v1) * JhiQ v1 - (1 - 2 * v2) * JloQ v2 ≤ B.a0 * B.b0 * JloQ vc)

/-! ## Soundness -/

set_option maxHeartbeats 2000000 in
/-- Soundness of the `endpoint` leaf check (in-row form): every law in the exact leaf image with the
canonical opposite-side hypotheses and strict psi-activity satisfies `gap ≤ cost`. -/
theorem checkEP_sound {B : B3} {v1 v2 vc : ℚ} (h : checkEP B v1 v2 vc = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hsum : μ.a + μ.b ≤ 1) (ha : 1 / 10 ≤ μ.a)
    (hb : 1 / 2 ≤ μ.b) (hd : 0 < μ.b - μ.a)
    (hin : InExy B μ.a μ.b μ.meanEntropy) (hact : PsiActive μ) : μ.gap ≤ μ.cost := by
  simp only [checkEP, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbox, hptM⟩, hptA⟩, hptB⟩, hhalf⟩, hpt1⟩, hv1⟩, hpt2⟩, hv2⟩, hptc⟩, hvc⟩,
    hfin⟩ := h
  obtain ⟨ha0, -, hb0, -, hc0, -⟩ := hbox
  obtain ⟨hmh, hah, hbh⟩ := hhalf
  obtain ⟨hv1h, hv1H⟩ := hv1
  obtain ⟨hv2h, hv2H⟩ := hv2
  obtain ⟨hvch, hvcH⟩ := hvc
  obtain ⟨hE0, hE1, hx0, hx1, hy0, hy1⟩ := hin
  have haI := μ.a_interior
  have hbI := μ.b_interior
  have hEpos : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  set E := μ.meanEntropy with hE_def
  -- casts of box data
  have ha0R : (0 : ℝ) < (B.a0 : ℝ) := by exact_mod_cast ha0
  have hb0R : (0 : ℝ) < (B.b0 : ℝ) := by exact_mod_cast hb0
  have hc0R : (0 : ℝ) ≤ (B.c0 : ℝ) := by exact_mod_cast hc0
  -- coordinates
  set x := (μ.b - μ.a) / E with hx_def
  set y := (1 - μ.a - μ.b) / E with hy_def
  have hxE : x * E = μ.b - μ.a := by rw [hx_def]; field_simp
  have hyE : y * E = 1 - μ.a - μ.b := by rw [hy_def]; field_simp
  have hxnn : 0 ≤ x := hb0R.le.trans hx0
  have hynn : 0 ≤ y := hc0R.trans hy0
  have hq_lo : (B.c0 : ℝ) * (B.a0 : ℝ) ≤ 1 - μ.a - μ.b := by
    rw [← hyE]; exact mul_le_mul hy0 hE0 ha0R.le hynn
  have hd_hi : μ.b - μ.a ≤ (B.b1 : ℝ) * (B.a1 : ℝ) := by
    rw [← hxE]; exact mul_le_mul hx1 hE1 hEpos.le (hxnn.trans hx1)
  have hq_hi : 1 - μ.a - μ.b ≤ (B.c1 : ℝ) * (B.a1 : ℝ) := by
    rw [← hyE]; exact mul_le_mul hy1 hE1 hEpos.le (hynn.trans hy1)
  -- the three evaluation points
  have hMeq : ((epM B : ℚ) : ℝ) = (1 - (B.c0 : ℝ) * (B.a0 : ℝ)) / 2 := by
    simp only [epM]; push_cast; ring
  have hAeq : ((epA B : ℚ) : ℝ) =
      (1 - min (4 / 5 : ℝ) ((B.b1 : ℝ) * (B.a1 : ℝ) + min (2 / 5 : ℝ) ((B.c1 : ℝ) * (B.a1 : ℝ)))) / 2 := by
    simp only [epA]; push_cast; ring
  have hBeq : ((epB B : ℚ) : ℝ) =
      (1 - max (0 : ℝ) ((B.b1 : ℝ) * (B.a1 : ℝ) - (B.c0 : ℝ) * (B.a0 : ℝ))) / 2 := by
    simp only [epB]; push_cast; ring
  have hM0 : (0 : ℝ) < ((epM B : ℚ) : ℝ) := by exact_mod_cast (ptOk_pos hptM).1
  have hA0 : (0 : ℝ) < ((epA B : ℚ) : ℝ) := by exact_mod_cast (ptOk_pos hptA).1
  have hB0 : (0 : ℝ) < ((epB B : ℚ) : ℝ) := by exact_mod_cast (ptOk_pos hptB).1
  have hMh := cast_le_half hmh
  -- H(m) ≤ H⁺(mhi)
  have hmid : (μ.a + μ.b) / 2 ≤ ((epM B : ℚ) : ℝ) := by rw [hMeq]; linarith
  have hHm : H ((μ.a + μ.b) / 2) ≤ ((Hhi (epM B) : ℚ) : ℝ) :=
    (CKLaneD.H_mono_left (by linarith) hmid hMh).trans (H_bounds hptM).2
  -- H(a) ≥ H⁻(alo)
  have hq25 : 1 - μ.a - μ.b ≤ 2 / 5 := by linarith
  have hpa : 1 - 2 * μ.a ≤
      min (4 / 5 : ℝ) ((B.b1 : ℝ) * (B.a1 : ℝ) + min (2 / 5 : ℝ) ((B.c1 : ℝ) * (B.a1 : ℝ))) := by
    apply le_min
    · linarith
    · have := le_min hq25 hq_hi
      linarith
  have hAa : ((epA B : ℚ) : ℝ) ≤ μ.a := by rw [hAeq]; linarith
  have hHa : ((Hlo (epA B) : ℚ) : ℝ) ≤ H μ.a :=
    (H_bounds hptA).1.trans (CKLaneD.H_mono_left hA0.le hAa (by linarith))
  -- H(b) = H(1-b) ≥ H⁻(blo)
  have hpb : 2 * μ.b - 1 ≤ max (0 : ℝ) ((B.b1 : ℝ) * (B.a1 : ℝ) - (B.c0 : ℝ) * (B.a0 : ℝ)) :=
    le_max_of_le_right (by linarith)
  have hBb : ((epB B : ℚ) : ℝ) ≤ 1 - μ.b := by rw [hBeq]; linarith
  have hHb : ((Hlo (epB B) : ℚ) : ℝ) ≤ H μ.b := by
    rw [← H_complement μ.b]
    exact (H_bounds hptB).1.trans (CKLaneD.H_mono_left hB0.le hBb (by linarith))
  -- ψ-gap bound through the two brackets
  have hpsi := CKLaneD.law_gap_le_P μ
  have hdef := CKLaneD.law_deficit_mem μ
  have hdrop : (H μ.a + H μ.b) / 2 ≤ H ((μ.a + μ.b) / 2) := by
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at this
    linarith
  have hHm1 : H ((μ.a + μ.b) / 2) ≤ 1 := H_le_one _
  have hv1pos : (0 : ℝ) < (v1 : ℝ) := by exact_mod_cast (ptOk_pos hpt1).1
  have hv2pos : (0 : ℝ) < (v2 : ℝ) := by exact_mod_cast (ptOk_pos hpt2).1
  have hvcpos : (0 : ℝ) < (vc : ℝ) := by exact_mod_cast (ptOk_pos hptc).1
  have hv1h' := cast_le_half hv1h
  have hv2h' := cast_le_half hv2h
  have hvch' := cast_le_half hvch
  have hv1HR : ((Hhi v1 : ℚ) : ℝ) ≤ (B.a0 : ℝ) + 1 - ((Hhi (epM B) : ℚ) : ℝ) := by
    exact_mod_cast hv1H
  have hv2HR : (B.a1 : ℝ) + 1 - (((Hlo (epA B) : ℚ) : ℝ) + ((Hlo (epB B) : ℚ) : ℝ)) / 2 ≤
      ((Hlo v2 : ℚ) : ℝ) := by
    exact_mod_cast hv2H
  have hvcHR : 1 - 2 * (vc : ℝ) ≤ (B.b0 : ℝ) * ((Hlo vc : ℚ) : ℝ) := by
    exact_mod_cast hvcH
  have hP1 : Scalar.P (H ((μ.a + μ.b) / 2) - E) ≤ (1 - 2 * (v1 : ℝ)) * J (v1 : ℝ) := by
    apply CKLaneD.P_le_bracket (by linarith) (by linarith) hv1pos hv1h'
    have := (H_bounds hpt1).2
    linarith
  have hP2 : (1 - 2 * (v2 : ℝ)) * J (v2 : ℝ) ≤ Scalar.P ((H μ.a + H μ.b) / 2 - E) := by
    apply CKLaneD.P_ge_bracket hdef.1 hdef.2 hv2pos hv2h'
    have := (H_bounds hpt2).1
    linarith
  obtain ⟨-, hJ1⟩ := J_bounds hpt1
  obtain ⟨hJ2, -⟩ := J_bounds hpt2
  obtain ⟨hJc, -⟩ := J_bounds hptc
  have hJ1' : (1 - 2 * (v1 : ℝ)) * J (v1 : ℝ) ≤ (1 - 2 * (v1 : ℝ)) * ((JhiQ v1 : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hJ1 (by linarith)
  have hJ2' : (1 - 2 * (v2 : ℝ)) * ((JloQ v2 : ℚ) : ℝ) ≤ (1 - 2 * (v2 : ℝ)) * J (v2 : ℝ) :=
    mul_le_mul_of_nonneg_left hJ2 (by linarith)
  -- cost lower bound
  have hcost := PsiEndpointPlane.law_radial_lower μ (by linarith)
  have hpersp : F (μ.b - μ.a) E = E * F x 1 := F_perspective hEpos.ne' _
  have hFmono : F (B.b0 : ℝ) 1 ≤ F x 1 := F_mono_radius hb0R.le hx0 one_pos
  have hFnn : 0 ≤ F (B.b0 : ℝ) 1 := F_nonneg hb0R.le one_pos
  have hrc0 := radialContact_pos hb0R one_pos
  have hrc : radialContact (B.b0 : ℝ) 1 ≤ (vc : ℝ) := by
    rw [radialContact_le_iff hb0R one_pos hvcpos.le hvch']
    have := mul_le_mul_of_nonneg_left (H_bounds hptc).1 hb0R.le
    linarith
  have hJrc := J_antitone hrc0 hvch' hrc
  have hFb0 : F (B.b0 : ℝ) 1 = (B.b0 : ℝ) * J (radialContact (B.b0 : ℝ) 1) := by
    simp [F, hb0R.ne']
  have hFlow : (B.a0 : ℝ) * (B.b0 : ℝ) * ((JloQ vc : ℚ) : ℝ) ≤ F (μ.b - μ.a) E := by
    have h1 : (B.a0 : ℝ) * (B.b0 : ℝ) * ((JloQ vc : ℚ) : ℝ) ≤
        (B.a0 : ℝ) * (B.b0 : ℝ) * J (radialContact (B.b0 : ℝ) 1) :=
      mul_le_mul_of_nonneg_left (hJc.trans hJrc) (by positivity)
    have h2 : (B.a0 : ℝ) * F (B.b0 : ℝ) 1 ≤ E * F (B.b0 : ℝ) 1 :=
      mul_le_mul_of_nonneg_right hE0 hFnn
    have h3 : E * F (B.b0 : ℝ) 1 ≤ E * F x 1 := mul_le_mul_of_nonneg_left hFmono hEpos.le
    rw [hpersp]
    rw [hFb0] at h2 h3
    nlinarith
  have hfinR : (1 - 2 * (v1 : ℝ)) * ((JhiQ v1 : ℚ) : ℝ) - (1 - 2 * (v2 : ℝ)) * ((JloQ v2 : ℚ) : ℝ) ≤
      (B.a0 : ℝ) * (B.b0 : ℝ) * ((JloQ vc : ℚ) : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hfin
    push_cast at h'
    linarith
  have hgap : μ.gap ≤ candidateGap psi μ.a μ.b μ.e μ.f := hybrid_gap_le_psi hact.le
  linarith

end CKLaneN1c

end


