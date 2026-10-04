-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Check
-- name    : CK_CKLaneN4_LU_Check
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T12:47:30.877328+00:00
-- url     : https://prove2.me/theorems/51dfbc57-e160-4271-a397-9bd5de598e11
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Check` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Check` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Check` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Check (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Check.lean)

import Definitions.Def_CK_CKLaneN4_LU_Eval

-- ===== source module CKLaneN4.LU.Check =====
section
/-
Lane N4b — the Boolean cell checker for the left-upper value and its soundness.

Cell data (all natural numbers):
* box `[a0,a1] × [t0,t1]` at scale `2^64` in the `(a,t)` chart `b = a + t (1/2 - a)`;
* centre `(c1,c2)` at scale `2^128` (any interior point; tangent plane of `Cfun` there);
* contact witnesses `u1 ≥ radialContact r 1 ≥ u2` for `r = (1/2 - c1)/hAvg c1 c2`;
* per vertex: a contact lower witness `f` (bounds `F(b-a,h)` above) and an entropy witness `e`
  with `H e ≤ h` (bounds `eta h` above).
`cellCheck_sound`: `cellCheck cl = true → ∀ a t in the box, 0 < a → 0 ≤ Gexpr a (bAt a t)`.
No real-variable hypotheses and no stored margins: every inequality is recomputed by the checker.
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK GeneralCK.Certificates DyadicInterval

theorem half_cast : ((2 ^ (P - 1) : ℕ) : ℝ) = 2 ^ P / 2 := by
  push_cast
  rw [show P = (P - 1) + 1 by decide, pow_succ]
  field_simp
  norm_num

theorem lt_half_of_nat {N : ℕ} (h : N < 2 ^ (P - 1)) : (N : ℝ) / 2 ^ P < 1 / 2 := by
  have hp := two_pow_P_pos
  have : (N : ℝ) < ((2 ^ (P - 1) : ℕ) : ℝ) := by exact_mod_cast h
  rw [half_cast] at this
  rw [div_lt_iff₀ hp]; linarith

theorem le_half_of_nat {N : ℕ} (h : N ≤ 2 ^ (P - 1)) : (N : ℝ) / 2 ^ P ≤ 1 / 2 := by
  have hp := two_pow_P_pos
  have : (N : ℝ) ≤ ((2 ^ (P - 1) : ℕ) : ℝ) := by exact_mod_cast h
  rw [half_cast] at this
  rw [div_le_iff₀ hp]; linarith

theorem lt_P_of_le_half {N : ℕ} (h : N ≤ 2 ^ (P - 1)) : N < 2 ^ P := by
  have : 2 ^ (P - 1) < 2 ^ P := by decide
  omega

theorem pos_of_nat {N : ℕ} (h : 1 ≤ N) : (0 : ℝ) < (N : ℝ) / 2 ^ P := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast h
  have hp := two_pow_P_pos
  positivity

theorem one_sub_two_cast {N : ℕ} (h : N ≤ 2 ^ (P - 1)) :
    (((2 ^ P - 2 * N : ℕ) : ℤ) : ℝ) = 2 ^ P * (1 - 2 * ((N : ℝ) / 2 ^ P)) := by
  have hp := two_pow_P_pos
  have hle : 2 * N ≤ 2 ^ P := by
    have : 2 * 2 ^ (P - 1) = 2 ^ P := by decide
    omega
  rw [Int.cast_natCast, Nat.cast_sub hle]
  push_cast
  field_simp

theorem pos_of_scaled {x : ℝ} {z : ℤ} (hz : 0 < z) (h : (z : ℝ) ≤ 2 ^ P * x) : 0 < x := by
  have hp := two_pow_P_pos
  have : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  by_contra hc
  push Not at hc
  nlinarith

theorem nonneg_of_scaled {x : ℝ} (h : 0 ≤ 2 ^ P * x) : 0 ≤ x := by
  have hp := two_pow_P_pos
  by_contra hc
  push Not at hc
  nlinarith

/-! ### Real-level steps (small contexts) -/

theorem fw_step {z hv v Hv HHhi lo S : ℝ} (hS : 0 < S) (hz : 0 < z) (h1v : 0 ≤ 1 - 2 * v)
    (hHv : S * Hv ≤ HHhi) (hlo : lo ≤ S * hv) (hc : S * z * HHhi ≤ lo * (S * (1 - 2 * v))) :
    z * Hv ≤ hv * (1 - 2 * v) := by
  have e1 : S * z * (S * Hv) ≤ S * z * HHhi := mul_le_mul_of_nonneg_left hHv (by positivity)
  have e2 : lo * (S * (1 - 2 * v)) ≤ (S * hv) * (S * (1 - 2 * v)) :=
    mul_le_mul_of_nonneg_right hlo (by positivity)
  have e3 : (S * S) * (z * Hv) ≤ (S * S) * (hv * (1 - 2 * v)) := by nlinarith
  exact le_of_mul_le_mul_left e3 (by positivity)

theorem cu_step {r H1 v rlo Hlo S : ℝ} (hS : 0 < S) (hrlo : rlo ≤ S * r) (hHlo : Hlo ≤ S * H1)
    (hHl0 : 0 ≤ Hlo) (hrl0 : 0 ≤ rlo) (hc : S * (1 - 2 * v) * S ≤ rlo * Hlo) :
    1 * (1 - 2 * v) ≤ r * H1 := by
  have e1 : rlo * Hlo ≤ (S * r) * Hlo := mul_le_mul_of_nonneg_right hrlo hHl0
  have e2 : (S * r) * Hlo ≤ (S * r) * (S * H1) :=
    mul_le_mul_of_nonneg_left hHlo (le_trans hrl0 hrlo)
  have e3 : (S * S) * (1 * (1 - 2 * v)) ≤ (S * S) * (r * H1) := by nlinarith
  exact le_of_mul_le_mul_left e3 (by positivity)

theorem cl_step {r H2 v rhi Hhi S : ℝ} (hS : 0 < S) (hrhi : S * r ≤ rhi) (hHhi : S * H2 ≤ Hhi)
    (hr : 0 ≤ r) (hH : 0 ≤ H2) (hc : rhi * Hhi ≤ S * (1 - 2 * v) * S) :
    r * H2 ≤ 1 * (1 - 2 * v) := by
  have e1 : (S * r) * (S * H2) ≤ rhi * (S * H2) := mul_le_mul_of_nonneg_right hrhi (by positivity)
  have e2 : rhi * (S * H2) ≤ rhi * Hhi :=
    mul_le_mul_of_nonneg_left hHhi (le_trans (by positivity) hrhi)
  have e3 : (S * S) * (r * H2) ≤ (S * S) * (1 * (1 - 2 * v)) := by nlinarith
  exact le_of_mul_le_mul_left e3 (by positivity)

/-! ### H at vertex coordinates (the coordinate may be `0`) -/

def HatN (N : ℕ) : DI := if N = 0 then ⟨0, 0⟩ else (mkPt N).HH

theorem HatN_contains {N : ℕ} (h2 : N < 2 ^ P) : (HatN N).Contains (H ((N : ℝ) / 2 ^ P)) := by
  unfold HatN
  split_ifs with h0
  · subst h0
    rw [contains_iff]
    simp [H_zero]
  · exact PtI.HH_contains (mkPt_sem (Nat.one_le_iff_ne_zero.2 h0) h2)

/-! ### Vertex: lower bound of the concave part -/

def vtxH (A B : ℕ) : DI := ((HatN A).add (HatN B)).mul halfI

def vtxOk (A B fw ew : ℕ) : Bool :=
  decide (A < 2 ^ (P - 1)) && decide (A ≤ B) && decide (B ≤ 2 ^ (P - 1)) && decide (1 ≤ B) &&
  decide (0 < (vtxH A B).lo) && decide (1 ≤ fw) && decide (fw ≤ 2 ^ (P - 1)) &&
  decide (((B - A : ℕ) : ℤ) * (mkPt fw).HH.hi ≤ (vtxH A B).lo * ((2 ^ P - 2 * fw : ℕ) : ℤ)) &&
  decide (1 ≤ ew) && decide (ew ≤ 2 ^ (P - 1)) && decide ((mkPt ew).HH.hi ≤ (vtxH A B).lo)

def vtxLo (A B fw ew : ℕ) : ℤ :=
  -((pt ((B - A : ℕ) : ℤ)).mul (mkPt fw).JJ).hi -
    (((cst 1).sub ((cst 2).mul (mkPt ew).v)).mul (mkPt ew).JJ).hi

set_option maxHeartbeats 1000000 in
theorem vtx_sound {A B fw ew : ℕ} (h : vtxOk A B fw ew = true) :
    VDom ((A : ℝ) / 2 ^ P) ((B : ℝ) / 2 ^ P) ∧
      (vtxLo A B fw ew : ℝ) ≤ 2 ^ P * Vfun ((A : ℝ) / 2 ^ P) ((B : ℝ) / 2 ^ P) := by
  simp only [vtxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA, hAB⟩, hB⟩, hB1⟩, hh⟩, hf1⟩, hf2⟩, hfc⟩, he1⟩, he2⟩, hec⟩ := h
  have hp : (0 : ℝ) < 2 ^ P := two_pow_P_pos
  have hAP : A < 2 ^ P := lt_P_of_le_half hA.le
  have hBP : B < 2 ^ P := lt_P_of_le_half hB
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (A : ℝ) / 2 ^ P := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (B : ℝ) / 2 ^ P := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hah : a < 1 / 2 := by rw [ha]; exact lt_half_of_nat hA
  have hab : a ≤ b := by
    rw [ha, hb]; exact div_le_div_of_nonneg_right (by exact_mod_cast hAB) hp.le
  have hbh : b ≤ 1 / 2 := by rw [hb]; exact le_half_of_nat hB
  have hb0 : 0 < b := by rw [hb]; exact pos_of_nat hB1
  refine ⟨⟨ha0, hab, hbh, hah, hb0⟩, ?_⟩
  have hHI : (vtxH A B).Contains (hAvg a b) := by
    have h1 := mul_sound (add_sound (HatN_contains hAP) (HatN_contains hBP)) halfI_contains
    rw [← ha, ← hb] at h1
    unfold vtxH
    have e : hAvg a b = (H a + H b) * (1 / 2) := by unfold hAvg; ring
    rw [e]; exact h1
  unfold Vfun
  obtain ⟨hv, hhv⟩ : ∃ hv : ℝ, hv = hAvg a b := ⟨_, rfl⟩
  rw [← hhv] at hHI ⊢
  have hlo : ((vtxH A B).lo : ℝ) ≤ 2 ^ P * hv := lo_le hHI
  have hpos : 0 < hv := pos_of_scaled hh hlo
  have hle1 : hv ≤ 1 := by rw [hhv]; exact hAvg_le_one a b
  -- F witness
  obtain ⟨v, hv'⟩ : ∃ v : ℝ, v = (fw : ℝ) / 2 ^ P := ⟨_, rfl⟩
  have hfP : fw < 2 ^ P := lt_P_of_le_half hf2
  have qfS : (mkPt fw).Sem v := by rw [hv']; exact mkPt_sem hf1 hfP
  have hv0 : 0 < v := by rw [hv']; exact pos_of_nat hf1
  have hvh : v ≤ 1 / 2 := by rw [hv']; exact le_half_of_nat hf2
  have hHv : 2 ^ P * H v ≤ ((mkPt fw).HH.hi : ℝ) := le_hi (PtI.HH_contains qfS)
  have hJv : (mkPt fw).JJ.Contains (J v) := PtI.JJ_contains qfS hv0 (by linarith)
  have hzC : (pt ((B - A : ℕ) : ℤ)).Contains (b - a) := by
    have := pt_contains ((B - A : ℕ) : ℤ)
    rw [Int.cast_natCast, Nat.cast_sub (R := ℝ) hAB, sub_div, ← ha, ← hb] at this
    exact this
  have hFup : 2 ^ P * ((b - a) * J v) ≤ (((pt ((B - A : ℕ) : ℤ)).mul (mkPt fw).JJ).hi : ℝ) :=
    le_hi (mul_sound hzC hJv)
  have hF : 2 ^ P * F (b - a) hv ≤ (((pt ((B - A : ℕ) : ℤ)).mul (mkPt fw).JJ).hi : ℝ) := by
    rcases eq_or_lt_of_le (sub_nonneg.2 hab) with hz0 | hzpos
    · have hF0 : F (b - a) hv = 0 := by rw [← hz0]; simp [F]
      have hzero : 2 ^ P * ((b - a) * J v) = 0 := by rw [← hz0]; ring
      rw [hF0, mul_zero]
      linarith
    · have hcont : v ≤ radialContact (b - a) hv := by
        rw [le_radialContact_iff hzpos hpos hv0.le hvh]
        have hc : (((B - A : ℕ) : ℤ) : ℝ) * ((mkPt fw).HH.hi : ℝ) ≤
            ((vtxH A B).lo : ℝ) * (((2 ^ P - 2 * fw : ℕ) : ℤ) : ℝ) := by exact_mod_cast hfc
        have hz' : (((B - A : ℕ) : ℤ) : ℝ) = 2 ^ P * (b - a) := by
          rw [Int.cast_natCast, Nat.cast_sub (R := ℝ) hAB, ha, hb]; field_simp
        have hw' : (((2 ^ P - 2 * fw : ℕ) : ℤ) : ℝ) = 2 ^ P * (1 - 2 * v) := by
          rw [one_sub_two_cast hf2, hv']
        rw [hz', hw'] at hc
        exact fw_step hp hzpos (by linarith) hHv hlo hc
      have hclt := radialContact_lt_half hzpos hpos
      have hJ := J_antitone hv0 hclt.le hcont
      have hFe : F (b - a) hv = (b - a) * J (radialContact (b - a) hv) := by
        simp [F, hzpos.ne']
      rw [hFe]
      have h1 : (b - a) * J (radialContact (b - a) hv) ≤ (b - a) * J v :=
        mul_le_mul_of_nonneg_left hJ hzpos.le
      have h2 : 2 ^ P * ((b - a) * J (radialContact (b - a) hv)) ≤ 2 ^ P * ((b - a) * J v) :=
        mul_le_mul_of_nonneg_left h1 hp.le
      linarith
  -- eta witness
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (ew : ℝ) / 2 ^ P := ⟨_, rfl⟩
  have heP : ew < 2 ^ P := lt_P_of_le_half he2
  have qeS : (mkPt ew).Sem w := by rw [hw]; exact mkPt_sem he1 heP
  have hw0 : 0 < w := by rw [hw]; exact pos_of_nat he1
  have hwh : w ≤ 1 / 2 := by rw [hw]; exact le_half_of_nat he2
  have hHw : 2 ^ P * H w ≤ ((mkPt ew).HH.hi : ℝ) := le_hi (PtI.HH_contains qeS)
  have hHwh : H w ≤ hv := by
    have h1 : ((mkPt ew).HH.hi : ℝ) ≤ ((vtxH A B).lo : ℝ) := by exact_mod_cast hec
    have h2 : 2 ^ P * H w ≤ 2 ^ P * hv := by linarith
    exact le_of_mul_le_mul_left h2 hp
  have hHw0 : 0 < H w := H_pos hw0 (by linarith)
  have heta : eta hv ≤ (1 - 2 * w) * J w := by
    have h1 := eta_antitoneOn ⟨hHw0, H_le_one w⟩ ⟨hpos, hle1⟩ hHwh
    rw [eta_eq_profile hHw0.le (H_le_one w), entropyInverse_H_lower hw0.le hwh] at h1
    exact h1
  have hJw : (mkPt ew).JJ.Contains (J w) := PtI.JJ_contains qeS hw0 (by linarith)
  have hvC : (mkPt ew).v.Contains w := qeS.1
  have hOmC : ((cst 1).sub ((cst 2).mul (mkPt ew).v)).Contains (1 - 2 * w) := by
    have := sub_sound (cst_contains 1) (mul_sound (cst_contains 2) hvC)
    push_cast at this; exact this
  have hEup : 2 ^ P * ((1 - 2 * w) * J w) ≤
      ((((cst 1).sub ((cst 2).mul (mkPt ew).v)).mul (mkPt ew).JJ).hi : ℝ) :=
    le_hi (mul_sound hOmC hJw)
  have hE : 2 ^ P * eta hv ≤ ((((cst 1).sub ((cst 2).mul (mkPt ew).v)).mul (mkPt ew).JJ).hi : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left heta hp.le) hEup
  unfold vtxLo
  push_cast
  have e : 2 ^ P * (-F (b - a) hv - eta hv) = -(2 ^ P * F (b - a) hv) - 2 ^ P * eta hv := by ring
  rw [e]
  linarith

/-! ### Centre: enclosures of `Cfun`, `gA`, `gB` -/

def cHc (c1 c2 : ℕ) : DI := ((mkPt c1).HH.add (mkPt c2).HH).mul halfI
def cR (c1 c2 : ℕ) : DI := (pt ((2 ^ (P - 1) - c1 : ℕ) : ℤ)).mul (cHc c1 c2).recip
def cPhi (c1 c2 u1 u2 : ℕ) : DI :=
  ⟨((cR c1 c2).mul (mkPt u1).JJ).lo, ((cR c1 c2).mul (mkPt u2).JJ).hi⟩
def cPhiD (u1 u2 : ℕ) : DI := ⟨(mkPt u1).RS.lo, (mkPt u2).RS.hi⟩
def cD (c1 c2 u1 u2 : ℕ) : DI := (cPhi c1 c2 u1 u2).sub ((cR c1 c2).mul (cPhiD u1 u2))
def cC21 (c1 c2 : ℕ) : DI := pt ((c2 - c1 : ℕ) : ℤ)
def cOm (c2 : ℕ) : DI := (cst 1).sub ((cst 2).mul (mkPt c2).v)

def cC (c1 c2 u1 u2 : ℕ) : DI :=
  ((((cC21 c1 c2).mul ((mkPt c1).JJ.sub (mkPt c2).JJ)).mul halfI).add
    ((cst 2).mul ((cHc c1 c2).mul (cPhi c1 c2 u1 u2)))).add (((cOm c2).mul (mkPt c2).JJ).mul halfI)

def cGA (c1 c2 u1 u2 : ℕ) : DI :=
  (((((mkPt c1).JJ.sub (mkPt c2).JJ).neg).add ((cC21 c1 c2).mul (mkPt c1).Jd)).mul halfI).add
    ((cst 2).mul ((cPhiD u1 u2).neg.add (((mkPt c1).JJ.mul halfI).mul (cD c1 c2 u1 u2))))

def cGB (c1 c2 u1 u2 : ℕ) : DI :=
  (((((mkPt c1).JJ.sub (mkPt c2).JJ).sub ((cC21 c1 c2).mul (mkPt c2).Jd)).mul halfI).add
    ((cst 2).mul (((mkPt c2).JJ.mul halfI).mul (cD c1 c2 u1 u2)))).add
    ((((cst 2).mul (mkPt c2).JJ).neg.add ((cOm c2).mul (mkPt c2).Jd)).mul halfI)

def cOk (c1 c2 u1 u2 : ℕ) : Bool :=
  decide (1 ≤ c1) && decide (c1 < c2) && decide (c2 < 2 ^ (P - 1)) &&
  decide (0 < (cHc c1 c2).lo) && decide (0 < (cR c1 c2).lo) &&
  decide (1 ≤ u1) && decide (u1 < 2 ^ (P - 1)) && decide (1 ≤ u2) && decide (u2 < 2 ^ (P - 1)) &&
  decide (((2 ^ P - 2 * u1 : ℕ) : ℤ) * 2 ^ P ≤ (cR c1 c2).lo * (mkPt u1).HH.lo) &&
  decide (0 ≤ (mkPt u1).HH.lo) &&
  decide ((cR c1 c2).hi * (mkPt u2).HH.hi ≤ ((2 ^ P - 2 * u2 : ℕ) : ℤ) * 2 ^ P) &&
  decide (0 < (mkPt u1).rsDen.lo) && decide (0 < (mkPt u2).rsDen.lo) &&
  decide (0 < (mkPt c1).jdDen.lo) && decide (0 < (mkPt c2).jdDen.lo)

set_option maxHeartbeats 2000000 in
theorem ctr_sound {c1 c2 u1 u2 : ℕ} (h : cOk c1 c2 u1 u2 = true) :
    0 < (c1 : ℝ) / 2 ^ P ∧ (c1 : ℝ) / 2 ^ P < (c2 : ℝ) / 2 ^ P ∧ (c2 : ℝ) / 2 ^ P < 1 / 2 ∧
      (cC c1 c2 u1 u2).Contains (Cfun ((c1 : ℝ) / 2 ^ P) ((c2 : ℝ) / 2 ^ P)) ∧
      (cGA c1 c2 u1 u2).Contains (gA ((c1 : ℝ) / 2 ^ P) ((c2 : ℝ) / 2 ^ P)) ∧
      (cGB c1 c2 u1 u2).Contains (gB ((c1 : ℝ) / 2 ^ P) ((c2 : ℝ) / 2 ^ P)) := by
  simp only [cOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc1, hc12⟩, hc2⟩, hhc⟩, hr⟩, hu11⟩, hu12⟩, hu21⟩, hu22⟩, hb1⟩, hb1'⟩, hb2⟩,
    hrs1⟩, hrs2⟩, hjd1⟩, hjd2⟩ := h
  have hp : (0 : ℝ) < 2 ^ P := two_pow_P_pos
  have hc2P : c2 < 2 ^ P := lt_P_of_le_half hc2.le
  have hc1P : c1 < 2 ^ P := by omega
  obtain ⟨x1, hx1⟩ : ∃ x : ℝ, x = (c1 : ℝ) / 2 ^ P := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ x : ℝ, x = (c2 : ℝ) / 2 ^ P := ⟨_, rfl⟩
  rw [← hx1, ← hx2]
  have hx1p : 0 < x1 := by rw [hx1]; exact pos_of_nat hc1
  have hx12 : x1 < x2 := by
    rw [hx1, hx2]; exact div_lt_div_of_pos_right (by exact_mod_cast hc12) hp
  have hx2h : x2 < 1 / 2 := by rw [hx2]; exact lt_half_of_nat hc2
  refine ⟨hx1p, hx12, hx2h, ?_⟩
  have hx2p : 0 < x2 := hx1p.trans hx12
  have p1S : (mkPt c1).Sem x1 := by rw [hx1]; exact mkPt_sem hc1 hc1P
  have p2S : (mkPt c2).Sem x2 := by rw [hx2]; exact mkPt_sem (by omega) hc2P
  have hJ1 : (mkPt c1).JJ.Contains (J x1) := PtI.JJ_contains p1S hx1p (by linarith)
  have hJ2 : (mkPt c2).JJ.Contains (J x2) := PtI.JJ_contains p2S hx2p (by linarith)
  -- average entropy and r
  have hHc : (cHc c1 c2).Contains (hAvg x1 x2) := by
    have := mul_sound (add_sound (PtI.HH_contains p1S) (PtI.HH_contains p2S)) halfI_contains
    unfold cHc
    have e : hAvg x1 x2 = (H x1 + H x2) * (1 / 2) := by unfold hAvg; ring
    rw [e]; exact this
  have hhpos : 0 < hAvg x1 x2 := pos_of_lo hHc hhc
  have hzC : (pt ((2 ^ (P - 1) - c1 : ℕ) : ℤ)).Contains (1 / 2 - x1) := by
    have := pt_contains ((2 ^ (P - 1) - c1 : ℕ) : ℤ)
    have e : (((2 ^ (P - 1) - c1 : ℕ) : ℤ) : ℝ) / 2 ^ P = 1 / 2 - x1 := by
      rw [Int.cast_natCast, Nat.cast_sub (R := ℝ) (by omega), sub_div, half_cast, hx1]
      field_simp
    rwa [e] at this
  have hR : (cR c1 c2).Contains (rc x1 x2) := by
    have := mul_sound hzC (recip_sound hhc hHc)
    unfold cR rc
    rw [div_eq_mul_inv]; exact this
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = rc x1 x2 := ⟨_, rfl⟩
  rw [← hrdef] at hR
  have hrpos : 0 < r := pos_of_lo hR hr
  have hrlo : ((cR c1 c2).lo : ℝ) ≤ 2 ^ P * r := lo_le hR
  have hrhi : 2 ^ P * r ≤ ((cR c1 c2).hi : ℝ) := le_hi hR
  -- contact bracket
  obtain ⟨v1, hv1⟩ : ∃ v : ℝ, v = (u1 : ℝ) / 2 ^ P := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v : ℝ, v = (u2 : ℝ) / 2 ^ P := ⟨_, rfl⟩
  have hu1P : u1 < 2 ^ P := lt_P_of_le_half hu12.le
  have hu2P : u2 < 2 ^ P := lt_P_of_le_half hu22.le
  have q1S : (mkPt u1).Sem v1 := by rw [hv1]; exact mkPt_sem hu11 hu1P
  have q2S : (mkPt u2).Sem v2 := by rw [hv2]; exact mkPt_sem hu21 hu2P
  have hv1p : 0 < v1 := by rw [hv1]; exact pos_of_nat hu11
  have hv1h : v1 < 1 / 2 := by rw [hv1]; exact lt_half_of_nat hu12
  have hv2p : 0 < v2 := by rw [hv2]; exact pos_of_nat hu21
  have hv2h : v2 < 1 / 2 := by rw [hv2]; exact lt_half_of_nat hu22
  have hH1lo : ((mkPt u1).HH.lo : ℝ) ≤ 2 ^ P * H v1 := lo_le (PtI.HH_contains q1S)
  have hH2hi : 2 ^ P * H v2 ≤ ((mkPt u2).HH.hi : ℝ) := le_hi (PtI.HH_contains q2S)
  have hcu : radialContact r 1 ≤ v1 := by
    rw [radialContact_le_iff hrpos one_pos hv1p.le hv1h.le]
    have hc : (((2 ^ P - 2 * u1 : ℕ) : ℤ) : ℝ) * 2 ^ P ≤
        ((cR c1 c2).lo : ℝ) * ((mkPt u1).HH.lo : ℝ) := by exact_mod_cast hb1
    rw [one_sub_two_cast hu12.le, ← hv1] at hc
    have hHl0 : (0 : ℝ) ≤ ((mkPt u1).HH.lo : ℝ) := by exact_mod_cast hb1'
    have hrl0 : (0 : ℝ) ≤ ((cR c1 c2).lo : ℝ) := by exact_mod_cast hr.le
    exact cu_step hp hrlo hH1lo hHl0 hrl0 hc
  have hcl : v2 ≤ radialContact r 1 := by
    rw [le_radialContact_iff hrpos one_pos hv2p.le hv2h.le]
    have hc : ((cR c1 c2).hi : ℝ) * ((mkPt u2).HH.hi : ℝ) ≤
        (((2 ^ P - 2 * u2 : ℕ) : ℤ) : ℝ) * 2 ^ P := by exact_mod_cast hb2
    rw [one_sub_two_cast hu22.le, ← hv2] at hc
    exact cl_step hp hrhi hH2hi hrpos.le (H_nonneg hv2p.le (by linarith)) hc
  have hcpos : 0 < radialContact r 1 := radialContact_pos hrpos one_pos
  have hclt : radialContact r 1 < 1 / 2 := radialContact_lt_half hrpos one_pos
  -- Phi
  have hJq1 : (mkPt u1).JJ.Contains (J v1) := PtI.JJ_contains q1S hv1p (by linarith)
  have hJq2 : (mkPt u2).JJ.Contains (J v2) := PtI.JJ_contains q2S hv2p (by linarith)
  have hPhi : (cPhi c1 c2 u1 u2).Contains (Phi r) := by
    have hJa : J v1 ≤ J (radialContact r 1) := J_antitone hcpos hv1h.le hcu
    have hJb : J (radialContact r 1) ≤ J v2 := J_antitone hv2p hclt.le hcl
    have hPe : Phi r = r * J (radialContact r 1) := by simp [Phi, F, hrpos.ne']
    have m1 : (((cR c1 c2).mul (mkPt u1).JJ).lo : ℝ) ≤ 2 ^ P * (r * J v1) :=
      lo_le (mul_sound hR hJq1)
    have m2 : 2 ^ P * (r * J v2) ≤ (((cR c1 c2).mul (mkPt u2).JJ).hi : ℝ) :=
      le_hi (mul_sound hR hJq2)
    have k1 : 2 ^ P * (r * J v1) ≤ 2 ^ P * (r * J (radialContact r 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJa hrpos.le) hp.le
    have k2 : 2 ^ P * (r * J (radialContact r 1)) ≤ 2 ^ P * (r * J v2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJb hrpos.le) hp.le
    rw [contains_iff, hPe]
    exact ⟨le_trans m1 k1, le_trans k2 m2⟩
  -- PhiD
  have hRS1 : (mkPt u1).RS.Contains (radialSlope v1) := PtI.RS_contains q1S hv1p (by linarith) hrs1
  have hRS2 : (mkPt u2).RS.Contains (radialSlope v2) := PtI.RS_contains q2S hv2p (by linarith) hrs2
  have hPhiD : (cPhiD u1 u2).Contains (PhiD r) := by
    have hPe : PhiD r = radialSlope (radialContact r 1) := deriv_F_radius_slope hrpos one_pos
    have hmem : radialContact r 1 ∈ Set.Ioo (0 : ℝ) (1 / 2) := ⟨hcpos, hclt⟩
    have hA := ZeroCapLeftStationaryThetaBracket.radialSlope_antitone hmem ⟨hv1p, hv1h⟩ hcu
    have hB := ZeroCapLeftStationaryThetaBracket.radialSlope_antitone ⟨hv2p, hv2h⟩ hmem hcl
    have m1 : ((mkPt u1).RS.lo : ℝ) ≤ 2 ^ P * radialSlope v1 := lo_le hRS1
    have m2 : 2 ^ P * radialSlope v2 ≤ ((mkPt u2).RS.hi : ℝ) := le_hi hRS2
    rw [contains_iff, hPe]
    exact ⟨le_trans m1 (mul_le_mul_of_nonneg_left hA hp.le),
      le_trans (mul_le_mul_of_nonneg_left hB hp.le) m2⟩
  have hD : (cD c1 c2 u1 u2).Contains (Phi r - r * PhiD r) := sub_sound hPhi (mul_sound hR hPhiD)
  -- remaining pieces
  have hC21 : (cC21 c1 c2).Contains (x2 - x1) := by
    have := pt_contains ((c2 - c1 : ℕ) : ℤ)
    rwa [Int.cast_natCast, Nat.cast_sub (R := ℝ) hc12.le, sub_div, ← hx1, ← hx2] at this
  have hOm : (cOm c2).Contains (1 - 2 * x2) := by
    have := sub_sound (cst_contains 1) (mul_sound (cst_contains 2) p2S.1)
    unfold cOm; push_cast at this; exact this
  have hJd1 : (mkPt c1).Jd.Contains (Jd x1) := PtI.Jd_contains p1S hjd1
  have hJd2 : (mkPt c2).Jd.Contains (Jd x2) := PtI.Jd_contains p2S hjd2
  have hFc : F (1 / 2 - x1) (hAvg x1 x2) = hAvg x1 x2 * Phi r := by
    rw [F_perspective hhpos.ne' (1 / 2 - x1), hrdef]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have h1 := add_sound (add_sound (mul_sound (mul_sound hC21 (sub_sound hJ1 hJ2)) halfI_contains)
      (mul_sound (cst_contains 2) (mul_sound hHc hPhi))) (mul_sound (mul_sound hOm hJ2) halfI_contains)
    unfold cC
    have e : Cfun x1 x2 = (x2 - x1) * (J x1 - J x2) * (1 / 2) +
        ((2 : ℤ) : ℝ) * (hAvg x1 x2 * Phi r) + (1 - 2 * x2) * J x2 * (1 / 2) := by
      unfold Cfun interiorCost kfun
      rw [hFc]; push_cast; ring
    rw [e]; exact h1
  · have h1 := add_sound (mul_sound (add_sound (neg_sound (sub_sound hJ1 hJ2)) (mul_sound hC21 hJd1))
      halfI_contains) (mul_sound (cst_contains 2) (add_sound (neg_sound hPhiD)
        (mul_sound (mul_sound hJ1 halfI_contains) hD)))
    unfold cGA
    have e : gA x1 x2 = (-(J x1 - J x2) + (x2 - x1) * Jd x1) * (1 / 2) +
        ((2 : ℤ) : ℝ) * (-PhiD r + J x1 * (1 / 2) * (Phi r - r * PhiD r)) := by
      unfold gA; rw [← hrdef]; push_cast; ring
    rw [e]; exact h1
  · have h1 := add_sound (add_sound (mul_sound (sub_sound (sub_sound hJ1 hJ2) (mul_sound hC21 hJd2))
      halfI_contains) (mul_sound (cst_contains 2) (mul_sound (mul_sound hJ2 halfI_contains) hD)))
      (mul_sound (add_sound (neg_sound (mul_sound (cst_contains 2) hJ2)) (mul_sound hOm hJd2))
        halfI_contains)
    unfold cGB
    have e : gB x1 x2 = ((J x1 - J x2) - (x2 - x1) * Jd x2) * (1 / 2) +
        ((2 : ℤ) : ℝ) * (J x2 * (1 / 2) * (Phi r - r * PhiD r)) +
        (-(((2 : ℤ) : ℝ) * J x2) + (1 - 2 * x2) * Jd x2) * (1 / 2) := by
      unfold gB; rw [← hrdef]; push_cast; ring
    rw [e]; exact h1

/-! ### The cell -/

structure Cell where
  a0 : ℕ
  a1 : ℕ
  t0 : ℕ
  t1 : ℕ
  c1 : ℕ
  c2 : ℕ
  u1 : ℕ
  u2 : ℕ
  f00 : ℕ
  f10 : ℕ
  f01 : ℕ
  f11 : ℕ
  e00 : ℕ
  e10 : ℕ
  e01 : ℕ
  e11 : ℕ
  deriving Repr

def aN (a : ℕ) : ℕ := a * 2 ^ 64
def bN (a t : ℕ) : ℕ := a * 2 ^ 64 + t * (2 ^ 63 - a)

def wLo (C gA gB : DI) (c1 c2 A B fw ew : ℕ) : ℤ :=
  C.lo + (gA.mul (pt ((A : ℤ) - c1))).lo + (gB.mul (pt ((B : ℤ) - c2))).lo + vtxLo A B fw ew

def vtxCheck (C gA gB : DI) (c1 c2 A B fw ew : ℕ) : Bool :=
  vtxOk A B fw ew && decide (0 ≤ wLo C gA gB c1 c2 A B fw ew)

def cellCheck (cl : Cell) : Bool :=
  cOk cl.c1 cl.c2 cl.u1 cl.u2 && decide (cl.a0 < cl.a1) && decide (cl.t0 < cl.t1) &&
  decide (cl.t1 ≤ 2 ^ 64) && decide (cl.a1 < 2 ^ 63) &&
  vtxCheck (cC cl.c1 cl.c2 cl.u1 cl.u2) (cGA cl.c1 cl.c2 cl.u1 cl.u2) (cGB cl.c1 cl.c2 cl.u1 cl.u2)
    cl.c1 cl.c2 (aN cl.a0) (bN cl.a0 cl.t0) cl.f00 cl.e00 &&
  vtxCheck (cC cl.c1 cl.c2 cl.u1 cl.u2) (cGA cl.c1 cl.c2 cl.u1 cl.u2) (cGB cl.c1 cl.c2 cl.u1 cl.u2)
    cl.c1 cl.c2 (aN cl.a1) (bN cl.a1 cl.t0) cl.f10 cl.e10 &&
  vtxCheck (cC cl.c1 cl.c2 cl.u1 cl.u2) (cGA cl.c1 cl.c2 cl.u1 cl.u2) (cGB cl.c1 cl.c2 cl.u1 cl.u2)
    cl.c1 cl.c2 (aN cl.a0) (bN cl.a0 cl.t1) cl.f01 cl.e01 &&
  vtxCheck (cC cl.c1 cl.c2 cl.u1 cl.u2) (cGA cl.c1 cl.c2 cl.u1 cl.u2) (cGB cl.c1 cl.c2 cl.u1 cl.u2)
    cl.c1 cl.c2 (aN cl.a1) (bN cl.a1 cl.t1) cl.f11 cl.e11

theorem aN_cast (a : ℕ) : ((aN a : ℕ) : ℝ) / 2 ^ P = (a : ℝ) / 2 ^ 64 := by
  simp only [aN, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ℝ) ^ P = 2 ^ 64 * 2 ^ 64 by norm_num]
  field_simp

theorem bN_cast {a t : ℕ} (ha : a ≤ 2 ^ 63) :
    ((bN a t : ℕ) : ℝ) / 2 ^ P = bAt ((a : ℝ) / 2 ^ 64) ((t : ℝ) / 2 ^ 64) := by
  simp only [bN, bAt, Nat.cast_add, Nat.cast_mul, Nat.cast_sub ha, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ℝ) ^ P = 2 ^ 64 * 2 ^ 64 by norm_num]
  field_simp

theorem vtxCheck_sound {C gA' gB' : DI} {c1 c2 A B fw ew : ℕ} {x1 x2 : ℝ}
    (hc : C.Contains (Cfun x1 x2)) (hga : gA'.Contains (gA x1 x2)) (hgb : gB'.Contains (gB x1 x2))
    (hx1 : x1 = (c1 : ℝ) / 2 ^ P) (hx2 : x2 = (c2 : ℝ) / 2 ^ P)
    (h : vtxCheck C gA' gB' c1 c2 A B fw ew = true) :
    VDom ((A : ℝ) / 2 ^ P) ((B : ℝ) / 2 ^ P) ∧
      0 ≤ Wfun x1 x2 ((A : ℝ) / 2 ^ P) ((B : ℝ) / 2 ^ P) := by
  simp only [vtxCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hw⟩ := h
  obtain ⟨hdom, hV⟩ := vtx_sound hv
  refine ⟨hdom, ?_⟩
  have hd1 : (pt ((A : ℤ) - c1)).Contains ((A : ℝ) / 2 ^ P - x1) := by
    have := pt_contains ((A : ℤ) - c1)
    rw [hx1]; push_cast at this; rwa [sub_div] at this
  have hd2 : (pt ((B : ℤ) - c2)).Contains ((B : ℝ) / 2 ^ P - x2) := by
    have := pt_contains ((B : ℤ) - c2)
    rw [hx2]; push_cast at this; rwa [sub_div] at this
  have m1 : (C.lo : ℝ) ≤ 2 ^ P * Cfun x1 x2 := lo_le hc
  have m2 : ((gA'.mul (pt ((A : ℤ) - c1))).lo : ℝ) ≤
      2 ^ P * (gA x1 x2 * ((A : ℝ) / 2 ^ P - x1)) := lo_le (mul_sound hga hd1)
  have m3 : ((gB'.mul (pt ((B : ℤ) - c2))).lo : ℝ) ≤
      2 ^ P * (gB x1 x2 * ((B : ℝ) / 2 ^ P - x2)) := lo_le (mul_sound hgb hd2)
  have hwR : (0 : ℝ) ≤ (C.lo : ℝ) + ((gA'.mul (pt ((A : ℤ) - c1))).lo : ℝ) +
      ((gB'.mul (pt ((B : ℤ) - c2))).lo : ℝ) + (vtxLo A B fw ew : ℝ) := by
    have h0 := hw
    unfold wLo at h0
    exact_mod_cast h0
  have e : 2 ^ P * Wfun x1 x2 ((A : ℝ) / 2 ^ P) ((B : ℝ) / 2 ^ P) =
      2 ^ P * Cfun x1 x2 + 2 ^ P * (gA x1 x2 * ((A : ℝ) / 2 ^ P - x1)) +
        2 ^ P * (gB x1 x2 * ((B : ℝ) / 2 ^ P - x2)) +
        2 ^ P * Vfun ((A : ℝ) / 2 ^ P) ((B : ℝ) / 2 ^ P) := by
    unfold Wfun; ring
  have hsum : (C.lo : ℝ) + ((gA'.mul (pt ((A : ℤ) - c1))).lo : ℝ) +
      ((gB'.mul (pt ((B : ℤ) - c2))).lo : ℝ) + (vtxLo A B fw ew : ℝ) ≤
      2 ^ P * Cfun x1 x2 + 2 ^ P * (gA x1 x2 * ((A : ℝ) / 2 ^ P - x1)) +
        2 ^ P * (gB x1 x2 * ((B : ℝ) / 2 ^ P - x2)) +
        2 ^ P * Vfun ((A : ℝ) / 2 ^ P) ((B : ℝ) / 2 ^ P) :=
    add_le_add (add_le_add (add_le_add m1 m2) m3) hV
  apply nonneg_of_scaled
  rw [e]
  exact le_trans hwR hsum

theorem cellCheck_sound {cl : Cell} (h : cellCheck cl = true) {a t : ℝ}
    (ha0 : (cl.a0 : ℝ) / 2 ^ 64 ≤ a) (ha1 : a ≤ (cl.a1 : ℝ) / 2 ^ 64)
    (ht0 : (cl.t0 : ℝ) / 2 ^ 64 ≤ t) (ht1 : t ≤ (cl.t1 : ℝ) / 2 ^ 64) (hapos : 0 < a) :
    0 ≤ Gexpr a (bAt a t) := by
  simp only [cellCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hok, hA⟩, hT⟩, hT1⟩, hA1⟩, v00⟩, v10⟩, v01⟩, v11⟩ := h
  obtain ⟨hx1p, hx12, hx2h, hC, hGA, hGB⟩ := ctr_sound hok
  have hA0le : cl.a0 ≤ 2 ^ 63 := by omega
  have hA1le : cl.a1 ≤ 2 ^ 63 := hA1.le
  obtain ⟨d00, w00⟩ := vtxCheck_sound hC hGA hGB rfl rfl v00
  obtain ⟨d10, w10⟩ := vtxCheck_sound hC hGA hGB rfl rfl v10
  obtain ⟨d01, w01⟩ := vtxCheck_sound hC hGA hGB rfl rfl v01
  obtain ⟨d11, w11⟩ := vtxCheck_sound hC hGA hGB rfl rfl v11
  rw [aN_cast, bN_cast hA0le] at d00 w00 d01 w01
  rw [aN_cast, bN_cast hA1le] at d10 w10 d11 w11
  have h64 : (0 : ℝ) < 2 ^ 64 := by positivity
  have hAlt : (cl.a0 : ℝ) / 2 ^ 64 < (cl.a1 : ℝ) / 2 ^ 64 :=
    div_lt_div_of_pos_right (by exact_mod_cast hA) h64
  have hTlt : (cl.t0 : ℝ) / 2 ^ 64 < (cl.t1 : ℝ) / 2 ^ 64 :=
    div_lt_div_of_pos_right (by exact_mod_cast hT) h64
  have hT0 : (0 : ℝ) ≤ (cl.t0 : ℝ) / 2 ^ 64 := by positivity
  have hT1' : (cl.t1 : ℝ) / 2 ^ 64 ≤ 1 := by
    rw [div_le_one h64]; exact_mod_cast hT1
  exact cell_bound hAlt hTlt d00 d10 d01 d11 hx1p hx12 hx2h ha0 ha1 ht0 ht1 hapos hT0 hT1'
    w00 w10 w01 w11

end CKLaneN4.LU

end


