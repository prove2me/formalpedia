-- Prove2me | Definitions.Def_CK_CKLaneA_LogKap
-- name    : CK_CKLaneA_LogKap
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:40:32.810504+00:00
-- url     : https://prove2.me/theorems/87329a7b-fe83-479d-bd78-def4a34f35e7
-- title:
--   Courtade–Kumar proof module `CKLaneA.LogKap` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA.LogKap` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA.LogKap` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA.LogKap (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA/LogKap.lean)

import Definitions.Def_CK_CKLaneA_PsiEnc
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionBounds
import Definitions.Def_CK_GeneralCK_ReflectionContactInverse
import Definitions.Def_CK_GeneralCK_ReflectionRegularContact

/-!
# Lane A: dyadic enclosures of `log`, `biasE`, `biasB`, `A` and the regular contact `κ`
-/

namespace CKLaneA
open GeneralCK GeneralCK.Certificates Real
open DI

section LogEnc
variable {p : ℕ}

/-- enclosure of the rational `n/d` (`0 < d`) -/
def ratDI (n d : ℤ) : DyadicInterval p :=
  ⟨DyadicInterval.floorDiv (n * DyadicInterval.scale p) d,
   DyadicInterval.ceilDiv (n * DyadicInterval.scale p) d⟩

theorem ratDI_sound {n d : ℤ} (hd : 0 < d) : (ratDI n d : DyadicInterval p).Contains ((n : ℝ) / d) := by
  have hdr : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hf := DyadicInterval.floorDiv_mul_le (n * DyadicInterval.scale p) hd
  have hc := DyadicInterval.le_ceilDiv_mul (n * DyadicInterval.scale p) hd
  have hf' : ((DyadicInterval.floorDiv (n * DyadicInterval.scale p) d : ℤ) : ℝ) * (d:ℝ) ≤
      (n:ℝ) * (DyadicInterval.scale p : ℝ) := by exact_mod_cast hf
  have hc' : (n:ℝ) * (DyadicInterval.scale p : ℝ) ≤
      ((DyadicInterval.ceilDiv (n * DyadicInterval.scale p) d : ℤ) : ℝ) * (d:ℝ) := by exact_mod_cast hc
  constructor <;> simp only [ratDI]
  · rw [mul_div_assoc', le_div_iff₀ hdr]; linarith
  · rw [mul_div_assoc', div_le_iff₀ hdr]; linarith

def third : DyadicInterval p := ratDI 1 3

theorem third_contains : (third : DyadicInterval p).Contains (1 / 3 : ℝ) := by
  have := ratDI_sound (p := p) (n := 1) (d := 3) (by norm_num)
  simpa [third] using this

def log2Enc (N : ℕ) : DyadicInterval p :=
  (DyadicInterval.ofInt p 2).mul ((third : DyadicInterval p).mul (psiVal third N))

def log2OK (N : ℕ) : Bool := psiOK (third : DyadicInterval p) N

theorem log_two_eq : Real.log 2 = 2 * ((1 / 3) * psi (1 / 3)) := by
  have h := two_mul_psi (y := 1 / 3) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [← mul_assoc, h]
  rw [show (1:ℝ) + 1 / 3 = 2 * (2 / 3) by norm_num, show (1:ℝ) - 1 / 3 = 2 / 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  ring

theorem two_contains : (DyadicInterval.ofInt p 2).Contains (2:ℝ) := by
  simpa using DyadicInterval.ofInt_sound p 2

theorem log2Enc_sound {N : ℕ} (h : log2OK (p := p) N = true) :
    (log2Enc N : DyadicInterval p).Contains (Real.log 2) := by
  rw [log_two_eq]
  exact DyadicInterval.mul_sound two_contains
    (DyadicInterval.mul_sound third_contains (psiVal_sound h third_contains))

/-- reduction exponent for `x = X / 2^p`: `2^e ≤ 4X/3 < 2^(e+1)`, so `X/2^e ∈ [3/4, 3/2)` -/
def logEx (X : ℤ) : ℕ := Nat.log2 ((4 * X / 3).toNat)
def logE (X : ℤ) : ℤ := 2 ^ (logEx X)

def logY (X : ℤ) : DyadicInterval p := ratDI (X - logE X) (X + logE X)

/-- `log (X/2^p)` given an enclosure `L2` of `log 2` -/
def logPt (L2 : DyadicInterval p) (X : ℤ) : DyadicInterval p :=
  ((DyadicInterval.ofInt p ((logEx X : ℤ) - p)).mul L2).add
    ((DyadicInterval.ofInt p 2).mul ((logY X : DyadicInterval p).mul (psiValA (logY X))))

def logPtOK (X : ℤ) : Bool :=
  decide (0 < X) && psiOKA (logY X : DyadicInterval p)

theorem logPt_sound {L2 : DyadicInterval p} (hL2 : L2.Contains (Real.log 2)) {X : ℤ}
    (h : logPtOK (p := p) X = true) :
    (logPt L2 X : DyadicInterval p).Contains (Real.log ((X : ℝ) / DyadicInterval.scale p)) := by
  simp only [logPtOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hX, hpsi⟩ := h
  set e : ℕ := logEx X
  have hE : logE X = 2 ^ e := rfl
  have hEpos : (0:ℤ) < logE X := by rw [hE]; positivity
  have hXr : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
  have hEr : (0:ℝ) < (logE X : ℝ) := by exact_mod_cast hEpos
  set y : ℝ := ((X - logE X : ℤ) : ℝ) / ((X + logE X : ℤ) : ℝ)
  have hy : (logY X : DyadicInterval p).Contains y := ratDI_sound (by omega)
  have hden : (0:ℝ) < (X:ℝ) + (logE X : ℝ) := by linarith
  have hy1 : |y| < 1 := by
    simp only [y]; push_cast
    rw [abs_div, abs_of_pos hden, div_lt_one hden, abs_lt]
    constructor <;> linarith
  have hlogz : Real.log ((X:ℝ) / (logE X : ℝ)) = 2 * y * psi y := by
    rw [two_mul_psi hy1]
    have h1 : 1 + y = 2 * (X:ℝ) / ((X:ℝ) + (logE X : ℝ)) := by
      simp only [y]; push_cast; field_simp; ring
    have h2 : 1 - y = 2 * (logE X : ℝ) / ((X:ℝ) + (logE X : ℝ)) := by
      simp only [y]; push_cast; field_simp; ring
    have hpos1 : 0 < 1 + y := by rw [h1]; positivity
    have hpos2 : 0 < 1 - y := by rw [h2]; positivity
    rw [← Real.log_div hpos1.ne' hpos2.ne', h1, h2]
    congr 1
    field_simp
  have hs := scale_pos' p
  have hscale : (DyadicInterval.scale p : ℝ) = 2 ^ p := by
    unfold DyadicInterval.scale; push_cast; ring
  have hlogE : (logE X : ℝ) = 2 ^ e := by rw [hE]; push_cast; ring
  have hsplit : Real.log ((X : ℝ) / DyadicInterval.scale p) =
      ((e : ℝ) - p) * Real.log 2 + 2 * (y * psi y) := by
    have hx : (X : ℝ) / DyadicInterval.scale p = ((X:ℝ) / (logE X : ℝ)) * ((logE X : ℝ) / DyadicInterval.scale p) := by
      field_simp
    rw [hx, Real.log_mul (by positivity) (by positivity), hlogz, Real.log_div (by positivity) (by positivity),
      hlogE, hscale, Real.log_pow, Real.log_pow]
    ring
  rw [hsplit]
  have hk : (DyadicInterval.ofInt p ((e : ℤ) - p)).Contains ((e : ℝ) - p) := by
    have := DyadicInterval.ofInt_sound p ((e : ℤ) - p)
    push_cast at this; exact this
  exact DyadicInterval.add_sound (DyadicInterval.mul_sound hk hL2)
    (DyadicInterval.mul_sound two_contains (DyadicInterval.mul_sound hy (psiValA_sound hpsi hy)))

/-- interval log by monotonicity -/
def logIv (L2 : DyadicInterval p) (Xi : DyadicInterval p) : DyadicInterval p :=
  ⟨(logPt L2 Xi.lo : DyadicInterval p).lo, (logPt L2 Xi.hi : DyadicInterval p).hi⟩

def logIvOK (Xi : DyadicInterval p) : Bool :=
  decide (0 < Xi.lo) && logPtOK (p := p) Xi.lo && logPtOK (p := p) Xi.hi

theorem logIv_sound {L2 : DyadicInterval p} (hL2 : L2.Contains (Real.log 2))
    {Xi : DyadicInterval p} (h : logIvOK Xi = true) {x : ℝ}
    (hx : Xi.Contains x) : (logIv L2 Xi).Contains (Real.log x) ∧ 0 < x := by
  simp only [logIvOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlo, h1⟩, h2⟩ := h
  have hs := scale_pos' p
  have hxpos : 0 < x := pos_of_lo_pos hx hlo
  have hl := logPt_sound hL2 h1
  have hu := logPt_sound hL2 h2
  have hlo' : (0:ℝ) < (Xi.lo : ℝ) / DyadicInterval.scale p := by
    apply div_pos _ hs; exact_mod_cast hlo
  have hxl : (Xi.lo : ℝ) / DyadicInterval.scale p ≤ x := lo_bound hx
  have hxu : x ≤ (Xi.hi : ℝ) / DyadicInterval.scale p := hi_bound hx
  have m1 := Real.log_le_log hlo' hxl
  have m2 := Real.log_le_log hxpos hxu
  refine ⟨⟨?_, ?_⟩, hxpos⟩
  · simp only [logIv]
    have := hl.1
    nlinarith [mul_le_mul_of_nonneg_left m1 hs.le]
  · simp only [logIv]
    have := hu.2
    nlinarith [mul_le_mul_of_nonneg_left m2 hs.le]

/-- outer jet enclosure for `Jet2.log Jet2.variableJet` -/
def logJetEnc (L2 : DyadicInterval p) (Xi : DyadicInterval p) : DyadicJetEnclosure p :=
  ⟨logIv L2 Xi, Xi.recip, (Xi.recip.mul Xi.recip).neg⟩

theorem logJetEnc_sound {L2 : DyadicInterval p} (hL2 : L2.Contains (Real.log 2))
    {Xi : DyadicInterval p} (h : logIvOK Xi = true) {x : ℝ}
    (hx : Xi.Contains x) : (logJetEnc L2 Xi).Contains (Jet2.log Jet2.variableJet) x ∧ 0 < x := by
  obtain ⟨hl, hxpos⟩ := logIv_sound hL2 h hx
  have hlo : 0 < Xi.lo := by
    simp only [logIvOK, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1
  have hr := DyadicInterval.recip_sound hlo hx
  refine ⟨⟨hl, ?_, ?_⟩, hxpos⟩
  · show Xi.recip.Contains ((Jet2.log Jet2.variableJet).first x)
    simpa [Jet2.log, Jet2.variableJet, one_div] using hr
  · show (Xi.recip.mul Xi.recip).neg.Contains ((Jet2.log Jet2.variableJet).second x)
    have := DyadicInterval.neg_sound (DyadicInterval.mul_sound hr hr)
    convert this using 1
    simp only [Jet2.log, Jet2.variableJet, id]
    ring

end LogEnc

/-! ## `biasE`, `biasB`, `A` over intervals -/

theorem A_eq_mul_psi {c : ℝ} (hc : |c| < 1) : SmallMean.A c = c * psi c := by
  have h := two_mul_psi hc
  have h1 : 0 < 1 + c := by linarith [neg_abs_le c]
  have h2 : 0 < 1 - c := by linarith [le_abs_self c]
  unfold SmallMean.A
  rw [Real.log_div h1.ne' h2.ne']
  linarith

theorem biasE_eq {c : ℝ} (hc : |c| < 1) :
    Reflection.biasE c = Reflection.biasB c - c * SmallMean.A c := by
  have h1 : 0 < 1 + c := by linarith [neg_abs_le c]
  have h2 : 0 < 1 - c := by linarith [le_abs_self c]
  unfold Reflection.biasE Reflection.biasB SmallMean.A
  rw [show 1 - c * c = (1 - c) * (1 + c) by ring, Real.log_mul h2.ne' h1.ne',
    Real.log_div h1.ne' h2.ne']
  ring

section EB
variable {p : ℕ}

/-- `(E, B, A)` enclosures of `biasE, biasB, A` over `C` -/
def ebaEnc (L2 : DyadicInterval p) (C : DyadicInterval p) :
    DyadicInterval p × DyadicInterval p × DyadicInterval p :=
  let B := L2.sub (divNat (logIv L2 (one.sub (C.mul C))) 2)
  let A := C.mul (psiValA C)
  (B.sub (C.mul A), B, A)

def ebaOK (C : DyadicInterval p) : Bool :=
  psiOKA C && logIvOK (one.sub (C.mul C))

theorem ebaEnc_sound {L2 : DyadicInterval p} (hL2 : L2.Contains (Real.log 2))
    {C : DyadicInterval p} (h : ebaOK C = true) {c : ℝ}
    (hc : C.Contains c) :
    (ebaEnc L2 C).1.Contains (Reflection.biasE c) ∧ (ebaEnc L2 C).2.1.Contains (Reflection.biasB c) ∧
      (ebaEnc L2 C).2.2.Contains (SmallMean.A c) ∧ |c| < 1 := by
  simp only [ebaOK, Bool.and_eq_true] at h
  obtain ⟨hpsi, hlog⟩ := h
  obtain ⟨-, hc1⟩ := psiEncA_sound hpsi hc
  have hcc := DyadicInterval.sub_sound one_contains (DyadicInterval.mul_sound hc hc)
  obtain ⟨hL, -⟩ := logIv_sound hL2 hlog hcc
  have hB : (ebaEnc L2 C).2.1.Contains (Reflection.biasB c) := by
    have := DyadicInterval.sub_sound hL2 (divNat_sound hL (m := 2) (by norm_num))
    simpa [ebaEnc, Reflection.biasB] using this
  have hA : (ebaEnc L2 C).2.2.Contains (SmallMean.A c) := by
    rw [A_eq_mul_psi hc1]
    exact DyadicInterval.mul_sound hc (psiValA_sound hpsi hc)
  refine ⟨?_, hB, hA, hc1⟩
  rw [biasE_eq hc1]
  exact DyadicInterval.sub_sound hB (DyadicInterval.mul_sound hc hA)

end EB

/-! ## The regular contact `κ = Reflection.regularContact` -/

noncomputable def kapJet : Jet2 :=
  ⟨Reflection.regularContact, Reflection.regularContactFirst, Reflection.regularContactSecond⟩

theorem kapJet_soundAt (t : ℝ) : kapJet.SoundAt t :=
  ⟨Reflection.hasDerivAt_regularContact t, Reflection.hasDerivAt_regularContactFirst t⟩

theorem regularContact_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Reflection.regularContact t := by
  rcases ht.lt_or_eq with ht | ht
  · rw [Reflection.regularContact_pos_eq ht]
    exact (Reflection.biasContact_mem (inv_pos.mpr ht)).1.le
  · subst ht; simp [Reflection.regularContact_zero]

theorem biasE_one : Reflection.biasE 1 = 0 := by
  unfold Reflection.biasE; norm_num

theorem biasE_nonneg' {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : 0 ≤ Reflection.biasE c := by
  have := Reflection.biasE_antitone ⟨h0, h1⟩ ⟨zero_le_one, le_rfl⟩ h1
  rw [biasE_one] at this; exact this

/-- bracket lemma: `c1 ≤ tlo E(c1)` and `thi E(c2) ≤ c2` bracket `κ(t)` for `t ∈ [tlo, thi]` -/
theorem kappa_bracket {t tlo thi c1 c2 : ℝ} (htlo : 0 ≤ tlo) (ht1 : tlo ≤ t) (ht2 : t ≤ thi)
    (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2) (hc2 : c2 ≤ 1)
    (hlo : c1 ≤ tlo * Reflection.biasE c1) (hhi : thi * Reflection.biasE c2 ≤ c2) :
    c1 ≤ Reflection.regularContact t ∧ Reflection.regularContact t ≤ c2 := by
  have ht0 : 0 ≤ t := htlo.trans ht1
  set c := Reflection.regularContact t
  have hc0 : 0 ≤ c := regularContact_nonneg ht0
  have hcl1 : c < 1 := (Reflection.regularContact_mem t).2
  have heq : c = t * Reflection.biasE c := Reflection.regularContact_equation t
  constructor
  · by_contra hn
    push Not at hn
    have hm := Reflection.biasE_antitone ⟨hc0, hcl1.le⟩ ⟨hc1, hc12.trans hc2⟩ hn.le
    have hE1 := biasE_nonneg' hc1 (hc12.trans hc2)
    have : tlo * Reflection.biasE c1 ≤ t * Reflection.biasE c :=
      mul_le_mul ht1 hm hE1 ht0
    linarith
  · by_contra hn
    push Not at hn
    have hm := Reflection.biasE_antitone ⟨hc1.trans hc12, hc2⟩ ⟨hc0, hcl1.le⟩ hn.le
    have hE2 := biasE_nonneg' (hc1.trans hc12) hc2
    have hEc := biasE_nonneg' hc0 hcl1.le
    have : t * Reflection.biasE c ≤ thi * Reflection.biasE c2 :=
      mul_le_mul ht2 hm hEc (htlo.trans (ht1.trans ht2))
    linarith

section Kap
variable {p : ℕ}

/-- the bracket `[max h.1 0, h.2]` from a hint (computed externally, checked here) -/
def kapC (hint : ℤ × ℤ) : DyadicInterval p := ⟨max hint.1 0, hint.2⟩

def kapEnc (L2 : DyadicInterval p) (hint : ℤ × ℤ) : DyadicJetEnclosure p :=
  let C : DyadicInterval p := kapC hint
  let eba := ebaEnc L2 C
  let E := eba.1
  let B := eba.2.1
  let A := eba.2.2
  let rB := B.recip
  let E2 := E.mul E
  ⟨C, E2.mul rB,
   ((((DyadicInterval.ofInt p 2).mul (E2.mul E)).mul A).mul (rB.mul rB)).neg.sub
     ((((E2.mul E2).mul C).mul (one.sub (C.mul C)).recip).mul ((rB.mul rB).mul rB))⟩

def kapOK (L2 : DyadicInterval p) (hint : ℤ × ℤ) (Ti : DyadicInterval p) : Bool :=
  let C : DyadicInterval p := kapC hint
  decide (0 ≤ Ti.lo) && decide (C.lo ≤ C.hi) && decide (C.hi ≤ DyadicInterval.scale p) &&
  ebaOK (pt C.lo : DyadicInterval p) && ebaOK (pt C.hi : DyadicInterval p) &&
  decide (C.lo ≤ ((pt Ti.lo : DyadicInterval p).mul (ebaEnc L2 (pt C.lo : DyadicInterval p)).1).lo) &&
  decide (((pt Ti.hi : DyadicInterval p).mul (ebaEnc L2 (pt C.hi : DyadicInterval p)).1).hi ≤ C.hi) &&
  ebaOK C && decide (0 < (ebaEnc L2 C).2.1.lo) && decide (0 < (one.sub (C.mul C)).lo)

theorem kapEnc_sound {L2 : DyadicInterval p} (hL2 : L2.Contains (Real.log 2)) {hint : ℤ × ℤ}
    {Ti : DyadicInterval p} (h : kapOK L2 hint Ti = true) {t : ℝ}
    (ht : Ti.Contains t) : (kapEnc L2 hint).Contains kapJet t := by
  simp only [kapOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hT0, hC12⟩, hC1⟩, hel⟩, heh⟩, hlo⟩, hhi⟩, hebaC⟩, hBpos⟩, hgap⟩ := h
  set C : DyadicInterval p := kapC hint
  have hs := scale_pos' p
  set tlo : ℝ := (Ti.lo : ℝ) / DyadicInterval.scale p
  set thi : ℝ := (Ti.hi : ℝ) / DyadicInterval.scale p
  set c1 : ℝ := (C.lo : ℝ) / DyadicInterval.scale p
  set c2 : ℝ := (C.hi : ℝ) / DyadicInterval.scale p
  have htlo : 0 ≤ tlo := div_nonneg (by exact_mod_cast hT0) hs.le
  have ht1 : tlo ≤ t := lo_bound ht
  have ht2 : t ≤ thi := hi_bound ht
  have hc1pos : 0 ≤ C.lo := le_max_right _ _
  have hc1 : 0 ≤ c1 := div_nonneg (by exact_mod_cast hc1pos) hs.le
  have hc12 : c1 ≤ c2 := div_le_div_of_nonneg_right (by exact_mod_cast hC12) hs.le
  have hc2 : c2 ≤ 1 := by rw [div_le_one hs]; exact_mod_cast hC1
  have hE1 := (ebaEnc_sound hL2 hel (pt_contains C.lo)).1
  have hE2 := (ebaEnc_sound hL2 heh (pt_contains C.hi)).1
  have hp1 := DyadicInterval.mul_sound (pt_contains Ti.lo) hE1
  have hp2 := DyadicInterval.mul_sound (pt_contains Ti.hi) hE2
  have hlo' : c1 ≤ tlo * Reflection.biasE c1 := by
    have := lo_bound hp1
    have h' : (C.lo : ℝ) / DyadicInterval.scale p ≤
        (((pt Ti.lo : DyadicInterval p).mul (ebaEnc L2 (pt C.lo : DyadicInterval p)).1).lo : ℝ) /
          DyadicInterval.scale p :=
      div_le_div_of_nonneg_right (by exact_mod_cast hlo) hs.le
    exact h'.trans this
  have hhi' : thi * Reflection.biasE c2 ≤ c2 := by
    have := hi_bound hp2
    have h' : (((pt Ti.hi : DyadicInterval p).mul (ebaEnc L2 (pt C.hi : DyadicInterval p)).1).hi : ℝ) /
          DyadicInterval.scale p ≤ (C.hi : ℝ) / DyadicInterval.scale p :=
      div_le_div_of_nonneg_right (by exact_mod_cast hhi) hs.le
    exact this.trans h'
  obtain ⟨hk1, hk2⟩ := kappa_bracket htlo ht1 ht2 hc1 hc12 hc2 hlo' hhi'
  set c := Reflection.regularContact t
  have hcC : C.Contains c := by
    constructor
    · have := mul_le_mul_of_nonneg_left hk1 hs.le
      simp only [c1] at this; rw [mul_div_cancel₀ _ hs.ne'] at this; exact this
    · have := mul_le_mul_of_nonneg_left hk2 hs.le
      simp only [c2] at this; rw [mul_div_cancel₀ _ hs.ne'] at this; exact this
  obtain ⟨hE, hB, hA, hcabs⟩ := ebaEnc_sound hL2 hebaC hcC
  have hrB := DyadicInterval.recip_sound hBpos hB
  have hgapC := DyadicInterval.sub_sound one_contains (DyadicInterval.mul_sound hcC hcC)
  have hrg := DyadicInterval.recip_sound hgap hgapC
  have hE2m := DyadicInterval.mul_sound hE hE
  refine ⟨hcC, ?_, ?_⟩
  · show (((ebaEnc L2 C).1.mul (ebaEnc L2 C).1).mul (ebaEnc L2 C).2.1.recip).Contains
      (Reflection.regularContactFirst t)
    have := DyadicInterval.mul_sound hE2m hrB
    convert this using 1
    simp only [Reflection.regularContactFirst]
    rw [div_eq_mul_inv, pow_two]
  · have := DyadicInterval.sub_sound
      (DyadicInterval.neg_sound (DyadicInterval.mul_sound (DyadicInterval.mul_sound
        (DyadicInterval.mul_sound two_contains (DyadicInterval.mul_sound hE2m hE)) hA)
        (DyadicInterval.mul_sound hrB hrB)))
      (DyadicInterval.mul_sound (DyadicInterval.mul_sound (DyadicInterval.mul_sound
        (DyadicInterval.mul_sound hE2m hE2m) hcC) hrg)
        (DyadicInterval.mul_sound (DyadicInterval.mul_sound hrB hrB) hrB))
    convert this using 1
    · rfl
    change Reflection.regularContactSecond t = _
    rw [Reflection.regularContactSecond.eq_1]
    show -2 * Reflection.biasE c ^ 3 * SmallMean.A c / Reflection.biasB c ^ 2 -
      Reflection.biasE c ^ 4 * c / ((1 - c ^ 2) * Reflection.biasB c ^ 3) = _
    have hBne : Reflection.biasB c ≠ 0 := by
      have := pos_of_lo_pos hB hBpos; exact this.ne'
    have hgne : 1 - c * c ≠ 0 := by
      have := pos_of_lo_pos hgapC hgap; linarith
    have hgne' : 1 - c ^ 2 ≠ 0 := by rw [pow_two]; exact hgne
    field_simp

end Kap

end CKLaneA


