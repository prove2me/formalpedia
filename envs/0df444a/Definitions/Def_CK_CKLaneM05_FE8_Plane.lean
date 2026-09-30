-- Prove2me | Definitions.Def_CK_CKLaneM05_FE8_Plane
-- name    : CK_CKLaneM05_FE8_Plane
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:02:16.561074+00:00
-- url     : https://prove2.me/theorems/705150c4-831c-447e-a6ee-2dcf14b1a195
-- title:
--   Courtade–Kumar proof module `CKLaneM05.FE8.Plane` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.FE8.Plane` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.FE8.Plane` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.FE8.Plane (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/FE8/Plane.lean)

import Definitions.Def_CK_CKLaneM05_FE8_Parent

-- ===== source module CKLaneM05.FE8.Plane =====
section

/-!
# Lane M05 / FE8: same-side plane checker (endpoint family)

A same-side port of `CKLaneD.checkCell` (Lane D's plane/chord relaxation) using `CKLaneE.FP`
fixed-point enclosures:

* `candidateGap psi ≤ P(H m - E) - P(C0 - E)` (`CKLaneD.law_gap_le_P`);
* `P(I) ≤` chord of the convex `P` over `[pLo, pHi]` with bracket values at `xa`, `xb`;
* `P(s) ≥ P(sL) + 4 (s - sL)` (`Scalar.P_increment_lower`), `P(sL)` bracket at `xc` or `4 sL`;
* explicit symmetric plane at the rational contact `v`: `cost ≥ ccLo (b - a) - 2 Khi E`
  (`CKLaneD.plane_cost_lower`);
* `kappa E` at `t*`, chords of `H` at `a` and `b` (concave), left-slope tangent of `H` at `m_lo`,
  final affine function of `(a, b)` checked at the corners.

Same side: `C0 ∈ [(Hlo a0 + Hlo b0)/2, (Hhi a1 + Hhi b1)/2]` (`H` increasing on `[0, 1/2]`).
The semantic statement carries the row premise `1/20 ≤ b - a` (so `b - a ≥ 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

open GeneralCK CKLaneE.FP

/-- psi-candidate statement on the box, for mean difference at least `1/20`. -/
def SemD (B : CKLaneD.Box) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), CKLaneD.InBox B μ.a μ.b μ.meanEntropy →
    1 / 20 ≤ μ.b - μ.a → candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

theorem leafOK_of_semD {B : CKLaneD.Box} (h : SemD B) : LeafOK B := by
  intro k μ _ _ _ _ hd _ _ hin hact
  have hact' : phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy := hact
  exact (hybrid_gap_le_psi hact'.le).trans (h k μ hin hd)

/-- Plane-cell certificate (untrusted data). -/
structure PC where
  v : ℚ
  hm : ℚ
  pLo : ℚ
  pHi : ℚ
  xa : ℚ
  xb : ℚ
  sL : ℚ
  useXc : Bool
  xc : ℚ
  deriving Repr

section defs
variable (B : CKLaneD.Box) (c : PC)

def HmLo2 : ℚ := min (Hlo (mLo B)) (Hlo (mHi B))
def numM : ℚ := (Hhi (mLo B) - Hlo (mLo B - c.hm)) / c.hm
def HmHi2 : ℚ := Hhi (mLo B) + max 0 (numM B c * (mHi B - mLo B))
def PuLo : ℚ := (1 - 2 * c.xa) * Jh c.xa
def PuHi : ℚ := (1 - 2 * c.xb) * Jh c.xb
def PlS : ℚ := if c.useXc then (1 - 2 * c.xc) * Jl c.xc else 4 * c.sL
def sig : ℚ := (PuHi c - PuLo c) / (c.pHi - c.pLo)
def nLo : ℚ := -(lHi c.v + l1Hi c.v)
def nHi : ℚ := -(lLo c.v + l1Lo c.v)
def baseK : ℚ := (1 - 2 * c.v) ^ 2 / (2 * c.v * (1 - c.v))
def Klo : ℚ := baseK c / nHi c
def Khi : ℚ := baseK c / nLo c
def ccLo : ℚ := Jl c.v + 2 * Klo c * Hlo c.v / (1 - 2 * c.v)
def kap : ℚ := sig c - 2 * Khi c - 4
def tstar : ℚ := if 0 ≤ kap c then B.t0 else B.t1
def gam : ℚ := (kap c * tstar B c + 4) / 2
def mua : ℚ := (Hlo B.ahi - Hlo B.alo) / (B.ahi - B.alo)
def mub : ℚ := (Hlo B.bhi - Hlo B.blo) / (B.bhi - B.blo)
def constT : ℚ := -PuLo c + sig c * c.pLo + PlS c - 4 * c.sL
def ca : ℚ := -ccLo c + gam B c * mua B - sig c * numM B c / 2
def cb : ℚ := ccLo c + gam B c * mub B - sig c * numM B c / 2
def c0 : ℚ :=
  kap c * CKLaneD.EMIN * (1 - tstar B c) +
    gam B c * (Hlo B.alo - mua B * B.alo + Hlo B.blo - mub B * B.blo) -
    sig c * (Hhi (mLo B) - numM B c * mLo B) + constT c
def finalVal : ℚ :=
  c0 B c + min (ca B c * B.alo) (ca B c * B.ahi) + min (cb B c * B.blo) (cb B c * B.bhi)

def xcOK : Bool :=
  !c.useXc || (ptOk c.xc && decide (2 * c.xc ≤ 1 ∧ 1 - c.sL ≤ Hlo c.xc ∧ 0 ≤ lamLo c.xc))

/-- The Boolean plane-cell checker (binds the box and every enclosure). -/
def planeCheck : Bool :=
  boxSane B && boxPts B && decide (0 < c.hm ∧ c.hm < mLo B) &&
    ptOk (mLo B - c.hm) && ptOk c.xa && ptOk c.xb && ptOk c.v && xcOK c &&
    decide (CKLaneD.EMIN < C0lo B) &&
    decide (0 ≤ c.pLo ∧ c.pLo ≤ HmLo2 B - Eup B ∧ HmHi2 B c - Elo B ≤ c.pHi ∧
      c.pLo < c.pHi ∧ c.pHi < 1) &&
    decide (2 * c.xa ≤ 1 ∧ Hhi c.xa ≤ 1 - c.pLo) &&
    decide (2 * c.xb ≤ 1 ∧ Hhi c.xb ≤ 1 - c.pHi) &&
    decide (0 ≤ c.sL ∧ c.sL ≤ (C0lo B - CKLaneD.EMIN) * (1 - B.t1)) &&
    decide (0 ≤ sig c) && decide (0 < c.v ∧ 2 * c.v < 1) && decide (0 < nLo c) &&
    decide (0 ≤ Hlo c.v ∧ 0 ≤ lamLo c.v) && decide (0 ≤ gam B c) && decide (0 ≤ finalVal B c)

end defs

/-! ## Soundness -/

theorem PlS_le {c : PC} (hx : xcOK c = true) (hs0 : 0 ≤ (c.sL : ℝ)) (hs1 : (c.sL : ℝ) < 1) :
    ((PlS c : ℚ) : ℝ) ≤ Scalar.P (c.sL : ℝ) := by
  unfold xcOK at hx
  unfold PlS
  cases hu : c.useXc with
  | false =>
    rw [if_neg Bool.false_ne_true]
    push_cast
    exact Scalar.four_mul_le_P hs0 hs1
  | true =>
    rw [hu] at hx
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hp, h2, h3, hlam⟩ := hx
    rw [if_pos rfl]
    have hx0 : (0 : ℝ) < c.xc := by exact_mod_cast (ptOk_pos hp).1
    have h2' : 2 * (c.xc : ℝ) ≤ 1 := by exact_mod_cast h2
    obtain ⟨hHl, _⟩ := H_bounds hp
    have h3' : 1 - (c.sL : ℝ) ≤ ((Hlo c.xc : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr h3; push_cast at h; exact h
    have hb := CKLaneD.P_ge_bracket hs0 hs1 hx0 (by linarith) (h3'.trans hHl)
    have hJl := Jl_le hp hlam
    push_cast
    have := mul_le_mul_of_nonneg_left hJl (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xc : ℝ))
    linarith

set_option maxHeartbeats 4000000 in
theorem planeCheck_sound {B : CKLaneD.Box} {c : PC} (h : planeCheck B c = true) : SemD B := by
  intro k μ hbox hd
  simp only [planeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hp⟩, ⟨hhm0, hhm1⟩⟩, pMh⟩, pxa⟩, pxb⟩, pv⟩, hxc⟩, hC0⟩,
    ⟨hpL0, hpL1, hpH1, hpLH, hpH2⟩⟩, ⟨hxa1, hxa2⟩⟩, ⟨hxb1, hxb2⟩⟩, ⟨hsL0, hsL1⟩⟩, hsig⟩,
    ⟨hv0q, hv2⟩⟩, hnLo⟩, ⟨hHv, hlamv⟩⟩, hgam⟩, hfin⟩ := h
  -- box facts
  obtain ⟨hmLo, hmHi, hmHh, hm0, hHmL, hHmH, hElo, hEup, hEm, hE0, _⟩ := box_facts hs hp μ hbox
  have hs' := hs
  simp only [boxSane, decide_eq_true_eq] at hs'
  obtain ⟨sa0, sa1, sa2, sb0, sb1, sb2, st0, st1, st2⟩ := hs'
  have hp' := hp
  simp only [boxPts, Bool.and_eq_true] at hp'
  obtain ⟨⟨⟨⟨⟨pa0, pa1⟩, pb0⟩, pb1⟩, pm0⟩, pm1⟩ := hp'
  obtain ⟨ha0, ha1, hb0, hb1, hE0', hE1'⟩ := hbox
  have hjen := CKLaneD.law_gap_le_P μ
  have hm_def : μ.midpoint = (μ.a + μ.b) / 2 := rfl
  rw [← hm_def] at hjen
  -- casts
  have rA0 : (0 : ℝ) < ((B.alo : ℚ) : ℝ) := by exact_mod_cast sa0
  have rA2 : ((B.ahi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr sa2; push_cast at h; exact h
  have rB0 : (0 : ℝ) < ((B.blo : ℚ) : ℝ) := by exact_mod_cast sb0
  have rB2 : ((B.bhi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr sb2; push_cast at h; exact h
  have rt0 : (0 : ℝ) ≤ ((B.t0 : ℚ) : ℝ) := by exact_mod_cast st0
  have rt01 : ((B.t0 : ℚ) : ℝ) ≤ ((B.t1 : ℚ) : ℝ) := by exact_mod_cast st1
  have rt1 : ((B.t1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast st2
  -- entropy enclosures at the corners
  obtain ⟨HA0l, _⟩ := H_bounds pa0
  obtain ⟨HA1l, HA1u⟩ := H_bounds pa1
  obtain ⟨HB0l, _⟩ := H_bounds pb0
  obtain ⟨HB1l, HB1u⟩ := H_bounds pb1
  obtain ⟨HM0l, HM0u⟩ := H_bounds pm0
  obtain ⟨HM1l, _⟩ := H_bounds pm1
  obtain ⟨HMhl, _⟩ := H_bounds pMh
  have ha2 : μ.a ≤ 1 / 2 := ha1.trans rA2
  have hb2 : μ.b ≤ 1 / 2 := hb1.trans rB2
  have hHa_lo : ((Hlo B.alo : ℚ) : ℝ) ≤ H μ.a := HA0l.trans (H_le_H rA0.le ha0 ha2)
  have hHb_lo : ((Hlo B.blo : ℚ) : ℝ) ≤ H μ.b := HB0l.trans (H_le_H rB0.le hb0 hb2)
  have hC0lo : ((C0lo B : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    have e : ((C0lo B : ℚ) : ℝ) = (((Hlo B.alo : ℚ) : ℝ) + ((Hlo B.blo : ℚ) : ℝ)) / 2 := by
      unfold C0lo; push_cast; ring
    rw [e]; linarith
  -- parent mean enclosures
  have c_mLo : ((mLo B : ℚ) : ℝ) = ((B.alo : ℚ) : ℝ) / 2 + ((B.blo : ℚ) : ℝ) / 2 := by
    unfold mLo; push_cast; ring
  have c_mHi : ((mHi B : ℚ) : ℝ) = ((B.ahi : ℚ) : ℝ) / 2 + ((B.bhi : ℚ) : ℝ) / 2 := by
    unfold mHi; push_cast; ring
  have rhm0 : (0 : ℝ) < (c.hm : ℝ) := by exact_mod_cast hhm0
  have rhm1 : (c.hm : ℝ) < ((mLo B : ℚ) : ℝ) := by exact_mod_cast hhm1
  have rmLo0 : (0 : ℝ) ≤ ((mLo B : ℚ) : ℝ) := by linarith
  have rmHi1 : ((mHi B : ℚ) : ℝ) ≤ 1 := by linarith
  have hHm_lo : ((HmLo2 B : ℚ) : ℝ) ≤ H μ.midpoint := by
    have hc := CKLaneD.H_chord_lower (lo := ((mLo B : ℚ) : ℝ)) (hi := ((mHi B : ℚ) : ℝ))
      (x := μ.midpoint) (HL0 := ((HmLo2 B : ℚ) : ℝ)) (HL1 := ((HmLo2 B : ℚ) : ℝ)) rmLo0 hmLo hmHi
      rmHi1 (by unfold HmLo2; rw [Rat.cast_min]; exact (min_le_left _ _).trans HM0l)
      (by unfold HmLo2; rw [Rat.cast_min]; exact (min_le_right _ _).trans HM1l)
    calc ((HmLo2 B : ℚ) : ℝ) = ((HmLo2 B : ℚ) : ℝ) + (((HmLo2 B : ℚ) : ℝ) - ((HmLo2 B : ℚ) : ℝ)) /
          (((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ)) * (μ.midpoint - ((mLo B : ℚ) : ℝ)) := by ring
      _ ≤ H μ.midpoint := hc
  have hMhl' : ((Hlo (mLo B - c.hm) : ℚ) : ℝ) ≤ H (((mLo B : ℚ) : ℝ) - (c.hm : ℝ)) := by
    have := HMhl; push_cast at this; exact this
  have enum : ((numM B c : ℚ) : ℝ) =
      (((Hhi (mLo B) : ℚ) : ℝ) - ((Hlo (mLo B - c.hm) : ℚ) : ℝ)) / (c.hm : ℝ) := by
    unfold numM; push_cast; ring
  have hHm_tan : H μ.midpoint ≤
      ((Hhi (mLo B) : ℚ) : ℝ) + ((numM B c : ℚ) : ℝ) * (μ.midpoint - ((mLo B : ℚ) : ℝ)) := by
    have hc := CKLaneD.H_leftslope_upper (lo := ((mLo B : ℚ) : ℝ)) (h := (c.hm : ℝ))
      (x := μ.midpoint) (HU0 := ((Hhi (mLo B) : ℚ) : ℝ))
      (HLh := ((Hlo (mLo B - c.hm) : ℚ) : ℝ)) rhm0 (by linarith) hmLo (by linarith) HM0u hMhl'
    rw [enum]; exact hc
  have hHm_hi : H μ.midpoint ≤ ((HmHi2 B c : ℚ) : ℝ) := by
    have hmm : 0 ≤ μ.midpoint - ((mLo B : ℚ) : ℝ) := by linarith
    have hmm2 : μ.midpoint - ((mLo B : ℚ) : ℝ) ≤ ((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ) := by
      linarith
    have hmax : ((numM B c : ℚ) : ℝ) * (μ.midpoint - ((mLo B : ℚ) : ℝ)) ≤
        max 0 (((numM B c : ℚ) : ℝ) * (((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ))) := by
      rcases le_total 0 ((numM B c : ℚ) : ℝ) with hn | hn
      · exact (mul_le_mul_of_nonneg_left hmm2 hn).trans (le_max_right _ _)
      · exact (mul_nonpos_iff.mpr (Or.inr ⟨hn, hmm⟩)).trans (le_max_left _ _)
    have e : ((HmHi2 B c : ℚ) : ℝ) = ((Hhi (mLo B) : ℚ) : ℝ) +
        max 0 (((numM B c : ℚ) : ℝ) * (((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ))) := by
      unfold HmHi2; push_cast; ring
    rw [e]; linarith
  -- information range
  have rpL0 : (0 : ℝ) ≤ (c.pLo : ℝ) := by exact_mod_cast hpL0
  have rpL1 : (c.pLo : ℝ) ≤ ((HmLo2 B : ℚ) : ℝ) - ((Eup B : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hpL1; push_cast at h; exact h
  have rpH1 : ((HmHi2 B c : ℚ) : ℝ) - ((Elo B : ℚ) : ℝ) ≤ (c.pHi : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hpH1; push_cast at h; exact h
  have rpLH : (c.pLo : ℝ) < (c.pHi : ℝ) := by exact_mod_cast hpLH
  have rpH2 : (c.pHi : ℝ) < 1 := by exact_mod_cast hpH2
  have hIlo : (c.pLo : ℝ) ≤ H μ.midpoint - μ.meanEntropy := by linarith
  have hIhi : H μ.midpoint - μ.meanEntropy ≤ (c.pHi : ℝ) := by linarith
  -- deficit range
  have hdef := CKLaneD.law_deficit_mem μ
  have rsL0 : (0 : ℝ) ≤ (c.sL : ℝ) := by exact_mod_cast hsL0
  have rsL1 : (c.sL : ℝ) ≤ (((C0lo B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsL1; push_cast at h; exact h
  have hsL : (c.sL : ℝ) ≤ (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    have h1 : (((C0lo B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) ≤
        ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) =
        (H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ) -
          ((B.t1 : ℚ) : ℝ) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) := by ring
    linarith
  -- P upper bound on the information side
  have rxa1 : 2 * (c.xa : ℝ) ≤ 1 := by exact_mod_cast hxa1
  have rxb1 : 2 * (c.xb : ℝ) ≤ 1 := by exact_mod_cast hxb1
  obtain ⟨_, HXa⟩ := H_bounds pxa
  obtain ⟨_, HXb⟩ := H_bounds pxb
  have rxa2 : ((Hhi c.xa : ℚ) : ℝ) ≤ 1 - (c.pLo : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hxa2; push_cast at h; exact h
  have rxb2 : ((Hhi c.xb : ℚ) : ℝ) ≤ 1 - (c.pHi : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hxb2; push_cast at h; exact h
  have hxa0 : (0 : ℝ) < c.xa := by exact_mod_cast (ptOk_pos pxa).1
  have hxb0 : (0 : ℝ) < c.xb := by exact_mod_cast (ptOk_pos pxb).1
  have hPLo : Scalar.P (c.pLo : ℝ) ≤ ((PuLo c : ℚ) : ℝ) := by
    have hb := CKLaneD.P_le_bracket rpL0 (by linarith) hxa0 (by linarith) (HXa.trans rxa2)
    have hJ := le_Jh pxa (by linarith)
    have e : ((PuLo c : ℚ) : ℝ) = (1 - 2 * (c.xa : ℝ)) * ((Jh c.xa : ℚ) : ℝ) := by
      unfold PuLo; push_cast; ring
    have := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xa : ℝ))
    rw [e]; linarith
  have hPHi : Scalar.P (c.pHi : ℝ) ≤ ((PuHi c : ℚ) : ℝ) := by
    have hb := CKLaneD.P_le_bracket (by linarith) rpH2 hxb0 (by linarith) (HXb.trans rxb2)
    have hJ := le_Jh pxb (by linarith)
    have e : ((PuHi c : ℚ) : ℝ) = (1 - 2 * (c.xb : ℝ)) * ((Jh c.xb : ℚ) : ℝ) := by
      unfold PuHi; push_cast; ring
    have := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xb : ℝ))
    rw [e]; linarith
  have esig : ((sig c : ℚ) : ℝ) =
      (((PuHi c : ℚ) : ℝ) - ((PuLo c : ℚ) : ℝ)) / ((c.pHi : ℝ) - (c.pLo : ℝ)) := by
    unfold sig; push_cast; ring
  have hPI : Scalar.P (H μ.midpoint - μ.meanEntropy) ≤
      ((PuLo c : ℚ) : ℝ) + ((sig c : ℚ) : ℝ) * (H μ.midpoint - μ.meanEntropy - (c.pLo : ℝ)) := by
    have hch := CKLaneD.P_chord rpL0 hIlo hIhi rpH2 rpLH
    have hm2 := CKLaneD.chord_mono (f0 := Scalar.P (c.pLo : ℝ)) (f1 := Scalar.P (c.pHi : ℝ))
      (g0 := ((PuLo c : ℚ) : ℝ)) (g1 := ((PuHi c : ℚ) : ℝ)) (Δ := (c.pHi : ℝ) - (c.pLo : ℝ))
      (x := H μ.midpoint - μ.meanEntropy - (c.pLo : ℝ))
      (by linarith) (by linarith) (by linarith) hPLo hPHi
    rw [esig]; exact hch.trans hm2
  -- P lower bound on the deficit side
  have hPs : ((PlS c : ℚ) : ℝ) + 4 * ((H μ.a + H μ.b) / 2 - μ.meanEntropy - (c.sL : ℝ)) ≤
      Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) := by
    have hinc := Scalar.P_increment_lower rsL0 hdef.2 hsL
    have hbr := PlS_le hxc rsL0 (by linarith)
    linarith
  -- the explicit plane
  have rv0 : (0 : ℝ) < (c.v : ℝ) := by exact_mod_cast hv0q
  have rv2 : 2 * (c.v : ℝ) < 1 := by exact_mod_cast hv2
  have hplane := CKLaneD.plane_cost_lower μ rv0 (by linarith : (c.v : ℝ) < 1 / 2)
  have hv1' : (0 : ℝ) < 1 - (c.v : ℝ) := by linarith
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ptOk_sound pv
  have hlogm : Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) =
      Real.log (c.v : ℝ) + Real.log (1 - (c.v : ℝ)) := Real.log_mul rv0.ne' hv1'.ne'
  have rnLo : (0 : ℝ) < ((nLo c : ℚ) : ℝ) := by exact_mod_cast hnLo
  have hnlo : ((nLo c : ℚ) : ℝ) ≤ -Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) := by
    have e : ((nLo c : ℚ) : ℝ) = -(((lHi c.v : ℚ) : ℝ) + ((l1Hi c.v : ℚ) : ℝ)) := by
      unfold nLo; push_cast; ring
    rw [e, hlogm]; linarith
  have hnhi : -Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) ≤ ((nHi c : ℚ) : ℝ) := by
    have e : ((nHi c : ℚ) : ℝ) = -(((lLo c.v : ℚ) : ℝ) + ((l1Lo c.v : ℚ) : ℝ)) := by
      unfold nHi; push_cast; ring
    rw [e, hlogm]; linarith
  have ebase : ((baseK c : ℚ) : ℝ) =
      (1 - 2 * (c.v : ℝ)) ^ 2 / (2 * (c.v : ℝ) * (1 - (c.v : ℝ))) := by
    unfold baseK; push_cast; ring
  have hbase : (0 : ℝ) < ((baseK c : ℚ) : ℝ) := by
    rw [ebase]
    have : (0 : ℝ) < 1 - 2 * (c.v : ℝ) := by linarith
    positivity
  have hnpos : 0 < -Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) := rnLo.trans_le hnlo
  have hK_eq : CKLaneD.planeK (c.v : ℝ) =
      ((baseK c : ℚ) : ℝ) / (-Real.log ((c.v : ℝ) * (1 - (c.v : ℝ)))) := by
    unfold CKLaneD.planeK; rw [ebase, div_div]
  have eKhi : ((Khi c : ℚ) : ℝ) = ((baseK c : ℚ) : ℝ) / ((nLo c : ℚ) : ℝ) := by
    unfold Khi; push_cast; ring
  have eKlo : ((Klo c : ℚ) : ℝ) = ((baseK c : ℚ) : ℝ) / ((nHi c : ℚ) : ℝ) := by
    unfold Klo; push_cast; ring
  have rnHi : (0 : ℝ) < ((nHi c : ℚ) : ℝ) := hnpos.trans_le hnhi
  have hKhi : CKLaneD.planeK (c.v : ℝ) ≤ ((Khi c : ℚ) : ℝ) := by
    rw [hK_eq, eKhi, div_le_div_iff₀ hnpos rnLo]
    exact mul_le_mul_of_nonneg_left hnlo hbase.le
  have hKlo : ((Klo c : ℚ) : ℝ) ≤ CKLaneD.planeK (c.v : ℝ) := by
    rw [hK_eq, eKlo, div_le_div_iff₀ rnHi hnpos]
    exact mul_le_mul_of_nonneg_left hnhi hbase.le
  have hKlo0 : (0 : ℝ) ≤ ((Klo c : ℚ) : ℝ) := by rw [eKlo]; exact div_nonneg hbase.le rnHi.le
  have rHv : (0 : ℝ) ≤ ((Hlo c.v : ℚ) : ℝ) := by exact_mod_cast hHv
  obtain ⟨hvHl, _⟩ := H_bounds pv
  have hvJl := Jl_le pv hlamv
  have hcc : ((ccLo c : ℚ) : ℝ) ≤
      J (c.v : ℝ) + 2 * CKLaneD.planeK (c.v : ℝ) * H (c.v : ℝ) / (1 - 2 * (c.v : ℝ)) := by
    have e : ((ccLo c : ℚ) : ℝ) = ((Jl c.v : ℚ) : ℝ) +
        2 * ((Klo c : ℚ) : ℝ) * ((Hlo c.v : ℚ) : ℝ) / (1 - 2 * (c.v : ℝ)) := by
      unfold ccLo; push_cast; ring
    rw [e]
    have hr : (0 : ℝ) < 1 - 2 * (c.v : ℝ) := by linarith
    have hprod : ((Klo c : ℚ) : ℝ) * ((Hlo c.v : ℚ) : ℝ) ≤ CKLaneD.planeK (c.v : ℝ) * H (c.v : ℝ) :=
      mul_le_mul hKlo hvHl rHv (hKlo0.trans hKlo)
    have hdiv : 2 * ((Klo c : ℚ) : ℝ) * ((Hlo c.v : ℚ) : ℝ) / (1 - 2 * (c.v : ℝ)) ≤
        2 * CKLaneD.planeK (c.v : ℝ) * H (c.v : ℝ) / (1 - 2 * (c.v : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hr.le
      linarith
    linarith
  have hd0 : 0 ≤ μ.b - μ.a := by linarith
  have hcost : ((ccLo c : ℚ) : ℝ) * (μ.b - μ.a) - 2 * ((Khi c : ℚ) : ℝ) * μ.meanEntropy ≤
      μ.cost := by
    have h1 := mul_le_mul_of_nonneg_right hcc hd0
    have h2 := mul_le_mul_of_nonneg_right hKhi hE0.le
    linarith
  -- relaxation algebra
  have rsig : (0 : ℝ) ≤ ((sig c : ℚ) : ℝ) := by exact_mod_cast hsig
  have rgam : (0 : ℝ) ≤ ((gam B c : ℚ) : ℝ) := by exact_mod_cast hgam
  have rfin : (0 : ℝ) ≤ ((finalVal B c : ℚ) : ℝ) := by exact_mod_cast hfin
  have hkapE : ((kap c : ℚ) : ℝ) * ((CKLaneD.EMIN : ℝ) + ((tstar B c : ℚ) : ℝ) *
      ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ))) ≤ ((kap c : ℚ) : ℝ) * μ.meanEntropy := by
    unfold tstar
    split_ifs with hk
    · have rk : (0 : ℝ) ≤ ((kap c : ℚ) : ℝ) := by exact_mod_cast hk
      exact mul_le_mul_of_nonneg_left hE0' rk
    · have rk : ((kap c : ℚ) : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hk))
      exact mul_le_mul_of_nonpos_left hE1' rk
  have hchA : ((Hlo B.alo : ℚ) : ℝ) + ((mua B : ℚ) : ℝ) * (μ.a - ((B.alo : ℚ) : ℝ)) ≤ H μ.a := by
    have hc := CKLaneD.H_chord_lower (lo := ((B.alo : ℚ) : ℝ)) (hi := ((B.ahi : ℚ) : ℝ)) (x := μ.a)
      (HL0 := ((Hlo B.alo : ℚ) : ℝ)) (HL1 := ((Hlo B.ahi : ℚ) : ℝ)) rA0.le ha0 ha1
      (by linarith) HA0l HA1l
    have e : ((mua B : ℚ) : ℝ) =
        (((Hlo B.ahi : ℚ) : ℝ) - ((Hlo B.alo : ℚ) : ℝ)) / (((B.ahi : ℚ) : ℝ) - ((B.alo : ℚ) : ℝ)) := by
      unfold mua; push_cast; ring
    rw [e]; exact hc
  have hchB : ((Hlo B.blo : ℚ) : ℝ) + ((mub B : ℚ) : ℝ) * (μ.b - ((B.blo : ℚ) : ℝ)) ≤ H μ.b := by
    have hc := CKLaneD.H_chord_lower (lo := ((B.blo : ℚ) : ℝ)) (hi := ((B.bhi : ℚ) : ℝ)) (x := μ.b)
      (HL0 := ((Hlo B.blo : ℚ) : ℝ)) (HL1 := ((Hlo B.bhi : ℚ) : ℝ)) rB0.le hb0 hb1
      (by linarith) HB0l HB1l
    have e : ((mub B : ℚ) : ℝ) =
        (((Hlo B.bhi : ℚ) : ℝ) - ((Hlo B.blo : ℚ) : ℝ)) / (((B.bhi : ℚ) : ℝ) - ((B.blo : ℚ) : ℝ)) := by
      unfold mub; push_cast; ring
    rw [e]; exact hc
  have hgamH := mul_le_mul_of_nonneg_left (add_le_add hchA hchB) rgam
  have hsigH := mul_le_mul_of_nonneg_left hHm_tan rsig
  have hcorner : (0 : ℝ) ≤ ((c0 B c : ℚ) : ℝ) + ((ca B c : ℚ) : ℝ) * μ.a +
      ((cb B c : ℚ) : ℝ) * μ.b := by
    have e1 := CKLaneD.min_mul_le (q := ca B c) ha0 ha1
    have e2 := CKLaneD.min_mul_le (q := cb B c) hb0 hb1
    have e : ((finalVal B c : ℚ) : ℝ) = ((c0 B c : ℚ) : ℝ) +
        ((min (ca B c * B.alo) (ca B c * B.ahi) : ℚ) : ℝ) +
        ((min (cb B c * B.blo) (cb B c * B.bhi) : ℚ) : ℝ) := by
      unfold finalVal; push_cast; ring
    linarith
  have egam : ((gam B c : ℚ) : ℝ) = (((kap c : ℚ) : ℝ) * ((tstar B c : ℚ) : ℝ) + 4) / 2 := by
    unfold gam; push_cast; ring
  have ekap : ((kap c : ℚ) : ℝ) = ((sig c : ℚ) : ℝ) - 2 * ((Khi c : ℚ) : ℝ) - 4 := by
    unfold kap; push_cast; ring
  have econst : ((constT c : ℚ) : ℝ) = -((PuLo c : ℚ) : ℝ) + ((sig c : ℚ) : ℝ) * (c.pLo : ℝ) +
      ((PlS c : ℚ) : ℝ) - 4 * (c.sL : ℝ) := by
    unfold constT; push_cast; ring
  have ec0 : ((c0 B c : ℚ) : ℝ) = ((kap c : ℚ) : ℝ) * (CKLaneD.EMIN : ℝ) *
      (1 - ((tstar B c : ℚ) : ℝ)) +
      ((gam B c : ℚ) : ℝ) * (((Hlo B.alo : ℚ) : ℝ) - ((mua B : ℚ) : ℝ) * ((B.alo : ℚ) : ℝ) +
        ((Hlo B.blo : ℚ) : ℝ) - ((mub B : ℚ) : ℝ) * ((B.blo : ℚ) : ℝ)) -
      ((sig c : ℚ) : ℝ) * (((Hhi (mLo B) : ℚ) : ℝ) - ((numM B c : ℚ) : ℝ) * ((mLo B : ℚ) : ℝ)) +
      ((constT c : ℚ) : ℝ) := by
    unfold c0; push_cast; ring
  have eca : ((ca B c : ℚ) : ℝ) = -((ccLo c : ℚ) : ℝ) + ((gam B c : ℚ) : ℝ) * ((mua B : ℚ) : ℝ) -
      ((sig c : ℚ) : ℝ) * ((numM B c : ℚ) : ℝ) / 2 := by
    unfold ca; push_cast; ring
  have ecb : ((cb B c : ℚ) : ℝ) = ((ccLo c : ℚ) : ℝ) + ((gam B c : ℚ) : ℝ) * ((mub B : ℚ) : ℝ) -
      ((sig c : ℚ) : ℝ) * ((numM B c : ℚ) : ℝ) / 2 := by
    unfold cb; push_cast; ring
  rw [ec0, eca, ecb, econst, egam, ekap] at hcorner
  rw [egam, ekap] at hgamH
  rw [ekap] at hkapE
  rw [hm_def] at hsigH hPI hjen
  have hmid2 : μ.midpoint = (μ.a + μ.b) / 2 := rfl
  generalize Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) = PI at hjen hPI
  generalize Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) = PS at hjen hPs
  rw [c_mLo] at hsigH hcorner
  linarith only [hjen, hPI, hPs, hkapE, hgamH, hsigH, hcorner, hcost]

theorem leafOK_of_planeCheck {B : CKLaneD.Box} {c : PC} (h : planeCheck B c = true) : LeafOK B :=
  leafOK_of_semD (planeCheck_sound h)

end CKLaneM05.FE8

#check @CKLaneM05.FE8.planeCheck_sound
#print axioms CKLaneM05.FE8.planeCheck_sound
#print axioms CKLaneM05.FE8.leafOK_of_planeCheck

end


