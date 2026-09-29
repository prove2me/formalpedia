-- Prove2me | Definitions.Def_CK_CKLaneA1_BSCellSound
-- name    : CK_CKLaneA1_BSCellSound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:21:47.768834+00:00
-- url     : https://prove2.me/theorems/8040762a-ab6f-48b6-8573-ea43b11d5714
-- title:
--   Courtade–Kumar proof module `CKLaneA1.BSCellSound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.BSCellSound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.BSCellSound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.BSCellSound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/BSCellSound.lean)

import Definitions.Def_CK_CKLaneA1_BSCell

/-!
# CKLaneA1.BSCellSound — soundness of the both-small cell check (final step)
-/

set_option autoImplicit false

namespace CKLaneA1

open GeneralCK GeneralCK.Correction GeneralCK.Correction.Natural GeneralCK.Correction.HighU
open GeneralCK.Certificates
open GeneralCK.Certificates.Reflection (biasE biasB)

local notation "sc" => (DyadicInterval.scale 64 : ℝ)

theorem mk_of_div {a b : ℤ} {x : ℝ} (ha : (a:ℝ)/sc ≤ x) (hb : x ≤ (b:ℝ)/sc) :
    (Iv.mk a b).Contains x := by
  have hs := SC_pos
  refine ⟨?_, ?_⟩
  · have e : (a:ℝ) = sc * ((a:ℝ)/sc) := by field_simp
    change (a:ℝ) ≤ _; rw [e]; exact mul_le_mul_of_nonneg_left ha hs.le
  · have e : (b:ℝ) = sc * ((b:ℝ)/sc) := by field_simp
    change _ ≤ (b:ℝ); rw [e]; exact mul_le_mul_of_nonneg_left hb hs.le

theorem lo_div_le {I : DI} {x : ℝ} (hI : I.Contains x) : (I.lo:ℝ)/sc ≤ x := by
  rw [div_le_iff₀ SC_pos]; linarith [hI.1]

theorem le_hi_div {I : DI} {x : ℝ} (hI : I.Contains x) : x ≤ (I.hi:ℝ)/sc := by
  rw [le_div_iff₀ SC_pos]; linarith [hI.2]

theorem pt_sub_contains (a : ℤ) : (Iv.pt (SCz - a)).Contains (1 - (a:ℝ)/sc) := by
  have := Iv.pt_contains (SCz - a)
  have hs := SC_pos
  have e : ((SCz - a : ℤ):ℝ) / sc = 1 - (a:ℝ)/sc := by
    rw [show (SCz - a : ℤ) = DyadicInterval.scale 64 - a from rfl]; push_cast; field_simp
  rwa [e] at this

theorem bsFinal_sound {n : ℕ} {L2 : DI} (hL : L2.Contains (Real.log 2)) {a : BSAt} {cd : CData}
    {two : Bool} (hbr : bsBracketOK n L2 two a.IY a.Ylo cd = true) (hf : bsFinal n L2 a cd = true)
    {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) (hSp0 : 0 < a.Sp.lo)
    (hP : a.P.Contains (1 / jn w)) (hOm : a.Om.Contains (w * jn w)) (hW : a.W.Contains w)
    (hU : a.U.Contains u) (hSh : a.Sh.Contains ((w - u)/w)) (hTau : a.Tau.Contains (jn w / jn u))
    (hQu : a.Qu.Contains (qp u / w)) (hQw : a.Qw.Contains (qp w / w))
    (hKh : a.Kh.Contains ((1 / jn w) * (qp u * jn u) / w))
    (hSp : a.Sp.Contains ((1 / jn w) * entropySum u w / w))
    (hQjh : a.Qjh.Contains ((qp u / w) * (w * ((jn w - jn u)/(w - u)))))
    (hNu : a.Nu.Contains (1/(1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))))))
    (hNus : a.Nus.Contains ((1/(1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))))) *
          (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u))))))
    (hsig : 0 ≤ -(jn w / jn u) * (w * ((jn w - jn u)/(w - u))))
    (hY2 : two = true → a.IY.Contains (entropySum u w / (2*(w-u))))
    (hY1 : two = false → (a.Ylo:ℝ)/sc ≤ entropySum u w / (2*(w-u))) :
    0 < actualDetGapCoefficient u w ∧ 0 < m11 u w := by
  have hw0 : 0 < w := hu.trans huw
  have hJu : 0 < jn u := jn_pos hu (by linarith)
  have hJw : 0 < jn w := jn_pos hw0 hw
  have hS := entropySum_pos' hu huw hw
  unfold bsFinal at hf
  simp only [] at hf
  obtain ⟨hq0, hfb0, hg0, hcc0, hmm0⟩ := of_decide_eq_true hf
  obtain ⟨hC0, hC1, heq⟩ := contact_facts hu huw hw
  obtain ⟨hlogs, hc0, hc1, hc2, hlC, hCh⟩ := bsBracket_bounds hL hbr hY2 hY1 hC0 hC1 heq
  obtain ⟨hCI, hEI, hBI, hLI⟩ := cAtoms_of_bounds (n := n) hL hlogs hc0 hc1 hc2 hq0 hC0 hC1 hlC hCh
  have hFoC : (cFoC (cLoC n cd) (cE n L2 cd) (cB n L2 cd) (cC cd)).Contains (foc (contact u w)) := by
    unfold cFoC foc
    exact DyadicInterval.add_sound hLI (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound Iv.two_contains hEI)
      (DyadicInterval.recip_sound hfb0 (DyadicInterval.mul_sound
        (DyadicInterval.sub_sound Iv.one_contains (DyadicInterval.mul_sound hCI hCI)) hBI)))
  have hF : ((cC cd).mul (cFoC (cLoC n cd) (cE n L2 cd) (cB n L2 cd) (cC cd))).Contains
      (Fs (contact u w)) := by
    rw [Fs_eq_foc hC0 hC1]
    exact DyadicInterval.mul_sound hCI hFoC
  have hrSp := DyadicInterval.recip_sound hSp0 hSp
  have hSpv : (1 / jn w) * entropySum u w / w ≠ 0 :=
    ne_of_gt (div_pos (mul_pos (one_div_pos.mpr hJw) hS) hw0)
  have hS' : entropySum u w ≠ 0 := hS.ne'
  have hJw' : jn w ≠ 0 := hJw.ne'
  have hw0' : w ≠ 0 := hw0.ne'
  have hRh : ((cFoC (cLoC n cd) (cE n L2 cd) (cB n L2 cd) (cC cd)).mul
      ((Iv.two.mul (cE n L2 cd)).mul a.Sp.recip)).Contains (w * regularFsGap u w / (1 / jn w)) := by
    have e : w * regularFsGap u w / (1 / jn w) =
        foc (contact u w) * ((2 * biasE (contact u w)) * ((1 / jn w) * entropySum u w / w)⁻¹) := by
      rw [regularFsGap_eq_foc hu huw hw]
      field_simp <;> ring
    rw [e]
    exact DyadicInterval.mul_sound hFoC (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound Iv.two_contains hEI) hrSp)
  have hGI : (cG (cE n L2 cd) (cB n L2 cd) (cC cd)).Contains (gW (contact u w)) := by
    unfold cG gW
    open DyadicInterval in
    exact mul_sound (mul_sound (Iv.ofInt_contains 8) (mul_sound (mul_sound (mul_sound hEI hEI) hEI)
      (sub_sound (mul_sound Iv.two_contains hBI) (mul_sound hCI hCI))))
      (recip_sound hg0 (mul_sound (mul_sound (sub_sound Iv.one_contains (mul_sound hCI hCI))
        (sub_sound Iv.one_contains (mul_sound hCI hCI))) (mul_sound (mul_sound hBI hBI) hBI)))
  have hWh1 : ((cG (cE n L2 cd) (cB n L2 cd) (cC cd)).mul a.Sp.recip).Contains
      (w * regularWeight u w / (1 / jn w)) := by
    have e : w * regularWeight u w / (1 / jn w) =
        gW (contact u w) * ((1 / jn w) * entropySum u w / w)⁻¹ := by
      rw [regularWeight_eq_gW hu huw hw]; field_simp <;> ring
    rw [e]; exact DyadicInterval.mul_sound hGI hrSp
  have hWh2 : ((cG (cE n L2 cd) (cB n L2 cd) (cC cd)).mul a.Sp.recip).Contains
      (w * weight u w / (1 / jn w)) := by
    have e : w * weight u w / (1 / jn w) =
        gW (contact u w) * ((1 / jn w) * entropySum u w / w)⁻¹ := by
      rw [weight_eq_gW hu huw hw]; field_simp <;> ring
    rw [e]; exact DyadicInterval.mul_sound hGI hrSp
  have hHh : (Iv.one.sub (Iv.two.mul a.U)).Contains (1 - 2*u) :=
    DyadicInterval.sub_sound Iv.one_contains (DyadicInterval.mul_sound Iv.two_contains hU)
  have hHms : ((Iv.one.sub (Iv.two.mul a.U)).sub (a.W.mul a.Sh)).Contains
      (1 - 2*u - w*((w - u)/w)) :=
    DyadicInterval.sub_sound hHh (DyadicInterval.mul_sound hW hSh)
  have hσne : 1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))) ≠ 0 := by linarith
  have hcc := bsCIv_contains hTau hP hOm hQu hQw hSh hSp hKh hQjh hNu hNus hRh hWh1 hHh hHms hSp0
  rw [← bsC_identity hu huw hw hσne] at hcc
  have hmm := bsMIv_contains hTau hP hQu hSh hSp hKh hF hWh2 hHh hSp0
  have hccpos := Iv.contains_pos hcc hcc0
  have hmmpos := Iv.contains_pos hmm hmm0
  have hnutau : 0 < 1/(1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u))))) * (jn w / jn u) := by
    have : 0 < 1 + (-(jn w / jn u) * (w * ((jn w - jn u)/(w - u)))) := by linarith
    exact mul_pos (one_div_pos.mpr this) (div_pos hJw hJu)
  refine ⟨(mul_pos_iff_of_pos_left hnutau).mp hccpos, ?_⟩
  rw [bsM_identity hu huw hw]
  exact mul_pos hw0 hmmpos

#print axioms bsFinal_sound

end CKLaneA1


