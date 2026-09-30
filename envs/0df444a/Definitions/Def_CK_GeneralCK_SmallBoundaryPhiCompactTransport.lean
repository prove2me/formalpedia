-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiCompactTransport
-- name    : CK_GeneralCK_SmallBoundaryPhiCompactTransport
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:41:23.378978+00:00
-- url     : https://prove2.me/theorems/a74570dc-a26f-45d3-9ac0-522e6cf53380
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiCompactTransport` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiCompactTransport` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiCompactTransport` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiCompactTransport (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiCompactTransport.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiContactCertificate

-- ===== source module GeneralCK.SmallBoundaryPhiCompactTransport =====
section

/-! A one-dimensional certificate interface for the exact compact contact core.
The low-contact tail is not part of this module. -/

namespace GeneralCK.SmallBoundaryPhiSchur

open Set SmallMeanPhiCutoff

set_option maxHeartbeats 800000

noncomputable def compactDelta : ℝ := 1 / 10000000000000000000000

noncomputable def compactComparisonPotential (t : ℝ) : ℝ :=
  naturalA t - (1/10)*Real.log (H t/(1-2*t))

structure CompactScalarBounds (δ : ℝ) : Prop where
  lowerA : ∀ t, δ ≤ t → t ≤ retainedCutoff → 99/100 ≤ naturalA t
  upperA : ∀ t, δ ≤ t → t ≤ retainedCutoff → naturalA t ≤ 6/5
  upperK : ∀ t, δ ≤ t → t ≤ retainedCutoff → naturalK t ≤ 6/5
  defect : ∀ t, δ ≤ t → t ≤ retainedCutoff → naturalA t-naturalK t ≤ t/5
  comparison : AntitoneOn compactComparisonPotential (Icc δ retainedCutoff)

theorem contactCore_radius_upper {δ q v s : ℝ} (hδ : 0 < δ)
    (hp : (q,v,s) ∈ contactCore δ) : s ≤ 1-2*v := by
  have hq : 0 < q := hδ.trans_le hp.1
  have hv : 0 < v := hq.trans_le hp.2.1
  have hv' : v < 1/2 := by
    have hh := hp.2.2.1
    dsimp [retainedCutoff] at hh
    linarith
  have hH : H q ≤ H v := H_strictMonoOn.monotoneOn
    ⟨hq.le,(hp.2.1.trans_lt hv').le⟩ ⟨hv.le,hv'.le⟩ hp.2.1
  have hHv : 0 < H v := H_pos hv (by linarith)
  apply (mul_le_mul_iff_left₀ hHv).mp
  calc
    s*H v = H q*(1-2*v) := hp.2.2.2.2.2
    _ ≤ H v*(1-2*v) := mul_le_mul_of_nonneg_right hH (by linarith)
    _ = (1-2*v)*H v := by ring

theorem compact_comparison_increment_bound {δ q v s : ℝ}
    (hδ : 0 < δ) (hb : CompactScalarBounds δ) (hp : (q,v,s) ∈ contactCore δ) :
    naturalA v-naturalA q ≤ (1-s)/9 := by
  have hq : 0 < q := hδ.trans_le hp.1
  have hv : 0 < v := hq.trans_le hp.2.1
  have hv' : v < 1/2 := by
    have hh := hp.2.2.1
    dsimp [retainedCutoff] at hh
    linarith
  have hq' : q < 1/2 := hp.2.1.trans_lt hv'
  have hs9 : 9/10 ≤ s := by
    have hh := hp.2.2.2.1
    dsimp [retainedCutoff] at hh
    linarith
  have hs : 0 < s := by linarith
  have hs1 : s ≤ 1 := hp.2.2.2.2.1
  have hHq : 0 < H q := H_pos hq (by linarith)
  have hHv : 0 < H v := H_pos hv (by linarith)
  have heq : s*H v=H q*(1-2*v) := hp.2.2.2.2.2
  have hratio : (H v/(1-2*v))/(H q/(1-2*q))=(1-2*q)/s := by
    apply (div_eq_iff (ne_of_gt (div_pos hHq (by linarith)))).mpr
    apply (div_eq_iff (by linarith : 1-2*v ≠ 0)).mpr
    field_simp [hs.ne', show 1-2*q ≠ 0 by linarith]
    nlinarith only [heq]
  have hant := hb.comparison ⟨hp.1,hp.2.1.trans hp.2.2.1⟩
    ⟨hp.1.trans hp.2.1,hp.2.2.1⟩ hp.2.1
  dsimp [compactComparisonPotential] at hant
  have hld : Real.log (H v/(1-2*v))-Real.log (H q/(1-2*q)) =
      Real.log ((1-2*q)/s) := by
    rw [← Real.log_div (ne_of_gt (div_pos hHv (by linarith)))
      (ne_of_gt (div_pos hHq (by linarith))), hratio]
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1-2*q) hs)
  have hinc : naturalA v-naturalA q ≤ (1/10)*(((1-2*q)/s)-1) := by
    linarith only [hant,hld,hlog]
  have hquot : (1/10)*(((1-2*q)/s)-1) ≤ (1-s)/(10*s) := by
    field_simp [hs.ne']
    nlinarith
  have hquot' : (1-s)/(10*s) ≤ (1-s)/9 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith [mul_nonneg (show 0 ≤ 10*s-9 by linarith) (show 0 ≤ 1-s by linarith)]
  exact hinc.trans (hquot.trans hquot')

theorem contactDeterminant_nonneg_of_compactScalarBounds {δ q v s : ℝ}
    (hδ : 0 < δ) (hb : CompactScalarBounds δ) (hp : (q,v,s) ∈ contactCore δ) :
    0 ≤ contactDeterminant s q v := by
  have hs9 : 9/10 ≤ s := by
    have hh := hp.2.2.2.1
    dsimp [retainedCutoff] at hh
    linarith
  have hs : 0 < s := by linarith
  have hs1 : s ≤ 1 := hp.2.2.2.2.1
  have haLo := hb.lowerA v (hp.1.trans hp.2.1) hp.2.2.1
  have haHi := hb.upperA v (hp.1.trans hp.2.1) hp.2.2.1
  have hkHi := hb.upperK q hp.1 (hp.2.1.trans hp.2.2.1)
  have hdef := hb.defect q hp.1 (hp.2.1.trans hp.2.2.1)
  have hinc := compact_comparison_increment_bound hδ hb hp
  have hqm : 2*q ≤ 1-s := by linarith [contactCore_radius_upper hδ hp, hp.2.1]
  have hdiff : (701/900)*(1-s) ≤ naturalK q-s*naturalA v := by
    have ha := mul_le_mul_of_nonneg_left haLo (show 0 ≤ 1-s by linarith)
    nlinarith only [ha,hinc,hdef,hqm]
  have hk0 : 0 ≤ naturalK q := by
    have hsa : 0 ≤ s*naturalA v := mul_nonneg hs.le (by linarith)
    have ht : 0 ≤ (701/900 : ℝ)*(1-s) := mul_nonneg (by norm_num) (by linarith)
    linarith only [hdiff,hsa,ht]
  have hprod : naturalA v*naturalK q ≤ 36/25 := by
    have ht := mul_le_mul haHi hkHi hk0 (by norm_num : (0:ℝ) ≤ 6/5)
    norm_num at ht
    exact ht
  have hgood := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 4*s by positivity)
  have hbad := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 1-s^2 by nlinarith)
  have hmargin : 0 ≤ 4*s*((701/900)*(1-s))-(1-s^2)*(36/25) := by
    have he : 4*s*((701/900)*(1-s))-(1-s^2)*(36/25) =
        (1-s)*((377/225)*s-36/25) := by ring
    rw [he]
    apply mul_nonneg (by linarith)
    linarith
  dsimp [contactDeterminant]
  nlinarith only [hgood,hbad,hmargin]

theorem compactContactOwner_of_scalarBounds {δ : ℝ}
    (hδ : 0 < δ) (hb : CompactScalarBounds δ) : CompactContactOwner δ := by
  intro p hp
  exact contactDeterminant_nonneg_of_compactScalarBounds hδ hb hp

#print axioms contactCore_radius_upper
#print axioms compact_comparison_increment_bound
#print axioms contactDeterminant_nonneg_of_compactScalarBounds
#print axioms compactContactOwner_of_scalarBounds

end GeneralCK.SmallBoundaryPhiSchur

end


