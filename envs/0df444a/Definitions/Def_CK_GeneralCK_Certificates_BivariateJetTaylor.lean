-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_BivariateJetTaylor
-- name    : CK_GeneralCK_Certificates_BivariateJetTaylor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:32:04.271251+00:00
-- url     : https://prove2.me/theorems/de43a8c4-7203-400e-adf7-8235d06d510a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.BivariateJetTaylor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.BivariateJetTaylor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.BivariateJetTaylor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.BivariateJetTaylor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/BivariateJetTaylor.lean)

import Definitions.Def_CK_GeneralCK_Certificates_BivariateJetBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Certificates
open Set JetBounds

namespace JetBounds.Interval



theorem magnitude_nonneg (i : Interval) : 0 ≤ i.magnitude :=
  (abs_nonneg i.lo).trans (le_max_left _ _)

theorem Contains.abs_le_magnitude {i : Interval} {x : ℝ} (hx : i.Contains x) :
    |x| ≤ i.magnitude := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le i.lo).trans hx.1)
  · exact hx.2.trans ((le_abs_self i.hi).trans (le_max_right _ _))

end JetBounds.Interval

namespace BivariateJetEnclosure







theorem taylor_lower {center whole : BivariateJetEnclosure} {j : BivariateJet2}
    {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz) :
    taylorLower center whole ra rz≤j.value 1 := by
  have hA := hc.2.1.abs_le_magnitude
  have hZ := hc.2.2.1.abs_le_magnitude
  have hAterm : |j.firstA 0*da|≤center.firstA.magnitude*ra := by
    rw [abs_mul]
    exact mul_le_mul hA hda (abs_nonneg _) center.firstA.magnitude_nonneg
  have hZterm : |j.firstZ 0*dz|≤center.firstZ.magnitude*rz := by
    rw [abs_mul]
    exact mul_le_mul hZ hdz (abs_nonneg _) center.firstZ.magnitude_nonneg
  have hslope : -(center.firstA.magnitude*ra+center.firstZ.magnitude*rz)≤
      (j.projection da dz).first 0 := by
    have h := (abs_add_le (j.firstA 0*da) (j.firstZ 0*dz)).trans (add_le_add hAterm hZterm)
    exact (abs_le.mp h).1
  exact taylor_rectangle_lower
    (fun t ht => (hs t ht).1)
    (fun t ht => (hs t ⟨ht.1.le,ht.2.le⟩).2)
    hc.1.1 hslope hra hrz hda hdz
    whole.secondAA.magnitude_nonneg whole.secondAZ.magnitude_nonneg whole.secondZZ.magnitude_nonneg
    (fun _ _ => rfl)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.1.abs_le_magnitude)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.2.1.abs_le_magnitude)
    (fun t ht => (hw t ⟨ht.1.le,ht.2.le⟩).2.2.2.2.2.abs_le_magnitude)

theorem value_pos_of_taylor {center whole : BivariateJetEnclosure} {j : BivariateJet2}
    {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (hcheck : 0<taylorLower center whole ra rz) : 0<j.value 1 :=
  hcheck.trans_le (taylor_lower hs hc hw hra hrz hda hdz)

end BivariateJetEnclosure
end GeneralCK.Certificates


