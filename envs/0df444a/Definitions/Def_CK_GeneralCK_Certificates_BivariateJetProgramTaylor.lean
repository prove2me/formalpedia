-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_BivariateJetProgramTaylor
-- name    : CK_GeneralCK_Certificates_BivariateJetProgramTaylor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:39:21.860715+00:00
-- url     : https://prove2.me/theorems/c1555a21-222e-418e-83f7-f9e125f876fc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.BivariateJetProgramTaylor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.BivariateJetProgramTaylor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.BivariateJetProgramTaylor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.BivariateJetProgramTaylor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/BivariateJetProgramTaylor.lean)

import Definitions.Def_CK_GeneralCK_Certificates_BivariateJetProgram
import Definitions.Def_CK_GeneralCK_Certificates_BivariateJetTaylor
import Definitions.Def_CK_GeneralCK_Certificates_JetProgramTaylor

namespace GeneralCK.Certificates
open Set

namespace DyadicBivariateJetEnclosure

theorem contains_affineA_zero {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) :
    (coordinateA value).Contains (BivariateJet2.affineA c x) 0 := by
  apply contains_coordinateA
  simpa using hc

theorem contains_affineZ_zero {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) :
    (coordinateZ value).Contains (BivariateJet2.affineZ c x) 0 := by
  apply contains_coordinateZ
  simpa using hc

theorem containsOn_affineA {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) (hx : value.Contains x) :
    (coordinateA value).ContainsOn (BivariateJet2.affineA c x) (Icc (0:ℝ) 1) := by
  intro t ht
  exact contains_coordinateA (DyadicInterval.contains_segment hc hx ht)

theorem containsOn_affineZ {p : ℕ} {value : DyadicInterval p} {c x : ℝ}
    (hc : value.Contains c) (hx : value.Contains x) :
    (coordinateZ value).ContainsOn (BivariateJet2.affineZ c x) (Icc (0:ℝ) 1) := by
  intro t ht
  exact contains_coordinateZ (DyadicInterval.contains_segment hc hx ht)

/-- Convert separately checked coordinate enclosures to the real Taylor rule.
The center and uniform enclosures may use different dyadic precisions. -/
theorem value_pos_of_separate_taylor {p q : ℕ}
    {center : DyadicBivariateJetEnclosure p} {whole : DyadicBivariateJetEnclosure q}
    {j : BivariateJet2} {da dz ra rz : ℝ}
    (hs : j.DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hc : center.Contains j 0) (hw : whole.ContainsOn j (Icc (0:ℝ) 1))
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower center.toReal whole.toReal ra rz) :
    0<j.value 1 :=
  BivariateJetEnclosure.value_pos_of_taylor hs (contains_toReal_iff.mpr hc)
    (containsOn_toReal_iff.mpr hw) hra hrz hda hdz ht

end DyadicBivariateJetEnclosure

namespace BivariateJetProgram

/-- Accepted programs of exactly the same witness-free shape prove positivity
of their actual output. Nonlinear derivative domains follow from the checker;
the only soundness premises concern the initial affine/constant inputs. -/
theorem value_pos_of_checked_taylor {p q : ℕ}
    (center : List (Instruction p)) (whole : List (Instruction q))
    {centerInputs : List (DyadicBivariateJetEnclosure p)}
    {wholeInputs : List (DyadicBivariateJetEnclosure q)} {jets : List BivariateJet2}
    (i : ℕ) {da dz ra rz : ℝ}
    (hshape : shapes center=shapes whole)
    (hc : RegistersContain centerInputs jets 0)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, RegistersContain wholeInputs jets t)
    (hs : ∀ i, (jets.getD i zeroJet).DirectionalSoundOn da dz (Icc (0:ℝ) 1))
    (hcc : check center centerInputs=true) (hwc : check whole wholeInputs=true)
    (hra : 0≤ra) (hrz : 0≤rz) (hda : |da|≤ra) (hdz : |dz|≤rz)
    (ht : 0<BivariateJetEnclosure.taylorLower
      ((finalBoxes center centerInputs).getD i (zeroBox p)).toReal
      ((finalBoxes whole wholeInputs).getD i (zeroBox q)).toReal ra rz) :
    0<((finalJets whole jets).getD i zeroJet).value 1 := by
  have heq := finalJets_eq_of_shapes_eq hshape jets
  have hcenter := (check_encloses center hc hcc).2 i
  rw [heq] at hcenter
  exact DyadicBivariateJetEnclosure.value_pos_of_separate_taylor
    (check_preserves_soundOn whole hw hs hwc i) hcenter
    (fun t ht => (check_encloses whole (hw t ht) hwc).2 i) hra hrz hda hdz ht

end BivariateJetProgram
end GeneralCK.Certificates


