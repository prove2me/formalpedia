-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_BivariateJetBounds
-- name    : CK_GeneralCK_Certificates_BivariateJetBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:27:21.810879+00:00
-- url     : https://prove2.me/theorems/5066c2a6-3a55-4fdb-9e87-b520aa9ddb87
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.BivariateJetBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.BivariateJetBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.BivariateJetBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.BivariateJetBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/BivariateJetBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_BivariateJet2
import Definitions.Def_CK_GeneralCK_Certificates_Jet2Bounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Certificates
open JetBounds










namespace BivariateJetEnclosure









def const (c : ℝ) : BivariateJetEnclosure :=
  ⟨.point c,.point 0,.point 0,.point 0,.point 0,.point 0⟩

def add (b c : BivariateJetEnclosure) : BivariateJetEnclosure :=
  ⟨b.value.add c.value,b.firstA.add c.firstA,b.firstZ.add c.firstZ,
    b.secondAA.add c.secondAA,b.secondAZ.add c.secondAZ,b.secondZZ.add c.secondZZ⟩

def neg (b : BivariateJetEnclosure) : BivariateJetEnclosure :=
  ⟨b.value.neg,b.firstA.neg,b.firstZ.neg,b.secondAA.neg,b.secondAZ.neg,b.secondZZ.neg⟩

noncomputable def mul (b c : BivariateJetEnclosure) : BivariateJetEnclosure :=
  ⟨b.value.mul c.value,
    (b.firstA.mul c.value).add (b.value.mul c.firstA),
    (b.firstZ.mul c.value).add (b.value.mul c.firstZ),
    ((b.secondAA.mul c.value).add (((Interval.point 2).mul b.firstA).mul c.firstA)).add
      (b.value.mul c.secondAA),
    (((b.secondAZ.mul c.value).add (b.firstA.mul c.firstZ)).add (b.firstZ.mul c.firstA)).add
      (b.value.mul c.secondAZ),
    ((b.secondZZ.mul c.value).add (((Interval.point 2).mul b.firstZ).mul c.firstZ)).add
      (b.value.mul c.secondZZ)⟩

/-- The outer Jet2 enclosure is evaluated at the actual inner value. -/
noncomputable def outerCompose (outer : JetEnclosure) (b : BivariateJetEnclosure) :
    BivariateJetEnclosure :=
  ⟨outer.value,outer.first.mul b.firstA,outer.first.mul b.firstZ,
    ((outer.second.mul b.firstA).mul b.firstA).add (outer.first.mul b.secondAA),
    ((outer.second.mul b.firstA).mul b.firstZ).add (outer.first.mul b.secondAZ),
    ((outer.second.mul b.firstZ).mul b.firstZ).add (outer.first.mul b.secondZZ)⟩

theorem contains_const (c t : ℝ) : (const c).Contains (BivariateJet2.const c) t := by
  exact ⟨Interval.contains_point _,Interval.contains_point _,Interval.contains_point _,
    Interval.contains_point _,Interval.contains_point _,Interval.contains_point _⟩

theorem Contains.add {b c : BivariateJetEnclosure} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.add c).Contains (j.add k) t :=
  ⟨hj.1.add hk.1,hj.2.1.add hk.2.1,hj.2.2.1.add hk.2.2.1,
    hj.2.2.2.1.add hk.2.2.2.1,hj.2.2.2.2.1.add hk.2.2.2.2.1,
    hj.2.2.2.2.2.add hk.2.2.2.2.2⟩

theorem Contains.neg {b : BivariateJetEnclosure} {j : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) : b.neg.Contains j.neg t :=
  ⟨hj.1.neg,hj.2.1.neg,hj.2.2.1.neg,hj.2.2.2.1.neg,hj.2.2.2.2.1.neg,hj.2.2.2.2.2.neg⟩

theorem Contains.mul {b c : BivariateJetEnclosure} {j k : BivariateJet2} {t : ℝ}
    (hj : b.Contains j t) (hk : c.Contains k t) : (b.mul c).Contains (j.mul k) t := by
  have htwo := Interval.contains_point (2:ℝ)
  exact ⟨hj.1.mul hk.1,(hj.2.1.mul hk.1).add (hj.1.mul hk.2.1),
    (hj.2.2.1.mul hk.1).add (hj.1.mul hk.2.2.1),
    ((hj.2.2.2.1.mul hk.1).add ((htwo.mul hj.2.1).mul hk.2.1)).add (hj.1.mul hk.2.2.2.1),
    (((hj.2.2.2.2.1.mul hk.1).add (hj.2.1.mul hk.2.2.1)).add
      (hj.2.2.1.mul hk.2.1)).add (hj.1.mul hk.2.2.2.2.1),
    ((hj.2.2.2.2.2.mul hk.1).add ((htwo.mul hj.2.2.1).mul hk.2.2.1)).add
      (hj.1.mul hk.2.2.2.2.2)⟩

theorem Contains.outerCompose {outer : JetEnclosure} {b : BivariateJetEnclosure}
    {f : Jet2} {j : BivariateJet2} {t : ℝ} (hf : outer.Contains f (j.value t))
    (hj : b.Contains j t) : (outerCompose outer b).Contains (BivariateJet2.outerCompose f j) t := by
  exact ⟨hf.1,hf.2.1.mul hj.2.1,hf.2.1.mul hj.2.2.1,
    by simpa only [BivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.1).mul hj.2.1).add (hf.2.1.mul hj.2.2.2.1),
    ((hf.2.2.mul hj.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.1),
    by simpa only [BivariateJetEnclosure.outerCompose,BivariateJet2.outerCompose,pow_two,mul_assoc] using
      ((hf.2.2.mul hj.2.2.1).mul hj.2.2.1).add (hf.2.1.mul hj.2.2.2.2.2)⟩

end BivariateJetEnclosure
end GeneralCK.Certificates


