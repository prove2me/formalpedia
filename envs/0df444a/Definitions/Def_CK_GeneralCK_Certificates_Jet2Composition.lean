-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Jet2Composition
-- name    : CK_GeneralCK_Certificates_Jet2Composition
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:16:52.600441+00:00
-- url     : https://prove2.me/theorems/c3d87d3a-35c6-429f-ba95-0f4a527e23f5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Jet2Composition` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Jet2Composition` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Jet2Composition` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Jet2Composition (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Jet2Composition.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet2
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Certificates.Jet2







theorem SoundAt.comp {j k : Jet2} {t : ℝ} (hj : j.SoundAt (k.value t))
    (hk : k.SoundAt t) : (j.comp k).SoundAt t := by
  refine ⟨hj.1.comp t hk.1, ?_⟩
  have hh := (hj.2.comp t hk.1).mul hk.2
  convert! hh using 1
  simp only [Jet2.comp, Function.comp_apply]
  ring

theorem SoundOn.comp {j k : Jet2} {s u : Set ℝ} (hj : j.SoundOn u)
    (hk : k.SoundOn s) (hmap : Set.MapsTo k.value s u) : (j.comp k).SoundOn s :=
  fun t ht => (hj (k.value t) (hmap ht)).comp (hk t ht)

end GeneralCK.Certificates.Jet2


