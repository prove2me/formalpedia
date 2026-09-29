-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_RegularContactJet
-- name    : CK_GeneralCK_Certificates_RegularContactJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:01:34.564269+00:00
-- url     : https://prove2.me/theorems/70bdeb2a-2d47-410e-85f1-cc41979f0a91
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.RegularContactJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.RegularContactJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.RegularContactJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.RegularContactJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/RegularContactJet.lean)

import Definitions.Def_CK_GeneralCK_ReflectionRegularContact
import Definitions.Def_CK_GeneralCK_Certificates_Jet2Composition

-- ===== source module GeneralCK.Certificates.RegularContactJet =====
section

namespace GeneralCK.Certificates
open GeneralCK.Reflection

noncomputable def regularContactJet : Jet2 :=
  ⟨regularContact,regularContactFirst,regularContactSecond⟩

theorem regularContactJet_soundOn (s : Set ℝ) : regularContactJet.SoundOn s :=
  fun t _ => ⟨hasDerivAt_regularContact t,hasDerivAt_regularContactFirst t⟩

theorem regularContactJet_comp_soundOn {j : Jet2} {s : Set ℝ} (hj : j.SoundOn s) :
    (regularContactJet.comp j).SoundOn s :=
  (regularContactJet_soundOn Set.univ).comp hj (fun _ _ => Set.mem_univ _)

end GeneralCK.Certificates

end


