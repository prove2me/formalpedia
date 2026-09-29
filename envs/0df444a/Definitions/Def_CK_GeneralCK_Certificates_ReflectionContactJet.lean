-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionContactJet
-- name    : CK_GeneralCK_Certificates_ReflectionContactJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:03:29.413088+00:00
-- url     : https://prove2.me/theorems/15a79ee6-84f2-421b-9f5a-34f6d9bba983
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionContactJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionContactJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionContactJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionContactJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionContactJet.lean)

import Definitions.Def_CK_GeneralCK_ReflectionContactInverse
import Definitions.Def_CK_GeneralCK_Certificates_Jet2Composition
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates
open Set Filter
open scoped Topology









theorem reflectionContactJet_soundAt {y : ℝ} (hy : 0 < y) :
    reflectionContactJet.SoundAt y := by
  refine ⟨Reflection.hasDerivAt_biasContact_inv hy, ?_⟩
  have heq : reflectionContactJet.first =ᶠ[𝓝 y] deriv Reflection.biasContact := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (Reflection.hasDerivAt_biasContact_inv ht).deriv.symm
  exact (Reflection.hasDerivAt_deriv_biasContact hy).congr_of_eventuallyEq heq

theorem reflectionContactJet_soundOn : reflectionContactJet.SoundOn (Ioi 0) :=
  fun _ hy => reflectionContactJet_soundAt hy

/-- A positive sound input jet can be passed through the implicit contact map. -/
theorem reflectionContactJet_comp_soundOn {j : Jet2} {s : Set ℝ}
    (hj : j.SoundOn s) (hpos : ∀ t ∈ s, 0 < j.value t) :
    (reflectionContactJet.comp j).SoundOn s :=
  reflectionContactJet_soundOn.comp hj hpos

theorem reflectionContactJet_comp_soundAt {j : Jet2} {t : ℝ}
    (hj : j.SoundAt t) (hpos : 0 < j.value t) :
    (reflectionContactJet.comp j).SoundAt t :=
  (reflectionContactJet_soundAt hpos).comp hj

end GeneralCK.Certificates


