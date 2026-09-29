-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisDyadicJetKernel
-- name    : CK_GeneralCK_Certificates_E8TAxisDyadicJetKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T09:51:55.750494+00:00
-- url     : https://prove2.me/theorems/6b5b1702-2580-41a2-bfdf-1e83b4c8cb24
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisDyadicJetKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisDyadicJetKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisDyadicJetKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisDyadicJetKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisDyadicJetKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicJet5ReciprocalLog
import Definitions.Def_GeneralCK_E8_interval_checkers

-- ===== source module GeneralCK.Certificates.E8TAxisDyadicJetKernel =====
section

/-!
# Missing dyadic product rule for the E8 order-five replay

The retained C++ `BJ5` evaluator multiplies factorial-normalized jets.  Lean's
`Jet5` uses raw derivatives, so the corresponding enclosure uses the binomial
coefficients in the ordinary Leibniz rule.
-/

namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure

open DyadicInterval




















theorem Contains.mul {p : ℕ} {a b : DyadicJet5Enclosure p} {j k : Jet5} {t : ℝ}
    (ha : a.Contains j t) (hb : b.Contains k t) :
    (a.mul b).Contains (j.mul k) t := by
  rcases ha with ⟨a0,a1,a2,a3,a4,a5⟩
  rcases hb with ⟨b0,b1,b2,b3,b4,b5⟩
  have c2 := ofInt_sound p 2
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c5 := ofInt_sound p 5
  have c6 := ofInt_sound p 6
  have c10 := ofInt_sound p 10
  dsimp only [Contains, DyadicJet5Enclosure.mul, Jet5.mul]
  exact ⟨mul_sound a0 b0,
    add_sound (mul_sound a1 b0) (mul_sound a0 b1),
    add_sound (add_sound (mul_sound a2 b0) (mul_sound (mul_sound c2 a1) b1))
      (mul_sound a0 b2),
    add_sound (add_sound (add_sound (mul_sound a3 b0) (mul_sound (mul_sound c3 a2) b1))
      (mul_sound (mul_sound c3 a1) b2)) (mul_sound a0 b3),
    add_sound (add_sound (add_sound (add_sound (mul_sound a4 b0)
      (mul_sound (mul_sound c4 a3) b1)) (mul_sound (mul_sound c6 a2) b2))
      (mul_sound (mul_sound c4 a1) b3)) (mul_sound a0 b4),
    add_sound (add_sound (add_sound (add_sound (add_sound (mul_sound a5 b0)
      (mul_sound (mul_sound c5 a4) b1)) (mul_sound (mul_sound c10 a3) b2))
      (mul_sound (mul_sound c10 a2) b3)) (mul_sound (mul_sound c5 a1) b4))
      (mul_sound a0 b5)⟩

#print axioms Contains.mul

end DyadicJet5Enclosure
end GeneralCK.Certificates

end


