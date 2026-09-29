-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicJet5ReciprocalLog
-- name    : CK_GeneralCK_Certificates_DyadicJet5ReciprocalLog
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:38:13.610217+00:00
-- url     : https://prove2.me/theorems/544de7c9-8ada-4301-957e-e8dfbcfa99aa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicJet5ReciprocalLog` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicJet5ReciprocalLog` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicJet5ReciprocalLog` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicJet5ReciprocalLog (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicJet5ReciprocalLog.lean)

import Definitions.Def_CK_GeneralCK_Certificates_DyadicJet5Bounds
import Definitions.Def_CK_GeneralCK_Certificates_Jet5ReciprocalLog
import Definitions.Def_GeneralCK_E8_interval_checkers

-- ===== source module GeneralCK.Certificates.DyadicJet5ReciprocalLog =====
section

/-! Fixed-scale interval propagation for reciprocal and logarithmic order-five jets. -/

namespace GeneralCK.Certificates
namespace DyadicJet5Enclosure

open DyadicInterval



































theorem Contains.inv {p : ℕ} {b : DyadicJet5Enclosure p} {a : Jet5} {t : ℝ}
    (hb : b.Contains a t) (hp : 0 < b.d0.lo) : b.inv.Contains a.inv t := by
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  have r1 := recip_sound hp h0
  have r2 := mul_sound r1 r1
  have r3 := mul_sound r2 r1
  have r4 := mul_sound r3 r1
  have r5 := mul_sound r4 r1
  have r6 := mul_sound r5 r1
  have c2 := ofInt_sound p 2
  have c6 := ofInt_sound p 6
  have c8 := ofInt_sound p 8
  have c10 := ofInt_sound p 10
  have c20 := ofInt_sound p 20
  have c24 := ofInt_sound p 24
  have c36 := ofInt_sound p 36
  have c60 := ofInt_sound p 60
  have c90 := ofInt_sound p 90
  have c120 := ofInt_sound p 120
  have c240 := ofInt_sound p 240
  dsimp only [Contains, DyadicJet5Enclosure.inv, Jet5.inv]
  refine ⟨r1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv, pow_two] using mul_sound (neg_sound h1) r2
  · convert sub_sound (mul_sound (mul_sound c2 (mul_sound h1 h1)) r3)
      (mul_sound h2 r2) using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound
      (mul_sound (neg_sound (mul_sound c6 (mul_sound (mul_sound h1 h1) h1))) r4)
      (mul_sound (mul_sound c6 (mul_sound h1 h2)) r3)) (mul_sound h3 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound (add_sound
      (sub_sound (mul_sound (mul_sound c24 (mul_sound (mul_sound (mul_sound h1 h1) h1) h1)) r5)
        (mul_sound (mul_sound c36 (mul_sound (mul_sound h1 h1) h2)) r4))
      (mul_sound (mul_sound c6 (mul_sound h2 h2)) r3))
      (mul_sound (mul_sound c8 (mul_sound h1 h3)) r3)) (mul_sound h4 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring
  · convert sub_sound (add_sound (add_sound
      (sub_sound (sub_sound (add_sound
        (mul_sound (neg_sound (mul_sound c120
          (mul_sound (mul_sound (mul_sound (mul_sound h1 h1) h1) h1) h1))) r6)
        (mul_sound (mul_sound c240 (mul_sound (mul_sound (mul_sound h1 h1) h1) h2)) r5))
        (mul_sound (mul_sound c90 (mul_sound (mul_sound h1 h2) h2)) r4))
        (mul_sound (mul_sound c60 (mul_sound (mul_sound h1 h1) h3)) r4))
      (mul_sound (mul_sound c20 (mul_sound h2 h3)) r3))
      (mul_sound (mul_sound c10 (mul_sound h1 h4)) r3)) (mul_sound h5 r2)
      using 1 <;>
      simp [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.sub_apply] <;> ring


















theorem Contains.log {p : ℕ} {b : DyadicJet5Enclosure p} {l : DyadicInterval p}
    {a : Jet5} {t : ℝ} (hb : b.Contains a t) (hp : 0 < b.d0.lo)
    (hl : l.Contains (Real.log (a.d0 t))) : (b.log l).Contains a.log t := by
  have hr := hb.inv hp
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  rcases hr with ⟨r0,r1,r2,r3,r4,r5⟩
  have c2 := ofInt_sound p 2
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c6 := ofInt_sound p 6
  dsimp only [Contains, DyadicJet5Enclosure.log, Jet5.log]
  exact ⟨hl, mul_sound h1 r0,
    add_sound (mul_sound h2 r0) (mul_sound h1 r1),
    add_sound (add_sound (mul_sound h3 r0) (mul_sound (mul_sound c2 h2) r1))
      (mul_sound h1 r2),
    add_sound (add_sound (add_sound (mul_sound h4 r0) (mul_sound (mul_sound c3 h3) r1))
      (mul_sound (mul_sound c3 h2) r2)) (mul_sound h1 r3),
    add_sound (add_sound (add_sound (add_sound (mul_sound h5 r0)
      (mul_sound (mul_sound c4 h4) r1)) (mul_sound (mul_sound c6 h3) r2))
      (mul_sound (mul_sound c4 h2) r3)) (mul_sound h1 r4)⟩

end DyadicJet5Enclosure
end GeneralCK.Certificates

end


