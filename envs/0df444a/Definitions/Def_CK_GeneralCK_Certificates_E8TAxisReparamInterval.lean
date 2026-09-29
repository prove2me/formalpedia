-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisReparamInterval
-- name    : CK_GeneralCK_Certificates_E8TAxisReparamInterval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:34:55.735596+00:00
-- url     : https://prove2.me/theorems/118bae97-689b-4ffe-80d9-2d190c098a29
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisReparamInterval` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisReparamInterval` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisReparamInterval` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisReparamInterval (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisReparamInterval.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisDyadicJetKernel
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisReparamJet5
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet

-- ===== source module GeneralCK.Certificates.E8TAxisReparamInterval =====
section

/-! Outward-rounded replay of the historical `qdata5` recurrence. -/

namespace GeneralCK.Certificates.E8TAxisReparamInterval

open DyadicInterval E8TAxisReparamJet5





theorem powI_sound {p : ℕ} {x : DyadicInterval p} {r : ℝ}
    (hx : x.Contains r) (n : ℕ) : (powI x n).Contains (r ^ n) := by
  induction n with
  | zero => simpa [powI] using ofInt_sound p 1
  | succ n ih => simpa [powI, pow_succ] using mul_sound ih hx









theorem eval_sound {p : ℕ} {x y : DyadicJet5Enclosure p}
    {jx jy : Jet5} {a : ℝ}
    (hx : x.Contains jx a) (hy : y.Contains jy a) (hp : 0 < y.d1.lo) :
    (eval x y).Contains (qdata5 jx jy) a := by
  rcases hx with ⟨hx0,hx1,hx2,hx3,hx4,hx5⟩
  rcases hy with ⟨hy0,hy1,hy2,hy3,hy4,hy5⟩
  have hr := recip_sound hp hy1
  dsimp only [DyadicJet5Enclosure.Contains, eval, qdata5]
  refine ⟨hx0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound hx1 hr)
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (sub_sound (mul_sound hy1 hx2) (mul_sound hy2 hx1)) (powI_sound hr 3))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (add_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 2) hx3) (mul_sound (mul_sound (mul_sound (ofInt_sound p 3) hy1) hy2) hx2)) (mul_sound (mul_sound hy1 hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 3) (powI_sound hy2 2)) hx1)) (powI_sound hr 5))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (sub_sound (add_sound (add_sound (sub_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 3) hx4) (mul_sound (mul_sound (mul_sound (ofInt_sound p 6) (powI_sound hy1 2)) hy2) hx3)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 4) (powI_sound hy1 2)) hy3) hx2)) (mul_sound (mul_sound (powI_sound hy1 2) hy4) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 15) hy1) (powI_sound hy2 2)) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) hy1) hy2) hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 15) (powI_sound hy2 3)) hx1)) (powI_sound hr 7))
  · simpa only [div_eq_mul_inv, inv_pow, Int.cast_ofNat] using (mul_sound (add_sound (sub_sound (sub_sound (add_sound (add_sound (add_sound (add_sound (sub_sound (sub_sound (sub_sound (sub_sound (mul_sound (powI_sound hy1 4) hx5) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 3)) hy2) hx4)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 3)) hy3) hx3)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 5) (powI_sound hy1 3)) hy4) hx2)) (mul_sound (mul_sound (powI_sound hy1 3) hy5) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 45) (powI_sound hy1 2)) (powI_sound hy2 2)) hx3)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 60) (powI_sound hy1 2)) hy2) hy3) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 15) (powI_sound hy1 2)) hy2) hy4) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 10) (powI_sound hy1 2)) (powI_sound hy3 2)) hx1)) (mul_sound (mul_sound (mul_sound (ofInt_sound p 105) hy1) (powI_sound hy2 3)) hx2)) (mul_sound (mul_sound (mul_sound (mul_sound (ofInt_sound p 105) hy1) (powI_sound hy2 2)) hy3) hx1)) (mul_sound (mul_sound (ofInt_sound p 105) (powI_sound hy2 4)) hx1)) (powI_sound hr 9))

theorem contains_of_eqAt {p : ℕ} {x : DyadicJet5Enclosure p}
    {f g : Jet5} {a : ℝ} (hx : x.Contains f a) (he : f.EqAt g a) :
    x.Contains g a := by
  rcases he with ⟨h0,h1,h2,h3,h4,h5⟩
  simpa only [DyadicJet5Enclosure.Contains, h0,h1,h2,h3,h4,h5] using hx

/-- The remaining parameter assumptions are scalar equality and soundness of
the two stable jets; the full fifth-order inverse recurrence is proved here. -/
theorem eval_contains_canonical {p : ℕ} {x y : DyadicJet5Enclosure p}
    {jx jy : Jet5} {U : Set ℝ} (hU : IsOpen U)
    (hjx : jx.SoundOn U) (hjy : jy.SoundOn U)
    (hrange : ∀ a ∈ U, jy.d0 a ∈ GeneralCK.e8SlopeRange)
    (hvalue : ∀ a ∈ U, jx.d0 a = GeneralCK.e8Q (jy.d0 a))
    {a : ℝ} (ha : a ∈ U)
    (hx : x.Contains jx a) (hy : y.Contains jy a) (hp : 0 < y.d1.lo) :
    (eval x y).Contains
      (E8InverseJet5Bridge.e8QJet5 E8InverseJet5Bridge.e8ThetaCanonicalJet5)
      (jy.d0 a) := by
  have hpReal : jy.d1 a ≠ 0 := by
    have hh := hy.2.1.1
    have hpos : (0 : ℝ) < y.d1.lo := by exact_mod_cast hp
    have hs := scale_cast_pos p
    intro he
    rw [he, mul_zero] at hh
    linarith
  have result := contains_of_eqAt (eval_sound hx hy hp)
    (qdata5_eq_canonical hU hjx hjy hrange hvalue ha hpReal)
  exact result

#print axioms eval_sound
#print axioms eval_contains_canonical

end GeneralCK.Certificates.E8TAxisReparamInterval


end


