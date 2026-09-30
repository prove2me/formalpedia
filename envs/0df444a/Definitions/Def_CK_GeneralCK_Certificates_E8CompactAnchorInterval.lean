-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorInterval
-- name    : CK_GeneralCK_Certificates_E8CompactAnchorInterval
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:34:15.619761+00:00
-- url     : https://prove2.me/theorems/007c9767-e44c-432d-a243-40c81317cdb9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8CompactAnchorInterval` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8CompactAnchorInterval` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8CompactAnchorInterval` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8CompactAnchorInterval (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8CompactAnchorInterval.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorDeltaJet
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisMixedCoefficients

-- ===== source module GeneralCK.Certificates.E8CompactAnchorInterval =====
section

/-! Exact dyadic enclosures for the actual compact-anchor directional jets. -/

namespace GeneralCK.Certificates.E8CompactAnchorInterval

open E8TAxisDeltaDirectionalJet E8CompactAnchorDeltaJet
open E8TAxisStableInterval E8TAxisMixedCoefficients DyadicInterval

def slopeBox {p : ℕ} (b : DyadicJet5Enclosure p) (m : ℤ) : DyadicJet5Enclosure p :=
  ⟨b.d0, b.d1.mul (ofInt p m), b.d2.mul (ofInt p (m ^ 2)),
    b.d3.mul (ofInt p (m ^ 3)), b.d4.mul (ofInt p (m ^ 4)),
    b.d5.mul (ofInt p (m ^ 5))⟩

theorem slopeBox_contains {p : ℕ} {b : DyadicJet5Enclosure p} {j : Jet5}
    {c u : ℝ} (m : ℤ) (h : b.Contains j (c + (m : ℝ) * u)) :
    (slopeBox b m).Contains (affine j c m) u := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
  refine ⟨h0, mul_sound h1 (ofInt_sound p m), ?_, ?_, ?_, ?_⟩
  · have hterm := mul_sound h2 (ofInt_sound p (m ^ 2))
    have hpow : ((m ^ 2 : ℤ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm
  · have hterm := mul_sound h3 (ofInt_sound p (m ^ 3))
    have hpow : ((m ^ 3 : ℤ) : ℝ) = (m : ℝ) ^ 3 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm
  · have hterm := mul_sound h4 (ofInt_sound p (m ^ 4))
    have hpow : ((m ^ 4 : ℤ) : ℝ) = (m : ℝ) ^ 4 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm
  · have hterm := mul_sound h5 (ofInt_sound p (m ^ 5))
    have hpow : ((m ^ 5 : ℤ) : ℝ) = (m : ℝ) ^ 5 := by push_cast; rfl
    rw [hpow] at hterm
    simpa only [slopeBox, affine] using hterm

def graphBox {p : ℕ} (a b c d : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ((b.add (negative d)).mul (c.add (negative a))).add
    (negative ((b.add (negative c)).mul (d.add a)))

theorem graphBox_contains {p : ℕ} {a b c d : DyadicJet5Enclosure p}
    {A B C D : Jet5} {u : ℝ}
    (ha : a.Contains A u) (hb : b.Contains B u)
    (hc : c.Contains C u) (hd : d.Contains D u) :
    (graphBox a b c d).Contains (deltaGraph A B C D) u :=
  ((hb.add (negative_sound hd)).mul (hc.add (negative_sound ha))).add
    (negative_sound ((hb.add (negative_sound hc)).mul (hd.add ha)))

structure Boxes (p : ℕ) where
  a : DyadicJet5Enclosure p
  b : DyadicJet5Enclosure p
  c : DyadicJet5Enclosure p
  d : DyadicJet5Enclosure p

def Boxes.ContainsAt {p : ℕ} (b : Boxes p) (s t : ℝ) : Prop :=
  b.a.Contains qJet t ∧ b.b.Contains qJet (2 * s + t) ∧
    b.c.Contains qJet (s + t) ∧ b.d.Contains qJet s

def Boxes.direction {p : ℕ} (b : Boxes p) (ds dt : ℤ) : DyadicJet5Enclosure p :=
  graphBox (slopeBox b.a dt) (slopeBox b.b (2 * ds + dt))
    (slopeBox b.c (ds + dt)) (slopeBox b.d ds)

theorem Boxes.direction_contains {p : ℕ} {b : Boxes p} {s0 t0 u : ℝ}
    (ds dt : ℤ) (h : b.ContainsAt (s0 + (ds : ℝ) * u) (t0 + (dt : ℝ) * u)) :
    (b.direction ds dt).Contains (deltaJet s0 t0 ds dt) u := by
  apply graphBox_contains
  · exact slopeBox_contains dt h.1
  · have heq : (2 * s0 + t0) + ((2 * ds + dt : ℤ) : ℝ) * u =
        2 * (s0 + (ds : ℝ) * u) + (t0 + (dt : ℝ) * u) := by push_cast; ring
    have hb : b.b.Contains qJet ((2 * s0 + t0) + ((2 * ds + dt : ℤ) : ℝ) * u) := by
      rw [heq]
      exact h.2.1
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using slopeBox_contains (2 * ds + dt) hb
  · have heq : (s0 + t0) + ((ds + dt : ℤ) : ℝ) * u =
        (s0 + (ds : ℝ) * u) + (t0 + (dt : ℝ) * u) := by push_cast; ring
    have hc : b.c.Contains qJet ((s0 + t0) + ((ds + dt : ℤ) : ℝ) * u) := by
      rw [heq]
      exact h.2.2.1
    simpa only [Int.cast_add] using slopeBox_contains (ds + dt) hc
  · exact slopeBox_contains ds h.2.2.2

theorem Boxes.directionAt_contains {p : ℕ} {b : Boxes p} {s t : ℝ}
    (ds dt : ℤ) (h : b.ContainsAt s t) :
    (b.direction ds dt).Contains (deltaJet s t ds dt) 0 := by
  apply Boxes.direction_contains
  simpa only [mul_zero, add_zero] using h

def Boxes.coeff {p : ℕ} (b : Boxes p) (i j : ℕ) : DyadicInterval p :=
  mixedBox b.a b.b b.c b.d i j

theorem Boxes.coeff_contains {p : ℕ} {b : Boxes p} {s t : ℝ}
    (h : b.ContainsAt s t) (i j : ℕ) :
    (b.coeff i j).Contains (mixed qJet s t i j) :=
  mixedBox_sound h.1 h.2.1 h.2.2.1 h.2.2.2 i j

#print axioms slopeBox_contains
#print axioms graphBox_contains
#print axioms Boxes.direction_contains
#print axioms Boxes.directionAt_contains
#print axioms Boxes.coeff_contains

end GeneralCK.Certificates.E8CompactAnchorInterval

end


