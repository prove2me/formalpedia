-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_DyadicJet5Bounds
-- name    : CK_GeneralCK_Certificates_DyadicJet5Bounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:20:11.412174+00:00
-- url     : https://prove2.me/theorems/2622ed86-df9a-427c-8575-53b036eb94eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.DyadicJet5Bounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.DyadicJet5Bounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.DyadicJet5Bounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.DyadicJet5Bounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/DyadicJet5Bounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet5
import Definitions.Def_CK_GeneralCK_Certificates_DyadicExpBounds
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_interval_checkers

-- ===== source module GeneralCK.Certificates.DyadicJet5Bounds =====
section

/-! Fixed-scale enclosures for raw order-five univariate jets. -/

namespace GeneralCK.Certificates










namespace DyadicJet5Enclosure

open DyadicInterval
















def scale {p : ℕ} (z : ℤ) (b : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  let c := ofInt p z
  ⟨c.mul b.d0, c.mul b.d1, c.mul b.d2, c.mul b.d3, c.mul b.d4, c.mul b.d5⟩

/-- Faà di Bruno interval propagation for `exp`, using a separately checked
value enclosure `e` for `exp (j.d0 t)`. -/
def exp {p : ℕ} (b : DyadicJet5Enclosure p) (e : DyadicInterval p) :
    DyadicJet5Enclosure p :=
  let c3 := ofInt p 3
  let c4 := ofInt p 4
  let c5 := ofInt p 5
  let c6 := ofInt p 6
  let c10 := ofInt p 10
  let c15 := ofInt p 15
  let q2 := (b.d1.mul b.d1).add b.d2
  let q3 := ((b.d1.mul b.d1).mul b.d1).add
    ((c3.mul b.d1).mul b.d2) |>.add b.d3
  let q4a := (((b.d1.mul b.d1).mul b.d1).mul b.d1).add
    ((c6.mul (b.d1.mul b.d1)).mul b.d2)
  let q4b := q4a.add ((c3.mul b.d2).mul b.d2)
  let q4c := q4b.add ((c4.mul b.d1).mul b.d3)
  let q4 := q4c.add b.d4
  let q5a := ((((b.d1.mul b.d1).mul b.d1).mul b.d1).mul b.d1).add
    (c10.mul (((b.d1.mul b.d1).mul b.d1).mul b.d2))
  let q5b := q5a.add (c15.mul ((b.d1.mul b.d2).mul b.d2))
  let q5c := q5b.add (c10.mul ((b.d1.mul b.d1).mul b.d3))
  let q5d := q5c.add (c10.mul (b.d2.mul b.d3))
  let q5e := q5d.add (c5.mul (b.d1.mul b.d4))
  let q5 := q5e.add b.d5
  ⟨e, e.mul b.d1, e.mul q2, e.mul q3, e.mul q4, e.mul q5⟩

theorem contains_const (p : ℕ) (z : ℤ) (t : ℝ) :
    (const p z).Contains (Jet5.const z) t := by
  exact ⟨ofInt_sound p z, by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0,
    by simpa [const, Jet5.const] using ofInt_sound p 0⟩

theorem contains_variable {p : ℕ} {i : DyadicInterval p} {t : ℝ} (ht : i.Contains t) :
    (variableJet i).Contains Jet5.variableJet t := by
  exact ⟨ht, by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 1,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0,
    by simpa [variableJet, Jet5.variableJet] using ofInt_sound p 0⟩

theorem Contains.add {p : ℕ} {b c : DyadicJet5Enclosure p} {j k : Jet5} {t : ℝ}
    (hb : b.Contains j t) (hc : c.Contains k t) :
    (b.add c).Contains (j.add k) t :=
  ⟨add_sound hb.1 hc.1, add_sound hb.2.1 hc.2.1,
    add_sound hb.2.2.1 hc.2.2.1, add_sound hb.2.2.2.1 hc.2.2.2.1,
    add_sound hb.2.2.2.2.1 hc.2.2.2.2.1, add_sound hb.2.2.2.2.2 hc.2.2.2.2.2⟩

theorem Contains.scale {p : ℕ} {b : DyadicJet5Enclosure p} {j : Jet5} {t : ℝ}
    (hb : b.Contains j t) (z : ℤ) :
    (b.scale z).Contains ((Jet5.const z).mul j) t := by
  have hz := ofInt_sound p z
  simp only [Contains, DyadicJet5Enclosure.scale, Jet5.mul, Jet5.const,
    zero_mul, mul_zero, zero_add]
  exact ⟨mul_sound hz hb.1, mul_sound hz hb.2.1, mul_sound hz hb.2.2.1,
    mul_sound hz hb.2.2.2.1, mul_sound hz hb.2.2.2.2.1,
    mul_sound hz hb.2.2.2.2.2⟩

theorem Contains.exp {p : ℕ} {b : DyadicJet5Enclosure p} {e : DyadicInterval p}
    {j : Jet5} {t : ℝ} (hb : b.Contains j t) (he : e.Contains (Real.exp (j.d0 t))) :
    (b.exp e).Contains j.exp t := by
  rcases hb with ⟨h0,h1,h2,h3,h4,h5⟩
  have c3 := ofInt_sound p 3
  have c4 := ofInt_sound p 4
  have c5 := ofInt_sound p 5
  have c6 := ofInt_sound p 6
  have c10 := ofInt_sound p 10
  have c15 := ofInt_sound p 15
  dsimp only [Contains, DyadicJet5Enclosure.exp, Jet5.exp]
  refine ⟨he, mul_sound he h1, ?_, ?_, ?_, ?_⟩
  · simpa [DyadicJet5Enclosure.exp, Jet5.exp, pow_two] using
      mul_sound he (add_sound (mul_sound h1 h1) h2)
  · simpa [DyadicJet5Enclosure.exp, Jet5.exp, pow_succ] using mul_sound he
      (add_sound (add_sound (mul_sound (mul_sound h1 h1) h1)
        (mul_sound (mul_sound c3 h1) h2)) h3)
  · convert mul_sound he
      (add_sound (add_sound (add_sound (add_sound
        (mul_sound (mul_sound (mul_sound h1 h1) h1) h1)
        (mul_sound (mul_sound c6 (mul_sound h1 h1)) h2))
        (mul_sound (mul_sound c3 h2) h2))
        (mul_sound (mul_sound c4 h1) h3)) h4) using 1 <;> ring
  · convert mul_sound he
      (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound
        (mul_sound (mul_sound (mul_sound (mul_sound h1 h1) h1) h1) h1)
        (mul_sound c10 (mul_sound (mul_sound (mul_sound h1 h1) h1) h2)))
        (mul_sound c15 (mul_sound (mul_sound h1 h2) h2)))
        (mul_sound c10 (mul_sound (mul_sound h1 h1) h3)))
        (mul_sound c10 (mul_sound h2 h3)))
        (mul_sound c5 (mul_sound h1 h4))) h5) using 1 <;> ring

end DyadicJet5Enclosure
end GeneralCK.Certificates

end


