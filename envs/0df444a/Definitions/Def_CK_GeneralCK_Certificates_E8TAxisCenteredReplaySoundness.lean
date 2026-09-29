-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCenteredReplaySoundness
-- name    : CK_GeneralCK_Certificates_E8TAxisCenteredReplaySoundness
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T11:06:30.364742+00:00
-- url     : https://prove2.me/theorems/1fc205a1-bc25-43aa-9607-95bb0a4c2a03
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisCenteredReplaySoundness` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisCenteredReplaySoundness` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisCenteredReplaySoundness` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisCenteredReplaySoundness (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisCenteredReplaySoundness.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisOneCellArithmetic
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisTaylor4
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.Certificates.E8TAxisCenteredReplaySoundness =====
section

/-! Semantic propagation through the historical centered arithmetic.
The finite coefficient enclosures are explicit premises; no saved numerical
derivative value is treated as an analytic fact. -/

namespace GeneralCK.Certificates.E8TAxisCenteredReplaySoundness

open DyadicInterval E8TAxisOneCellArithmetic Set

def CenterEnclosed (c : ℕ → ℕ → ℝ) : Prop :=
  initial.Contains (c 0 1) ∧
  der_0_2.Contains (c 0 2) ∧
  der_1_1.Contains (c 1 1) ∧
  der_0_3.Contains (c 0 3) ∧
  der_1_2.Contains (c 1 2) ∧
  der_2_1.Contains (c 2 1) ∧
  der_0_4.Contains (c 0 4) ∧
  der_1_3.Contains (c 1 3) ∧
  der_2_2.Contains (c 2 2) ∧
  der_3_1.Contains (c 3 1)

def RemainderEnclosed (r : ℕ → ℕ → ℝ) : Prop :=
  der_0_5.Contains (r 0 5) ∧
  der_1_4.Contains (r 1 4) ∧
  der_2_3.Contains (r 2 3) ∧
  der_3_2.Contains (r 3 2) ∧
  der_4_1.Contains (r 4 1)




theorem powI_sound {a : DyadicInterval precision} {x : ℝ}
    (ha : a.Contains x) (n : ℕ) : (powI a n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [powI] using ofInt_sound precision 1
  | succ n ih => simpa [powI, pow_succ] using mul_sound ih ha

theorem divNat_sound {a : DyadicInterval precision} {x : ℝ} {n : ℕ}
    (ha : a.Contains x) (hn : 0 < n) : (divNat a n).Contains (x / n) := by
  have hp : 0 < (ofInt precision (n : ℤ)).lo := by
    dsimp [ofInt]
    exact mul_pos (scale_pos precision) (by exact_mod_cast hn)
  have hh := mul_sound ha (recip_sound hp (ofInt_sound precision (n : ℤ)))
  simpa only [divNat, Int.cast_natCast, div_eq_mul_inv] using hh

theorem term_sound {a : DyadicInterval precision} {z x y : ℝ} {i j n : ℕ}
    (ha : a.Contains z) (hx : ds.Contains x) (hy : dt.Contains y) (hn : 0 < n) :
    (divNat ((a.mul (powI ds i)).mul (powI dt j)) n).Contains
      (z * x ^ i * y ^ j / n) :=
  divNat_sound (mul_sound (mul_sound ha (powI_sound hx i)) (powI_sound hy j)) hn

/-- Every multiplication, positive integer division, and addition in the
saved centered replay preserves containment of the corresponding real sum. -/
theorem centeredValue_mem {c r : ℕ → ℕ → ℝ} {x y : ℝ}
    (hc : CenterEnclosed c) (hr : RemainderEnclosed r)
    (hx : ds.Contains x) (hy : dt.Contains y) :
    centeredReplay.Contains (centeredValue c r x y) := by
  rcases hc with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases hr with ⟨h10, h11, h12, h13, h14⟩
  exact
    add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (add_sound (h0) (by simpa only [term_00, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 0) (j := 1) h1 hx hy (by decide : 0 < 1))) (by simpa only [term_01, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 1) (j := 0) h2 hx hy (by decide : 0 < 1))) (by simpa only [term_02, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 0) (j := 2) h3 hx hy (by decide : 0 < 2))) (by simpa only [term_03, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 1) (j := 1) h4 hx hy (by decide : 0 < 1))) (by simpa only [term_04, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 2) (j := 0) h5 hx hy (by decide : 0 < 2))) (by simpa only [term_05, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 0) (j := 3) h6 hx hy (by decide : 0 < 6))) (by simpa only [term_06, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 1) (j := 2) h7 hx hy (by decide : 0 < 2))) (by simpa only [term_07, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 2) (j := 1) h8 hx hy (by decide : 0 < 2))) (by simpa only [term_08, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 3) (j := 0) h9 hx hy (by decide : 0 < 6))) (by simpa only [term_09, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 0) (j := 4) h10 hx hy (by decide : 0 < 24))) (by simpa only [term_10, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 1) (j := 3) h11 hx hy (by decide : 0 < 6))) (by simpa only [term_11, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 2) (j := 2) h12 hx hy (by decide : 0 < 4))) (by simpa only [term_12, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 3) (j := 1) h13 hx hy (by decide : 0 < 6))) (by simpa only [term_13, Nat.cast_ofNat, Nat.cast_one] using term_sound (i := 4) (j := 0) h14 hx hy (by decide : 0 < 24))

/-- Exact real polynomial corresponding to the grouped raw ray derivatives. -/
theorem centeredValue_eq (c r : ℕ → ℕ → ℝ) (x y : ℝ) :
    centeredValue c r x y = c 0 1 +
      (c 0 2 * y + c 1 1 * x) +
      (c 0 3 * y ^ 2 + 2 * c 1 2 * x * y + c 2 1 * x ^ 2) / 2 +
      (c 0 4 * y ^ 3 + 3 * c 1 3 * x * y ^ 2 +
        3 * c 2 2 * x ^ 2 * y + c 3 1 * x ^ 3) / 6 +
      (r 0 5 * y ^ 4 + 4 * r 1 4 * x * y ^ 3 +
        6 * r 2 3 * x ^ 2 * y ^ 2 + 4 * r 3 2 * x ^ 3 * y + r 4 1 * x ^ 4) / 24 := by
  unfold centeredValue
  ring

/-- A sound derivative chain and its raw bivariate coefficient identities
transfer the arithmetic enclosure to the actual endpoint value. -/
theorem endpoint_mem {f f1 f2 f3 f4 : ℝ → ℝ}
    {c : ℕ → ℕ → ℝ} {r : ℝ → ℕ → ℕ → ℝ} {x y : ℝ}
    (h0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f1 u) u)
    (h1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f1 (f2 u) u)
    (h2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f2 (f3 u) u)
    (h3 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f3 (f4 u) u)
    (hv : f 0 = c 0 1)
    (hd1 : f1 0 = c 0 2 * y + c 1 1 * x)
    (hd2 : f2 0 = c 0 3 * y ^ 2 + 2 * c 1 2 * x * y + c 2 1 * x ^ 2)
    (hd3 : f3 0 = c 0 4 * y ^ 3 + 3 * c 1 3 * x * y ^ 2 +
      3 * c 2 2 * x ^ 2 * y + c 3 1 * x ^ 3)
    (hd4 : ∀ u ∈ Ioo (0 : ℝ) 1, f4 u =
      r u 0 5 * y ^ 4 + 4 * r u 1 4 * x * y ^ 3 +
      6 * r u 2 3 * x ^ 2 * y ^ 2 + 4 * r u 3 2 * x ^ 3 * y + r u 4 1 * x ^ 4)
    (hc : CenterEnclosed c)
    (hr : ∀ u ∈ Ioo (0 : ℝ) 1, RemainderEnclosed (r u))
    (hx : ds.Contains x) (hy : dt.Contains y) : centeredReplay.Contains (f 1) := by
  obtain ⟨u, hu, heq⟩ := E8TAxisTaylor4.exists_remainder h0 h1 h2 h3
  rw [heq, hv, hd1, hd2, hd3, hd4 u hu, ← centeredValue_eq]
  exact centeredValue_mem hc (hr u hu) hx hy

#print axioms centeredValue_mem
#print axioms endpoint_mem

end GeneralCK.Certificates.E8TAxisCenteredReplaySoundness

end


