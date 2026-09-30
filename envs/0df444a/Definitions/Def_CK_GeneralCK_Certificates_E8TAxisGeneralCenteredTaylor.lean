-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
-- name    : CK_GeneralCK_Certificates_E8TAxisGeneralCenteredTaylor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:35:24.949926+00:00
-- url     : https://prove2.me/theorems/fdb2e875-d004-458b-9479-0cadd1b96af9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisGeneralCenteredTaylor.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisBivariateTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisReparamInterval
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisOneCellGeometry
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor =====
section

/-!
# Centered E8 Taylor replay with arbitrary coefficient boxes

The precision and coefficient intervals are parameters.  The real Taylor
identity is inherited from the canonical directional jet, while the interval
proof checks the same fourteen terms as the retained first-cell arithmetic.
-/

namespace GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor

open GeneralCK Set DyadicInterval
open E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisCenteredReplaySoundness E8TAxisBivariateTaylor
open E8TAxisOneCellGeometry






namespace Data































theorem term_sound {p : ℕ} {b : Data p} {z x y : ℝ} {i j : ℕ}
    (hz : (b.coeff i (j + 1)).Contains z)
    (hx : b.ds.Contains x) (hy : b.dt.Contains y) :
    (b.term i j).Contains
      (z * x ^ i * y ^ j / ((i.factorial * j.factorial : ℕ) : ℝ)) := by
  have hn : 0 < i.factorial * j.factorial :=
    Nat.mul_pos (Nat.factorial_pos i) (Nat.factorial_pos j)
  have hp : 0 < (ofInt p (i.factorial * j.factorial : ℕ)).lo := by
    dsimp only [ofInt]
    exact mul_pos (scale_pos p) (by exact_mod_cast hn)
  have hh := mul_sound
    (mul_sound (mul_sound hz (E8TAxisReparamInterval.powI_sound hx i))
      (E8TAxisReparamInterval.powI_sound hy j))
    (recip_sound hp (ofInt_sound p (i.factorial * j.factorial : ℕ)))
  simpa only [term, Int.cast_natCast, div_eq_mul_inv] using hh

theorem centeredValue_mem {p : ℕ} {b : Data p} {c r : ℕ → ℕ → ℝ} {x y : ℝ}
    (hc : b.CenterEnclosed c) (hr : b.RemainderEnclosed r)
    (hx : b.ds.Contains x) (hy : b.dt.Contains y) :
    b.replay.Contains (centeredValue c r x y) := by
  rcases hc with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases hr with ⟨h10, h11, h12, h13, h14⟩
  have t01 := term_sound (i := 0) (j := 1) h1 hx hy
  have t10 := term_sound (i := 1) (j := 0) h2 hx hy
  have t02 := term_sound (i := 0) (j := 2) h3 hx hy
  have t11 := term_sound (i := 1) (j := 1) h4 hx hy
  have t20 := term_sound (i := 2) (j := 0) h5 hx hy
  have t03 := term_sound (i := 0) (j := 3) h6 hx hy
  have t12 := term_sound (i := 1) (j := 2) h7 hx hy
  have t21 := term_sound (i := 2) (j := 1) h8 hx hy
  have t30 := term_sound (i := 3) (j := 0) h9 hx hy
  have t04 := term_sound (i := 0) (j := 4) h10 hx hy
  have t13 := term_sound (i := 1) (j := 3) h11 hx hy
  have t22 := term_sound (i := 2) (j := 2) h12 hx hy
  have t31 := term_sound (i := 3) (j := 1) h13 hx hy
  have t40 := term_sound (i := 4) (j := 0) h14 hx hy
  have hh := add_sound
    (add_sound (add_sound (add_sound (add_sound
      (add_sound (add_sound (add_sound (add_sound
        (add_sound (add_sound (add_sound (add_sound
          (add_sound h0 t01) t10) t02) t11) t20) t03) t12) t21) t30)
      t04) t13) t22) t31) t40
  simpa [replay, centeredValue, Nat.factorial] using hh

end Data

/-- A point on the segment supplies all five remainder coefficients in the
same real centered polynomial used by the interval replay. -/
theorem exists_centeredValue {s0 t0 x y : ℝ}
    (hrange : ∀ u ∈ Icc (0 : ℝ) 1, InputsInRange (s0 + x * u) (t0 + y * u)) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      e8RegularDeltaT (s0 + x) (t0 + y) =
        centeredValue (mixed qJet s0 t0)
          (mixed qJet (s0 + x * u) (t0 + y * u)) x y := by
  have hj := deltaTJet_sound4On hrange
  obtain ⟨u, hu, heq⟩ := E8TAxisTaylor4.exists_remainder
    (fun v hv => (hj v hv).1) (fun v hv => (hj v hv).2.1)
    (fun v hv => (hj v hv).2.2.1) (fun v hv => (hj v hv).2.2.2)
  refine ⟨u, hu, ?_⟩
  have hend : (deltaTJet s0 t0 x y).d0 1 = e8RegularDeltaT (s0 + x) (t0 + y) := by
    simpa only [mul_one] using deltaTJet_d0_eq_regular (hrange 1 (by norm_num))
  rw [hend, ray_d0 s0 t0 x y 0, ray_d1 s0 t0 x y 0,
    ray_d2 s0 t0 x y 0, ray_d3 s0 t0 x y 0, ray_d4 s0 t0 x y u] at heq
  simp only [mul_zero, add_zero] at heq
  rw [centeredValue_eq]
  exact heq

namespace Data

theorem replay_contains {p : ℕ} {b : Data p} {s0 t0 x y : ℝ}
    (hrange : ∀ u ∈ Icc (0 : ℝ) 1, InputsInRange (s0 + x * u) (t0 + y * u))
    (hc : b.CenterEnclosed (mixed qJet s0 t0))
    (hr : ∀ u ∈ Ioo (0 : ℝ) 1,
      b.RemainderEnclosed (mixed qJet (s0 + x * u) (t0 + y * u)))
    (hx : b.ds.Contains x) (hy : b.dt.Contains y) :
    b.replay.Contains (e8RegularDeltaT (s0 + x) (t0 + y)) := by
  obtain ⟨u, hu, heq⟩ := exists_centeredValue hrange
  rw [heq]
  exact centeredValue_mem hc (hr u hu) hx hy

/-- Specialization to the retained first-cell displacement intervals. -/
theorem firstCell_contains {b : Data E8TAxisOneCellArithmetic.precision}
    (hds : b.ds = E8TAxisOneCellArithmetic.ds)
    (hdt : b.dt = E8TAxisOneCellArithmetic.dt)
    (hc : b.CenterEnclosed (mixed qJet centerS centerT))
    (hr : ∀ s t, InFirstCell s t → b.RemainderEnclosed (mixed qJet s t))
    {s t : ℝ} (h : InFirstCell s t) :
    b.replay.Contains (e8RegularDeltaT s t) := by
  have hd := displacement_mem h
  have hx : b.ds.Contains (s - centerS) := by rw [hds]; exact hd.1
  have hy : b.dt.Contains (t - centerT) := by rw [hdt]; exact hd.2
  have hh := replay_contains (segment_inputsInRange h) hc
    (fun u hu => hr _ _ (segment_mem h ⟨hu.1.le, hu.2.le⟩)) hx hy
  simpa only [show centerS + (s - centerS) = s by ring,
    show centerT + (t - centerT) = t by ring] using hh

theorem firstCell_positive {b : Data E8TAxisOneCellArithmetic.precision}
    (hds : b.ds = E8TAxisOneCellArithmetic.ds)
    (hdt : b.dt = E8TAxisOneCellArithmetic.dt)
    (hc : b.CenterEnclosed (mixed qJet centerS centerT))
    (hr : ∀ s t, InFirstCell s t → b.RemainderEnclosed (mixed qJet s t))
    (hp : b.replay.positiveCheck = true) {s t : ℝ} (h : InFirstCell s t) :
    0 < e8RegularDeltaT s t :=
  positiveCheck_sound hp (firstCell_contains hds hdt hc hr h)

end Data

#print axioms Data.centeredValue_mem
#print axioms exists_centeredValue
#print axioms Data.firstCell_positive

end GeneralCK.Certificates.E8TAxisGeneralCenteredTaylor

end


