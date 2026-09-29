-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8CompactAnchorTaylor3
-- name    : CK_GeneralCK_Certificates_E8CompactAnchorTaylor3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:04:04.27435+00:00
-- url     : https://prove2.me/theorems/28b5e705-e71e-4b77-b256-9f83496eb5f5
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8CompactAnchorTaylor3` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8CompactAnchorTaylor3` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8CompactAnchorTaylor3` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8CompactAnchorTaylor3 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8CompactAnchorTaylor3.lean)

import Definitions.Def_CK_GeneralCK_Certificates_TaylorBounds
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

-- ===== source module GeneralCK.Certificates.E8CompactAnchorTaylor3 =====
section

/-!
# Third-order and first-order anchor bounds on a unit segment

These lemmas consume explicit derivative chains.  They do not trust stored
numerical anchors and can be applied to the actual E8 directional jets.
-/

namespace GeneralCK.Certificates.E8CompactAnchorTaylor3

open Set

/-- A three-link derivative chain gives the exact cubic Lagrange
remainder at some interior segment point. -/
theorem exists_remainder
    {f f1 f2 f3 : ℝ → ℝ}
    (h0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f1 u) u)
    (h1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f1 (f2 u) u)
    (h2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f2 (f3 u) u) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      f 1 = f 0 + f1 0 + f2 0 / 2 + f3 u / 6 := by
  let R := 6 * (f 1 - (f 0 + f1 0 + f2 0 / 2))
  let g0 : ℝ → ℝ := fun u =>
    f u - (f 0 + f1 0 * u + f2 0 * u ^ 2 / 2 + R * u ^ 3 / 6)
  let g1 : ℝ → ℝ := fun u =>
    f1 u - (f1 0 + f2 0 * u + R * u ^ 2 / 2)
  let g2 : ℝ → ℝ := fun u => f2 u - (f2 0 + R * u)
  let g3 : ℝ → ℝ := fun u => f3 u - R
  have hd0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g0 (g1 u) u := by
    intro u hu
    have hd := (h0 u hu).sub
      ((((hasDerivAt_const u (f 0)).add
        ((hasDerivAt_id u).const_mul (f1 0))).add
        (((hasDerivAt_id u).pow 2).const_mul (f2 0 / 2))).add
        (((hasDerivAt_id u).pow 3).const_mul (R / 6)))
    convert! hd using 1 <;>
      simp only [g0, g1, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
  have hd1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g1 (g2 u) u := by
    intro u hu
    have hd := (h1 u hu).sub
      (((hasDerivAt_const u (f1 0)).add
        ((hasDerivAt_id u).const_mul (f2 0))).add
        (((hasDerivAt_id u).pow 2).const_mul (R / 2)))
    convert! hd using 1 <;>
      simp only [g1, g2, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
  have hd2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g2 (g3 u) u := by
    intro u hu
    convert! (h2 u hu).sub
      ((hasDerivAt_const u (f2 0)).add
        ((hasDerivAt_id u).const_mul R)) using 1 <;>
      simp only [g2, g3, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;>
      first
      | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring)
      | ring
  have step {g dg : ℝ → ℝ} {b : ℝ}
      (hb : 0 < b) (hb1 : b ≤ 1)
      (hd : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g (dg u) u)
      (heq : g 0 = g b) : ∃ c ∈ Ioo (0 : ℝ) b, dg c = 0 := by
    apply exists_hasDerivAt_eq_zero hb
    · intro u hu
      exact (hd u ⟨hu.1, hu.2.trans hb1⟩).continuousAt.continuousWithinAt
    · exact heq
    · intro u hu
      exact hd u ⟨hu.1.le, hu.2.le.trans hb1⟩
  obtain ⟨u1, hu1, he1⟩ := step (by norm_num : (0 : ℝ) < 1) le_rfl hd0
    (by dsimp [g0, R]; ring)
  obtain ⟨u2, hu2, he2⟩ := step hu1.1 hu1.2.le hd1
    (by rw [he1]; simp [g1])
  obtain ⟨u3, hu3, he3⟩ := step hu2.1 (hu2.2.trans hu1.2).le hd2
    (by rw [he2]; simp [g2])
  refine ⟨u3, ⟨hu3.1, hu3.2.trans (hu2.2.trans hu1.2)⟩, ?_⟩
  dsimp [g3, R] at he3
  linarith

/-- Uniform lower control of the third directional derivative yields a
numerical cubic anchor bound. -/
theorem lower_of_third_bound
    {f f1 f2 f3 : ℝ → ℝ} {R : ℝ}
    (h0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f1 u) u)
    (h1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f1 (f2 u) u)
    (h2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f2 (f3 u) u)
    (hR : ∀ u ∈ Ioo (0 : ℝ) 1, R ≤ f3 u) :
    f 0 + f1 0 + f2 0 / 2 + R / 6 ≤ f 1 := by
  obtain ⟨u, hu, heq⟩ := exists_remainder h0 h1 h2
  rw [heq]
  linarith [hR u hu]

/-- A uniform lower bound on the first directional derivative transports
one center value to the whole segment. -/
theorem lower_of_first_bound {f df : ℝ → ℝ} {R : ℝ}
    (hd : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (df u) u)
    (hR : ∀ u ∈ Ioo (0 : ℝ) 1, R ≤ df u) :
    f 0 + R ≤ f 1 := by
  let g : ℝ → ℝ := fun u => f u - R * u
  have hg : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g (df u - R) u := by
    intro u hu
    convert! (hd u hu).sub ((hasDerivAt_id u).const_mul R) using 1 <;>
      simp [g]
  have hmono : MonotoneOn g (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro u hu
      exact (hg u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hg u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hg u ⟨hu.1.le, hu.2.le⟩).deriv]
      linarith [hR u hu]
  have h01 := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [g] at h01
  linarith

#print axioms exists_remainder
#print axioms lower_of_third_bound
#print axioms lower_of_first_bound

end GeneralCK.Certificates.E8CompactAnchorTaylor3

end


