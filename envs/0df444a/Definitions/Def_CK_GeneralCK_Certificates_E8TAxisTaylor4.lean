-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisTaylor4
-- name    : CK_GeneralCK_Certificates_E8TAxisTaylor4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:09:58.69898+00:00
-- url     : https://prove2.me/theorems/cd337954-4b5d-47f4-b1ff-317823a4629c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisTaylor4` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisTaylor4` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisTaylor4` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisTaylor4 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisTaylor4.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet5
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

-- ===== source module GeneralCK.Certificates.E8TAxisTaylor4 =====
section

/-!
# Fourth-order Taylor's theorem for explicitly supplied derivative chains

The interval replay supplies raw derivatives through order four of the
t-derivative of the E8 determinant.  Four applications of Rolle's theorem
give exactly the centered cubic polynomial and a fourth-order Lagrange
remainder, without asking for a sixth derivative of the inverse.
-/

namespace GeneralCK.Certificates.E8TAxisTaylor4

open Set

/-- A derivative chain through order four gives a Lagrange remainder on the
unit segment. No continuity of the last derivative is required. -/
theorem exists_remainder
    {f f1 f2 f3 f4 : ℝ → ℝ}
    (h0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f1 u) u)
    (h1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f1 (f2 u) u)
    (h2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f2 (f3 u) u)
    (h3 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f3 (f4 u) u) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      f 1 = f 0 + f1 0 + f2 0 / 2 + f3 0 / 6 + f4 u / 24 := by
  let R := 24 * (f 1 - (f 0 + f1 0 + f2 0 / 2 + f3 0 / 6))
  let g0 : ℝ → ℝ := fun u =>
    f u - (f 0 + f1 0 * u + f2 0 * u ^ 2 / 2 + f3 0 * u ^ 3 / 6 + R * u ^ 4 / 24)
  let g1 : ℝ → ℝ := fun u =>
    f1 u - (f1 0 + f2 0 * u + f3 0 * u ^ 2 / 2 + R * u ^ 3 / 6)
  let g2 : ℝ → ℝ := fun u => f2 u - (f2 0 + f3 0 * u + R * u ^ 2 / 2)
  let g3 : ℝ → ℝ := fun u => f3 u - (f3 0 + R * u)
  let g4 : ℝ → ℝ := fun u => f4 u - R
  have hd0 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g0 (g1 u) u := by
    intro u hu
    have hd := (h0 u hu).sub
      (((((hasDerivAt_const u (f 0)).add ((hasDerivAt_id u).const_mul (f1 0))).add
        (((hasDerivAt_id u).pow 2).const_mul (f2 0 / 2))).add
        (((hasDerivAt_id u).pow 3).const_mul (f3 0 / 6))).add
        (((hasDerivAt_id u).pow 4).const_mul (R / 24)))
    convert! hd using 1 <;> simp only [g0, g1, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;>
      first | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring) | ring
  have hd1 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g1 (g2 u) u := by
    intro u hu
    have hd := (h1 u hu).sub
      ((((hasDerivAt_const u (f1 0)).add ((hasDerivAt_id u).const_mul (f2 0))).add
        (((hasDerivAt_id u).pow 2).const_mul (f3 0 / 2))).add
        (((hasDerivAt_id u).pow 3).const_mul (R / 6)))
    convert! hd using 1 <;> simp only [g1, g2, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;>
      first | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring) | ring
  have hd2 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g2 (g3 u) u := by
    intro u hu
    have hd := (h2 u hu).sub
      (((hasDerivAt_const u (f2 0)).add ((hasDerivAt_id u).const_mul (f3 0))).add
        (((hasDerivAt_id u).pow 2).const_mul (R / 2)))
    convert! hd using 1 <;> simp only [g2, g3, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;>
      first | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring) | ring
  have hd3 : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt g3 (g4 u) u := by
    intro u hu
    convert! (h3 u hu).sub
      ((hasDerivAt_const u (f3 0)).add ((hasDerivAt_id u).const_mul R)) using 1 <;>
      simp only [g3, g4, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;> first | (funext x; simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]; ring) | ring
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
  obtain ⟨u4, hu4, he4⟩ := step hu3.1 (hu3.2.trans (hu2.2.trans hu1.2)).le hd3
    (by rw [he3]; simp [g3])
  refine ⟨u4, ⟨hu4.1, hu4.2.trans (hu3.2.trans (hu2.2.trans hu1.2))⟩, ?_⟩
  dsimp [g4, R] at he4
  linarith

#print axioms exists_remainder

end GeneralCK.Certificates.E8TAxisTaylor4

end


