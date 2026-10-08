-- Prove2me | Definitions.Def_sf241_shoot_bounds
-- name    : sf241_shoot_bounds
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T05:32:38.846725+00:00
-- url     : https://prove2.me/theorems/16b57ba5-9e5d-4b55-9b69-8d6d32b6b581
-- title:
--   Shooting at $\kappa=4$: slope 3 overshoots, slope 5 undershoots
-- statement:
--   Validated endpoint bounds for the shooting problem at $\kappa=4$. For every shot $h$ (solution of (2.6) on $(0,\pi/2)$, smooth on $[0,\pi/2]$, $h(0)=0$, $h'(0)=a$):
--   $$a=3:\ h(\pi/2)>3.15>\pi,\qquad a=5:\ h(\pi/2)<3.14<\pi.$$
--   These are `P241N.three_overshoots` and `P241N.five_undershoots`.
--
--   The proof chains the a-priori start at $z=2^{-12}$ (with $z=\tan(\theta/2)$) and the four kernel-checked chunks, and reads off $k(1)=h(\pi/2)$. Numerically $h_3(\pi/2)\approx 3.228$ and $h_5(\pi/2)\approx 3.013$.
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Definitions.Def_sf241_enclosure3_lo
import Definitions.Def_sf241_enclosure3_hi
import Definitions.Def_sf241_enclosure5_lo
import Definitions.Def_sf241_enclosure5_hi

/-!
# Validated endpoint bounds for the slopes 3 and 5

Any shot `h` with slope `a` (`ShootSol a h`) is moved to the variable `z = tan (θ/2)`, where
`θ = π/2` becomes `z = 1`. Near `z = 0` an a-priori estimate pins the solution to `2az` up to
`O(z³)`; on `[2⁻¹², 1]` the chained piecewise-polynomial enclosures (checked by the kernel in
`Def_sf241_check3_*`, `Def_sf241_check5_*`, chained in `Def_sf241_enclosure3_lo/hi`, `Def_sf241_enclosure5_lo/hi`) bound `h(π/2)`:
`h(π/2) > 3.15 > π` for slope 3 and `h(π/2) < 3.14 < π` for slope 5.
-/

open Real Set

namespace P241N

lemma isSol_of {a : ℝ} {h : ℝ → ℝ} (hs : SphericalFerromagnet.ShootSol a h) {z0 : ℝ}
    (h0 : 0 < z0) (h1 : z0 < 1) : IsSol (kz h) (Pz h) z0 where
  pos := h0
  cont_k := (kz_cont hs).mono (Icc_subset_Icc_left h0.le)
  cont_P := (Pz_cont hs).mono (Icc_subset_Icc_left h0.le)
  dk := fun z hz => kz_deriv hs ⟨lt_of_lt_of_le h0 hz.1, hz.2⟩
  dP := fun z hz => Pz_deriv hs ⟨lt_of_lt_of_le h0 hz.1, hz.2⟩

lemma nearZero_of {a : ℝ} {h : ℝ → ℝ} (hs : SphericalFerromagnet.ShootSol a h) {z1 : ℝ}
    (h0 : 0 < z1) (h1 : z1 < 1) : NearZero (kz h) (Pz h) a z1 where
  pos := h0
  le1 := h1.le
  ck := (kz_cont hs).mono fun z hz => ⟨hz.1.le, le_trans hz.2 h1.le⟩
  cP := (Pz_cont hs).mono fun z hz => ⟨hz.1.le, le_trans hz.2 h1.le⟩
  dk := fun z hz => kz_deriv hs ⟨hz.1, lt_trans hz.2 h1⟩
  dP := fun z hz => Pz_deriv hs ⟨hz.1, lt_trans hz.2 h1⟩
  lk := kz_lim hs
  lP := Pz_lim hs

theorem bound3 {k P : ℝ → ℝ} (hsol : IsSol k P D3.z0)
    (hk : |k D3.z0 - 2 * (3 : ℚ) * D3.z0| ≤ D3.sing) (hP : |P D3.z0 - 2 * (3 : ℚ) * D3.z0| ≤ D3.sing) :
    ((315 / 100 : ℚ) : ℝ) < k 1 := by
  have i0 := init_sound (s := D3.s0) hk hP (by decide +kernel)
  have c2 := enclosure3_lo hsol le_rfl i0
  have c4 := enclosure3_hi hsol c2.1 c2.2
  exact lowerEnd_sound (by exact_mod_cast c4.2) (by decide +kernel)

theorem bound5 {k P : ℝ → ℝ} (hsol : IsSol k P D5.z0)
    (hk : |k D5.z0 - 2 * (5 : ℚ) * D5.z0| ≤ D5.sing) (hP : |P D5.z0 - 2 * (5 : ℚ) * D5.z0| ≤ D5.sing) :
    k 1 < ((314 / 100 : ℚ) : ℝ) := by
  have i0 := init_sound (s := D5.s0) hk hP (by decide +kernel)
  have c2 := enclosure5_lo hsol le_rfl i0
  have c4 := enclosure5_hi hsol c2.1 c2.2
  exact upperEnd_sound (by exact_mod_cast c4.2) (by decide +kernel)

/-- Slope 3 overshoots: every shot with slope 3 satisfies `h(π/2) > π`. -/
theorem three_overshoots : ∀ h, SphericalFerromagnet.ShootSol 3 h → π < h (π / 2) := by
  intro h hs
  have hs' : SphericalFerromagnet.ShootSol ((3 : ℚ) : ℝ) h := by norm_num; exact hs
  have hz0 : (0 : ℝ) < (D3.z0 : ℝ) := by norm_num [D3.z0]
  have hz1 : (D3.z0 : ℝ) < 1 := by norm_num [D3.z0]
  have hsing := sing_start (nearZero_of hs' hz0 hz1) (η := 1 / 100) (by norm_num)
    (by norm_num [D3.z0])
  have hS : 3 * ((2 / 3) * (2 * |((3 : ℚ) : ℝ)| + 1 / 100) ^ 3 +
      16 * ((2 * |((3 : ℚ) : ℝ)| + 1 / 100) + 2)) * (D3.z0 : ℝ) ^ 3 / 8 = (D3.sing : ℝ) := by
    norm_num [D3.z0, D3.sing]
  rw [hS] at hsing
  have := bound3 (isSol_of hs' hz0 hz1) hsing.1 hsing.2
  rw [kz_one] at this
  have hpi := Real.pi_lt_d2
  norm_num at this hpi ⊢
  linarith

/-- Slope 5 undershoots: every shot with slope 5 satisfies `h(π/2) < π`. -/
theorem five_undershoots : ∀ h, SphericalFerromagnet.ShootSol 5 h → h (π / 2) < π := by
  intro h hs
  have hs' : SphericalFerromagnet.ShootSol ((5 : ℚ) : ℝ) h := by norm_num; exact hs
  have hz0 : (0 : ℝ) < (D5.z0 : ℝ) := by norm_num [D5.z0]
  have hz1 : (D5.z0 : ℝ) < 1 := by norm_num [D5.z0]
  have hsing := sing_start (nearZero_of hs' hz0 hz1) (η := 1 / 100) (by norm_num)
    (by norm_num [D5.z0])
  have hS : 3 * ((2 / 3) * (2 * |((5 : ℚ) : ℝ)| + 1 / 100) ^ 3 +
      16 * ((2 * |((5 : ℚ) : ℝ)| + 1 / 100) + 2)) * (D5.z0 : ℝ) ^ 3 / 8 = (D5.sing : ℝ) := by
    norm_num [D5.z0, D5.sing]
  rw [hS] at hsing
  have := bound5 (isSol_of hs' hz0 hz1) hsing.1 hsing.2
  rw [kz_one] at this
  have hpi := Real.pi_gt_d2
  norm_num at this hpi ⊢
  linarith

end P241N


