-- Prove2me | Definitions.Def_Castro2006_action
-- name    : Castro2006_action
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T19:47:09.511566+00:00
-- url     : https://prove2.me/theorems/31f201f5-36ae-4a78-83ec-231999eb7412
-- title:
--   Action representation from a MulAut homomorphism
-- statement:
--   Constructs the G-module structure and the integral representation induced by a homomorphism into the automorphism group.

import Mathlib
open CategoryTheory

namespace Castro2006
variable {G N : Type} [Group G] [CommGroup N]

/-- The `G`-action on `N` induced by a homomorphism `φ : G →* MulAut N`. -/
def mulDistribMulActionOfMulAut (φ : G →* MulAut N) : MulDistribMulAction G N where
  smul g n := φ g n
  one_smul n := by change φ 1 n = n; simp
  mul_smul g h n := by change φ (g * h) n = φ g (φ h n); rw [map_mul, MulAut.mul_apply]
  smul_one g := by change φ g 1 = 1; simp
  smul_mul g n m := by change φ g (n * m) = φ g n * φ g m; exact (φ g).map_mul n m

/-- The `ℤ`-linear `G`-representation on `Additive N` induced by `φ`. -/
noncomputable def repOfMulAut (φ : G →* MulAut N) : Rep ℤ G :=
  letI := mulDistribMulActionOfMulAut φ
  Rep.ofMulDistribMulAction G N
end Castro2006


