-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:18.56817+00:00
-- url     : https://prove2.me/theorems/02221fd8-db72-4148-b248-9ec126a8da99
-- title:
--   Perp Surj
-- statement:
--   Definitions and structural lemmas for Perp Surj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PerpSurj.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.DimA
open Module
section Perp
variable {H : Type*} [AddCommGroup H] (B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ)
theorem alt_swap (halt : ∀ h, B h h = 0) (x y : H) : B x y = -B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  linear_combination h
def perp (e f : H) : Submodule ℤ H := LinearMap.ker (B.flip e) ⊓ LinearMap.ker (B.flip f)
theorem mem_perp {e f h : H} : h ∈ perp B e f ↔ B h e = 0 ∧ B h f = 0 := by
  simp [perp]
variable (halt : ∀ h, B h h = 0) (e f : H) (he : B e f = 1)
include halt he
theorem proj_mem (y : H) : y - B y f • e + B y e • f ∈ perp B e f := by
  have h1 : B f e = -1 := by rw [alt_swap B halt, he]
  rw [mem_perp]
  constructor <;> simp [halt, he, h1] <;> ring
def proj : H →ₗ[ℤ] perp B e f where
  toFun y := ⟨y - B y f • e + B y e • f, proj_mem B halt e f he y⟩
  map_add' x y := by ext; simp only [map_add, LinearMap.add_apply, add_smul, Submodule.coe_add]; abel
  map_smul' c x := by
    ext; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_smul, mul_smul,
      RingHom.id_apply, smul_add, smul_sub]
theorem proj_apply (y : H) : (proj B halt e f he y : H) = y - B y f • e + B y e • f := rfl
def splitEquiv : H ≃ₗ[ℤ] perp B e f × ℤ × ℤ where
  toFun y := (proj B halt e f he y, B y f, B y e)
  map_add' x y := by simp
  map_smul' c x := by simp
  invFun p := (p.1 : H) + p.2.1 • e - p.2.2 • f
  left_inv y := by simp only [proj_apply]; abel
  right_inv p := by
    obtain ⟨⟨p, hp⟩, a, c⟩ := p
    have h1 : B f e = -1 := by rw [alt_swap B halt, he]
    rw [mem_perp] at hp
    have hf : B (p + a • e - c • f) f = a := by
      simp [hp.2, he, halt]
    have hE : B (p + a • e - c • f) e = c := by
      simp [hp.1, h1, halt]
    simp only [Prod.mk.injEq]
    refine ⟨?_, hf, hE⟩
    ext
    rw [proj_apply, hf, hE]
    abel
end Perp
end ReciprocityTheory.ChartRestriction.G.I2.DimA


