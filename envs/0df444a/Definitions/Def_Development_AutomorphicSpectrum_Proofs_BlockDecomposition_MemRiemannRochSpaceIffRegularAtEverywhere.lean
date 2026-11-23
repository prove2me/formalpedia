-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:16.600161+00:00
-- url     : https://prove2.me/theorems/6f9f37df-c0f0-4ef8-9eef-018573ab7abf
-- title:
--   Mem Riemann Roch Space Iff Regular At Everywhere
-- statement:
--   Definitions and structural lemmas for Mem Riemann Roch Space Iff Regular At Everywhere, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs
namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit
variable {k : Type} [Field k] {n : ℕ}
theorem mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    x ∈ gmap g M ↔ (g⁻¹).val *ᵥ x ∈ M := by
  unfold gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hz
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
theorem gmap_mul {N : ℕ} (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    gmap (g * h) M = gmap g (gmap h M) := by
  ext x
  rw [mem_gmap, mem_gmap, mem_gmap, Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]
theorem gmap_one {N : ℕ} (M : Submodule k (Fin N → k)) : gmap (1 : GL (Fin N) k) M = M := by
  ext x
  rw [mem_gmap, inv_one, Units.val_one, Matrix.one_mulVec]
def gmapEquiv {N : ℕ} (g : GL (Fin N) k) : Submodule k (Fin N → k) ≃ Submodule k (Fin N → k) where
  toFun := gmap g
  invFun := gmap g⁻¹
  left_inv M := by rw [← gmap_mul, inv_mul_cancel, gmap_one]
  right_inv M := by rw [← gmap_mul, mul_inv_cancel, gmap_one]
section Lat
variable {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
def stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) : Submodule ℂ V where
  carrier := {y | ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y}
  add_mem' := by
    intro a b ha hb γ h
    rw [map_add, ha γ h, hb γ h]
  zero_mem' := by
    intro γ _
    simp
  smul_mem' := by
    intro c a ha γ h
    rw [map_smul, ha γ h]
variable [Fintype k]
def zx (v : Submodule k (Fin (n + 1) → k) → V) (x : Fin (n + 1) → k) (j : ℕ) : V :=
  ∑ M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => x ∈ M ∧ Module.finrank k M + j = n + 1), v M
def IsCov (red : Γ →* GL (Fin (n + 1)) k) (gam : (Fin (n + 1) → k) → Γ) : Prop :=
  ∀ a, a ≠ 0 → ∀ x, a ⬝ᵥ ((red (gam a)).val *ᵥ x) = x 0
def uop (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (gam : (Fin (n + 1) → k) → Γ) : Module.End ℂ V :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1), ρ (gam a) * t
end Lat
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
end


