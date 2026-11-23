-- Prove2me | Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds
-- name    : Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:58.50069+00:00
-- url     : https://prove2.me/theorems/897a9f20-5eae-4080-826b-2efea9f1dcfd
-- title:
--   Wach Module Statement Holds
-- statement:
--   Definitions and structural lemmas for Wach Module Statement Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachModuleLifts/WachModuleProofs/WachModuleStatementHolds.lean

import Definitions.Def_Formalism_WachModuleLifts_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CL.W
section Lift
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
  {D' : Type} [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']
end Lift
section Claim
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
def QS (W : WachMod B η D) : Submodule ℤ_[p] D where
  carrier := {y | B.q ^ η • y ∈ W.N}
  add_mem' := by
    intro x y hx hy; show B.q ^ η • (x + y) ∈ W.N; rw [smul_add]; exact W.N.add_mem hx hy
  zero_mem' := by show B.q ^ η • (0 : D) ∈ W.N; simp
  smul_mem' := by
    intro c y hy; show B.q ^ η • (c • y) ∈ W.N; rw [smul_comm]; exact W.N.smul_of_tower_mem c hy
end Claim
section Gamma
end Gamma
section Wit
open Polynomial
variable (p : ℕ) [Fact p.Prime]
abbrev K := FractionRing (Polynomial ℤ_[p])
example : IsScalarTower ℤ_[p] (Polynomial ℤ_[p]) (K p) := inferInstance
def polyW : WachMod (polyBase p) 0 (K p) where
  N := LinearMap.range (Algebra.linearMap (Polynomial ℤ_[p]) (K p))
  φ := 0
  γ := LinearMap.id
  φ_smul := by intros; simp
  γ_smul := by intros; simp [polyBase]
  comm := by intros; simp
  π₀_inj := by
    intro x hx
    simp only [polyBase, Algebra.smul_def] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd ((IsFractionRing.injective (Polynomial ℤ_[p]) (K p)) (h.trans (map_zero _).symm)) X_ne_zero
    · exact h
  q_bij := by
    have hne : (algebraMap (Polynomial ℤ_[p]) (K p)) (X + C (p : ℤ_[p])) ≠ 0 := by
      intro h
      have := (IsFractionRing.injective (Polynomial ℤ_[p]) (K p)) (h.trans (map_zero _).symm)
      exact X_add_C_ne_zero _ this
    refine ⟨fun a b h => ?_, fun b => ⟨(algebraMap _ (K p) (X + C (p : ℤ_[p])))⁻¹ * b, ?_⟩⟩
    · simp only [polyBase, Algebra.smul_def] at h
      exact mul_left_cancel₀ hne h
    · simp only [polyBase, Algebra.smul_def]; field_simp
  φ_N := by intro x hx; simp
  γ_N := by intro x hx; exact ⟨0, Submodule.zero_mem _, by simp⟩
  γ_qN := by intro y hy; exact ⟨0, by simp, by simp⟩
end Wit
end Formalism.CL.W


