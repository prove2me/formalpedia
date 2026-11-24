-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:46.527997+00:00
-- url     : https://prove2.me/theorems/e25210ef-b34f-43fa-8ed8-29e5da2bcca6
-- title:
--   Box Cancel
-- statement:
--   Definitions and structural lemmas for Box Cancel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/BoxCancel.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
def dv (w w' : V R κ) : V R (κ ⊕ κ) := (Sum.elim w.1 w'.1, Sum.elim w.2 (-w'.2))
def dE (R κ : Type) [CommRing R] : (V R κ × V R κ) ≃ₗ[R] V R (κ ⊕ κ) where
  toFun p := dv p.1 p.2
  invFun u := ((u.1 ∘ Sum.inl, u.2 ∘ Sum.inl), (u.1 ∘ Sum.inr, -(u.2 ∘ Sum.inr)))
  map_add' p q := by ext (k | k) <;> simp [dv, add_comm]
  map_smul' a p := by ext (k | k) <;> simp [dv]
  left_inv p := by ext k <;> simp [dv]
  right_inv u := by ext (k | k) <;> simp [dv]
theorem exists_dv (u : V R (κ ⊕ κ)) : ∃ w w', u = dv w w' := ⟨_, _, ((dE R κ).apply_symm_apply u).symm⟩
def dbS (S : V R κ ≃ₗ[R] V R κ) : V R (κ ⊕ κ) ≃ₗ[R] V R (κ ⊕ κ) := (dE R κ).symm ≪≫ₗ S.prodCongr S ≪≫ₗ dE R κ
theorem dbS_dv (S : V R κ ≃ₗ[R] V R κ) (w w' : V R κ) : dbS S (dv w w') = dv (S w) (S w') := by
  show dE R κ (S.prodCongr S ((dE R κ).symm (dE R κ (w, w')))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl
def kE (R : Type) [CommRing R] (p : κ → Prop) [DecidablePred p] : V R (κ ⊕ κ) ≃ₗ[R] V R (κ ⊕ κ) where
  toFun w := (Sum.elim (fun k => w.1 (.inl k) - w.1 (.inr k)) fun k => if p k then w.2 (.inl k) + w.2 (.inr k) else w.1 (.inr k),
    Sum.elim (fun k => w.2 (.inl k)) fun k => if p k then -w.1 (.inr k) else w.2 (.inl k) + w.2 (.inr k))
  invFun u := (Sum.elim (fun k => u.1 (.inl k) + if p k then -u.2 (.inr k) else u.1 (.inr k))
      fun k => if p k then -u.2 (.inr k) else u.1 (.inr k),
    Sum.elim (fun k => u.2 (.inl k)) fun k => (if p k then u.1 (.inr k) else u.2 (.inr k)) - u.2 (.inl k))
  map_add' a b := by ext (k | k) <;> by_cases h : p k <;> simp [h] <;> ring
  map_smul' a b := by ext (k | k) <;> by_cases h : p k <;> simp [h] <;> ring
  left_inv a := by ext (k | k) <;> by_cases h : p k <;> simp [h]
  right_inv a := by ext (k | k) <;> by_cases h : p k <;> simp [h]
def fE (R κ : Type) [CommRing R] : V R κ ≃ₗ[R] V R κ where
  toFun w := (w.2, -w.1)
  invFun w := (-w.2, w.1)
  map_add' a b := by ext <;> simp [add_comm]
  map_smul' a b := by ext <;> simp
  left_inv a := by simp
  right_inv a := by simp
variable [Fintype κ] [Fintype κ₁]
theorem IsSp.dbS {S : V R κ ≃ₗ[R] V R κ} (h : IsSp S) : IsSp (dbS S) := fun u u' => by
  obtain ⟨a, b, rfl⟩ := exists_dv u
  obtain ⟨a', b', rfl⟩ := exists_dv u'
  rw [dbS_dv, dbS_dv]
  simp only [dv, sumElim_dotProduct_sumElim, dotProduct_neg]
  linear_combination h a a' - h b b'
variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
  {E : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ)}
end PositivityTheory.ThKF0.Chr


