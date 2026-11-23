-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
-- name    : GroupTheoreticShannonCapacity_P0Matrix
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:25:39.605286+00:00
-- url     : https://prove2.me/theorems/aeb7a2ef-059b-44d2-a857-cdae26ab6f1f
-- title:
--   P0 Matrix
-- statement:
--   Definitions and structural lemmas for P0 Matrix, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/P0Matrix.lean

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
def principalSubmatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    Matrix (Fin S.card) (Fin S.card) ℝ :=
  M.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)
def IsP0Matrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ S : Finset (Fin n), (principalSubmatrix n M S).det ≥ 0
theorem perm_mem_of_fixing (n : ℕ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (hfix : ∀ i ∈ Sᶜ, σ i = i) (x : Fin n) : x ∈ S ↔ σ x ∈ S := by
  constructor
  · intro hx
    by_contra hσx
    have hσxc : σ x ∈ Sᶜ := Finset.mem_compl.mpr hσx
    have hσ_fix := hfix (σ x) hσxc
    rw [σ.apply_eq_iff_eq] at hσ_fix
    rw [hσ_fix, Finset.mem_compl] at hσxc
    exact hσxc hx
  · intro hσx
    by_contra hx
    have hxc : x ∈ Sᶜ := Finset.mem_compl.mpr hx
    have heq := hfix x hxc
    rw [heq] at hσx
    exact hx hσx
noncomputable def orderEmbEquiv (n : ℕ) (S : Finset (Fin n)) : S ≃ Fin S.card :=
  (S.orderIsoOfFin rfl).toEquiv.symm
noncomputable def fixingPermEquiv (n : ℕ) (S : Finset (Fin n)) :
    {σ : Equiv.Perm (Fin n) // ∀ i ∈ Sᶜ, σ i = i} ≃ Equiv.Perm (Fin S.card) := by
  -- Use subtypePerm to get Perm ↥S, then conjugate with orderEmbEquiv
  have hS_eq : ∀ σ : Equiv.Perm (Fin n), (∀ i ∈ Sᶜ, σ i = i) →
      ∀ x, σ x ∈ S ↔ x ∈ S := fun σ hfix x => (perm_mem_of_fixing n σ S hfix x).symm
  refine Equiv.trans ?_ (Equiv.permCongr (orderEmbEquiv n S))
  exact {
    toFun := fun ⟨σ, hfix⟩ => σ.subtypePerm (hS_eq σ hfix)
    invFun := fun τ => ⟨Equiv.Perm.ofSubtype τ,
      fun i hi => Equiv.Perm.ofSubtype_apply_of_not_mem τ (Finset.mem_compl.mp hi)⟩
    left_inv := fun ⟨σ, hfix⟩ => by
      simp only [Subtype.mk.injEq]
      ext x
      by_cases hx : x ∈ S
      · rw [Equiv.Perm.ofSubtype_apply_of_mem (σ.subtypePerm (hS_eq σ hfix)) hx]
        simp only [Equiv.Perm.subtypePerm_apply]
      · have hxc : x ∈ Sᶜ := Finset.mem_compl.mpr hx
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem (σ.subtypePerm (hS_eq σ hfix)) hx, hfix x hxc]
    right_inv := fun τ => by
      ext ⟨x, hx⟩
      rw [Equiv.Perm.subtypePerm_apply]
      simp only [Equiv.Perm.ofSubtype_apply_of_mem τ hx]
  }
end GroupTheoreticShannonCapacity.P0Matrix


