-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:42.371803+00:00
-- url     : https://prove2.me/theorems/ed5396f6-704a-43ca-ab11-654fd32099d8
-- title:
--   Is Cong Ideal Two Torsion
-- statement:
--   Definitions and structural lemmas for Is Cong Ideal Two Torsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsCongIdealTwoTorsion.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
namespace GlobalTheory.CompanionTheory.Iwahori
structure IsPieces {E ι : Type} [Ring E] [Fintype ι] (P : ι → E) : Prop where
  orth : ∀ i j, i ≠ j → P i * P j = 0
  idem : ∀ i, P i * P i = P i
  sum : ∑ i, P i = 1
def IsUpper {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (a : E) : Prop :=
  ∀ i j, wt j < wt i → P i * a * P j = 0
def IsLower {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  ∀ i j, wt i < wt j → P i * b * P j = 0
def IsLowerUni {E ι : Type} [Ring E] (wt : ι → ℕ) (P : ι → E) (b : E) : Prop :=
  IsLower wt P b ∧ ∀ i, P i * b * P i = P i
structure IsCongIdeal {E ι : Type} [Ring E] (J : AddSubgroup E) (P : ι → E) : Prop where
  mul_mem : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J
  left_mem : ∀ i, ∀ x ∈ J, P i * x ∈ J
  right_mem : ∀ i, ∀ x ∈ J, x * P i ∈ J
  inv : ∀ x ∈ J, ∃ y ∈ J, (1 + x) * (1 + y) = 1 ∧ (1 + y) * (1 + x) = 1
def twoTorsion : AddSubgroup (Fin 2 → ZMod 4) := (AddMonoidHom.mulLeft (2 : Fin 2 → ZMod 4)).ker
abbrev Idx (l : ℕ) := Option (Fin l ⊕ Fin l)
def wt {l : ℕ} : Idx l → ℕ
  | some (Sum.inl i) => i
  | none => l
  | some (Sum.inr i) => 2 * l - i
def rev {l : ℕ} : Idx l → Idx l
  | some (Sum.inl i) => some (Sum.inr i)
  | none => none
  | some (Sum.inr i) => some (Sum.inl i)
section Concrete
variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
def tau {l : ℕ} (s : L →+* L) (u : Fin l → L) : Idx l → L
  | some (Sum.inl i) => u i
  | none => 1
  | some (Sum.inr i) => (s (u i))⁻¹
def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x : V) : V →ₗ[L] L where
  toFun := h x
  map_add' := hh.1 x
  map_smul' a y := by simpa using hh.2.1 a x y
def projE {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := (s δ)⁻¹ • (hLin hh (f i)).smulRight (e i)
def projF {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) (i : Fin l) :
    Module.End L V := δ⁻¹ • (hLin hh (e i)).smulRight (f i)
def piece {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (δ : L) {l : ℕ} (e f : Fin l → V) :
    Idx l → Module.End L V
  | some (Sum.inl i) => projE hh δ e f i
  | none => 1 - ∑ i, (projE hh δ e f i + projF hh δ e f i)
  | some (Sum.inr i) => projF hh δ e f i
def congJ (Λ : AddSubgroup V) (π : L) : AddSubgroup (Module.End L V) where
  carrier := {g | ∀ x ∈ Λ, ∃ y ∈ Λ, g x = π • y}
  zero_mem' x _ := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' {g g'} hg hg' x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    obtain ⟨y', hy', e2⟩ := hg' x hx
    exact ⟨y + y', Λ.add_mem hy hy', by simp [e1, e2, smul_add]⟩
  neg_mem' {g} hg x hx := by
    obtain ⟨y, hy, e1⟩ := hg x hx
    exact ⟨-y, Λ.neg_mem hy, by simp [e1]⟩
end Concrete
end GlobalTheory.CompanionTheory.Iwahori
end


