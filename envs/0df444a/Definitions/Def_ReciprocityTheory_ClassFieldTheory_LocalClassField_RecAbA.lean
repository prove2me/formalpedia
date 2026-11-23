-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecAbA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_RecAbA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:19.670803+00:00
-- url     : https://prove2.me/theorems/96810536-1142-4997-a3b5-f72676b8c0bc
-- title:
--   Rec Ab A
-- statement:
--   Definitions and structural lemmas for Rec Ab A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RecAbA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
noncomputable section
theorem qz_mk_eq_zero_iff (q : ℚ) : (QuotientAddGroup.mk q : QZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff]; rfl
theorem qz_nsmul_mk (l : ℕ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← nsmul_eq_mul]; rfl
theorem qz_zsmul_mk (l : ℤ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← zsmul_eq_mul]; rfl
theorem qz_exists_zsmul (n : ℕ) (hn : n ≠ 0) (x : QZ) (hx : n • x = 0) :
    ∃ k : ℤ, x = k • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  rw [qz_zsmul_mk, hk]
  have : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  congr 1
  field_simp
theorem qz_nsmul_inv_eq_zero_iff (n : ℕ) (hn : n ≠ 0) (l : ℕ) :
    l • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) = 0 ↔ n ∣ l := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have h : ((k * n : ℤ) : ℚ) = ((l : ℤ) : ℚ) := by
      push_cast
      rw [hk]
      field_simp
    have h' : k * n = (l : ℤ) := Int.cast_injective h
    exact Int.natCast_dvd_natCast.1 ⟨k, by rw [← h', mul_comm]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    field_simp
scoped instance hasEnoughRootsOfUnity_QZ (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (Multiplicative QZ) n where
  prim := ⟨Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n)),
    { pow_eq_one := by
        rw [← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]; rfl
      dvd_of_pow_eq_one := fun l hl => by
        rw [← ofAdd_nsmul] at hl
        exact (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) l).1 (Multiplicative.ofAdd.injective hl) }⟩
  cyc := by
    have h0 : (toUnits (Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ))) ∈
        rootsOfUnity n (Multiplicative QZ) := by
      rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]
      exact map_one _
    refine ⟨⟨⟨_, h0⟩, fun x => ?_⟩⟩
    have hx : n • Multiplicative.toAdd (x.1 : Multiplicative QZ) = 0 := by
      have := x.2
      rw [mem_rootsOfUnity] at this
      have h2 := congrArg (fun u : (Multiplicative QZ)ˣ => Multiplicative.toAdd (u : Multiplicative QZ)) this
      simpa using h2
    obtain ⟨k, hk⟩ := qz_exists_zsmul n (NeZero.ne n) _ hx
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply Multiplicative.toAdd.injective
    rw [hk]
    simp
section fin
variable (A : Type) [AddCommGroup A] [Finite A]
def homEquivUnits : (A →+ QZ) ≃ (Multiplicative A →* (Multiplicative QZ)ˣ) :=
  AddMonoidHom.toMultiplicative.trans (toUnits (G := Multiplicative QZ)).monoidHomCongrRight.toEquiv
scoped instance : NeZero (Monoid.exponent (Multiplicative A)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
theorem card_hom_QZ : Nat.card (A →+ QZ) = Nat.card A := by
  rw [Nat.card_congr (homEquivUnits A),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative A) (Multiplicative QZ)]
  rfl
scoped instance finite_hom_QZ : Finite (A →+ QZ) :=
  Nat.finite_of_card_ne_zero (by rw [card_hom_QZ]; exact Nat.card_pos.ne')
variable {A}
end fin
section top
variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))
def pullChar : (A →+ QZ) →+ charGrp G where
  toFun ψ := ⟨ψ.comp π, hc.comp ψ⟩
  map_zero' := rfl
  map_add' _ _ := rfl
variable {π}
include hc
end top
section quot
variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]
abbrev quotAddCommGroup (h : commutator G ≤ H) : AddCommGroup (Additive (G ⧸ H)) :=
  { (inferInstance : AddGroup (Additive (G ⧸ H))) with
    add_comm := fun a b => by
      have := (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H)).2 h
      exact congrArg Additive.ofMul (this.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }
end quot
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


