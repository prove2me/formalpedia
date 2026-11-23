-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableEqCardHom
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableEqCardHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:19.635738+00:00
-- url     : https://prove2.me/theorems/7196f601-8371-40b5-8e71-122d52ee5543
-- title:
--   Card Stable Eq Card Hom
-- statement:
--   Definitions and structural lemmas for Card Stable Eq Card Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardStableEqCardHom.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
namespace GlobalTheory.StableGraph
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁]
  [Algebra O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}
theorem mem_of_inl {M : Submodule O (A₁ × A₂)} (h : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    {a : A₁} (ha : (a, (0 : A₂)) ∈ M) : a ∈ M₁ := by
  rw [← h]; exact ha
theorem mem_of_snd {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    {a : A₁} {x : A₂} (hx : (a, x) ∈ M) : x ∈ M₂ := by
  rw [← h]; exact Submodule.mem_map_of_mem (f := LinearMap.snd O A₁ A₂) hx
theorem exists_of_map {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : ∃ a : A₁, (a, (x : A₂)) ∈ M := by
  have hx : (x : A₂) ∈ M.map (LinearMap.snd O A₁ A₂) := h ▸ x.2
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.1 hx
  have hp' : p = (p.1, (x : A₂)) := Prod.ext rfl hpx
  exact ⟨p.1, hp' ▸ hp⟩
noncomputable def classOf {M : Submodule O (A₁ × A₂)} (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : A₁ ⧸ M₁ :=
  Submodule.Quotient.mk (exists_of_map h₂ x).choose
theorem classOf_eq {M : Submodule O (A₁ × A₂)} (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) {x : M₂} {a : A₁} (hp : (a, (x : A₂)) ∈ M) :
    classOf (M₁ := M₁) h₂ x = Submodule.Quotient.mk a := by
  unfold classOf
  rw [Submodule.Quotient.eq]
  apply mem_of_inl h₁
  have := M.sub_mem (exists_of_map h₂ x).choose_spec hp
  simpa using this
noncomputable def toHom (M : Submodule O (A₁ × A₂)) (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun := classOf h₂
  map_add' x y := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    obtain ⟨b, hb⟩ := exists_of_map h₂ y
    rw [classOf_eq h₁ h₂ ha, classOf_eq h₁ h₂ hb, ← Submodule.Quotient.mk_add]
    exact classOf_eq h₁ h₂ (by simpa using M.add_mem ha hb)
  map_smul' c x := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    rw [classOf_eq h₁ h₂ ha, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact classOf_eq h₁ h₂ (by simpa using M.smul_mem c ha)
def graph (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : Submodule O (A₁ × A₂) where
  carrier := {p | ∃ h : p.2 ∈ M₂, Submodule.Quotient.mk p.1 = φ ⟨p.2, h⟩}
  add_mem' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨hx, ha⟩ ⟨hy, hb⟩
    refine ⟨M₂.add_mem hx hy, ?_⟩
    have e : (⟨x + y, M₂.add_mem hx hy⟩ : M₂) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    simp only [Prod.fst_add, Prod.snd_add] at *
    rw [e, map_add, Submodule.Quotient.mk_add, ha, hb]
  zero_mem' := ⟨M₂.zero_mem, by
    have e : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
    simp only [Prod.fst_zero, Prod.snd_zero]
    rw [e, map_zero, Submodule.Quotient.mk_zero]⟩
  smul_mem' := by
    rintro c ⟨a, x⟩ ⟨hx, ha⟩
    refine ⟨M₂.smul_mem c hx, ?_⟩
    have e : (⟨c • x, M₂.smul_mem c hx⟩ : M₂) = c • ⟨x, hx⟩ := rfl
    simp only [Prod.smul_fst, Prod.smul_snd] at *
    rw [e, map_smul, Submodule.Quotient.mk_smul, ha]
theorem mem_graph {φ : M₂ →ₗ[O] A₁ ⧸ M₁} {a : A₁} {x : A₂} :
    (a, x) ∈ graph φ ↔ ∃ h : x ∈ M₂, Submodule.Quotient.mk a = φ ⟨x, h⟩ := Iff.rfl
theorem graph_comap (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).comap (LinearMap.inl O A₁ A₂) = M₁ := by
    ext a
    simp only [Submodule.mem_comap, LinearMap.inl_apply]
    rw [mem_graph]
    constructor
    · rintro ⟨h, e⟩
      have e0 : (⟨0, h⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero] at e
      exact e
    · intro ha
      refine ⟨M₂.zero_mem, ?_⟩
      have e0 : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero]
      exact ha
theorem graph_map (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).map (LinearMap.snd O A₁ A₂) = M₂ := by
    ext x
    constructor
    · rintro ⟨p, ⟨h, _⟩, rfl⟩
      exact h
    · intro hx
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ ⟨x, hx⟩)
      exact ⟨(a, x), ⟨hx, ha⟩, rfl⟩
noncomputable def stableEquiv (g₁ : A₁) (g₂ : A₂) (hM₂ : ∀ y ∈ M₂, g₂ * y ∈ M₂) :
    {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} ≃
      {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁,
        φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} where
  toFun M := ⟨toHom M.1 M.2.2.1 M.2.2.2, by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    intro x y hy a ha
    obtain ⟨c, hc⟩ := exists_of_map h₂ x
    have hφx : toHom M h₁ h₂ x = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
    rw [hφx, Submodule.Quotient.eq] at ha
    have h1 : (c - a, (0 : A₂)) ∈ M := by rw [← h₁] at ha; exact ha
    have h2 := hst _ hc
    have h3 := hst _ h1
    have h4 : (g₁ * a, (y : A₂)) ∈ M := by
      have := M.sub_mem h2 h3
      rw [hy]
      convert this using 1
      ext
      · simp only [Prod.fst_sub, Prod.fst_mul]; ring
      · simp
    exact classOf_eq h₁ h₂ h4⟩
  invFun φ := ⟨graph φ.1, by
    rintro ⟨a, x⟩ ⟨hx, ha⟩
    exact ⟨hM₂ x hx, (φ.2 ⟨x, hx⟩ ⟨g₂ * x, hM₂ x hx⟩ rfl a ha.symm).symm⟩,
    graph_comap φ.1, graph_map φ.1⟩
  left_inv M := by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    apply Subtype.ext
    ext ⟨a, x⟩
    show (a, x) ∈ graph (toHom M h₁ h₂) ↔ (a, x) ∈ M
    rw [mem_graph]
    constructor
    · rintro ⟨hx, e⟩
      obtain ⟨c, hc⟩ := exists_of_map h₂ ⟨x, hx⟩
      have hφx : toHom M h₁ h₂ ⟨x, hx⟩ = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
      rw [hφx, Submodule.Quotient.eq] at e
      have h1 : (a - c, (0 : A₂)) ∈ M := by rw [← h₁] at e; exact e
      have := M.add_mem h1 hc
      simpa using this
    · intro hm
      exact ⟨mem_of_snd h₂ hm, (classOf_eq h₁ h₂ hm).symm⟩
  right_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ.1 x)
    have hm : (a, (x : A₂)) ∈ graph φ.1 := ⟨x.2, ha⟩
    exact (classOf_eq (graph_comap φ.1) (graph_map φ.1) hm).trans ha
end GlobalTheory.StableGraph


