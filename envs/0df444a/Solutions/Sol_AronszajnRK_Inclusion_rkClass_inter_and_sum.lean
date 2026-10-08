-- Prove2me | solution 1 for AronszajnRK.Inclusion.rkClass_inter_and_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:13:51.244534+00:00
-- url     : https://prove2.me/submissions/9f050b8f-56c4-4d99-9f9a-7431dc79de23

import Mathlib
import Definitions.Def_AronszajnRK_Inclusion_IsRKClass

set_option autoImplicit false

universe u

namespace AronszajnRK.Inclusion.RKAux750

open AronszajnRK.Inclusion

lemma isRKClass_range {X : Type u} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] (X → ℂ)) : IsRKClass (Set.range T) := by
  classical
  set K : Submodule ℂ E := T.ker with hK
  have : CompleteSpace K := (T.isComplete_ker).completeSpace_coe
  have hinj : Function.Injective (T ∘L Kᗮ.subtypeL) := by
    refine (injective_iff_map_eq_zero _).mpr fun w hw => ?_
    have h1 : (w : E) ∈ K := by
      show (w : E) ∈ T.ker
      exact LinearMap.mem_ker.mpr hw
    exact Subtype.ext (Submodule.disjoint_def.mp K.orthogonal_disjoint _ h1 w.2)
  let inst : RKHS ℂ Kᗮ X ℂ := ⟨T ∘L Kᗮ.subtypeL, hinj⟩
  refine ⟨Kᗮ, inferInstance, inferInstance, inferInstance, inst, ?_⟩
  ext φ
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨(f : E), rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) v
    have hy' : T y = 0 := LinearMap.mem_ker.mp hy
    refine ⟨⟨z, hz⟩, ?_⟩
    show T z = T (y + z)
    rw [map_add, hy', zero_add]

lemma exists_clm {X : Type u} {S : Set (X → ℂ)} (h : IsRKClass S) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ι : H →L[ℂ] (X → ℂ)), Set.range ι = S := by
  obtain ⟨H, i1, i2, i3, i4, rfl⟩ := h
  exact ⟨H, i1, i2, i3, RKHS.coeCLM ℂ, rfl⟩

lemma sum_part {X : Type u} {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (ι₁ : H₁ →L[ℂ] (X → ℂ)) (ι₂ : H₂ →L[ℂ] (X → ℂ)) :
    IsRKClass {f | ∃ f₁ ∈ Set.range ι₁, ∃ f₂ ∈ Set.range ι₂, f = f₁ + f₂} := by
  set T : WithLp 2 (H₁ × H₂) →L[ℂ] (X → ℂ) :=
    ι₁ ∘L WithLp.fstL 2 ℂ H₁ H₂ + ι₂ ∘L WithLp.sndL 2 ℂ H₁ H₂ with hT
  have hS : {f | ∃ f₁ ∈ Set.range ι₁, ∃ f₂ ∈ Set.range ι₂, f = f₁ + f₂} = Set.range T := by
    ext φ
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact ⟨WithLp.toLp 2 (a, b), by simp [T]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨_, ⟨v.fst, rfl⟩, _, ⟨v.snd, rfl⟩, by simp [T]⟩
  rw [hS]
  exact isRKClass_range T

lemma inter_part {X : Type u} {H₁ H₂ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (ι₁ : H₁ →L[ℂ] (X → ℂ)) (ι₂ : H₂ →L[ℂ] (X → ℂ)) :
    IsRKClass (Set.range ι₁ ∩ Set.range ι₂) := by
  set D : WithLp 2 (H₁ × H₂) →L[ℂ] (X → ℂ) :=
    ι₁ ∘L WithLp.fstL 2 ℂ H₁ H₂ - ι₂ ∘L WithLp.sndL 2 ℂ H₁ H₂ with hD
  set M : Submodule ℂ (WithLp 2 (H₁ × H₂)) := D.ker with hM
  have : CompleteSpace M := (D.isComplete_ker).completeSpace_coe
  set T : M →L[ℂ] (X → ℂ) := ι₁ ∘L WithLp.fstL 2 ℂ H₁ H₂ ∘L M.subtypeL with hT
  have hS : Set.range ι₁ ∩ Set.range ι₂ = Set.range T := by
    ext φ
    constructor
    · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hmem : WithLp.toLp 2 (a, b) ∈ M := by
        show D (WithLp.toLp 2 (a, b)) = 0
        simp [D, hb]
      exact ⟨⟨WithLp.toLp 2 (a, b), hmem⟩, by simp [T]⟩
    · rintro ⟨⟨v, hv⟩, rfl⟩
      have hv' : D v = 0 := hv
      have : ι₁ v.fst = ι₂ v.snd := sub_eq_zero.mp (by simpa [D] using hv')
      exact ⟨⟨v.fst, by simp [T]⟩, ⟨v.snd, by simp [T, this]⟩⟩
  rw [hS]
  exact isRKClass_range T

end AronszajnRK.Inclusion.RKAux750

open AronszajnRK.Inclusion in
theorem solution {X : Type*} (S₁ S₂ : Set (X → ℂ))
    (h₁ : IsRKClass S₁) (h₂ : IsRKClass S₂) :
    IsRKClass (S₁ ∩ S₂) ∧ IsRKClass {f | ∃ f₁ ∈ S₁, ∃ f₂ ∈ S₂, f = f₁ + f₂} := by
  obtain ⟨H₁, i1, i2, i3, ι₁, rfl⟩ := AronszajnRK.Inclusion.RKAux750.exists_clm h₁
  obtain ⟨H₂, j1, j2, j3, ι₂, rfl⟩ := AronszajnRK.Inclusion.RKAux750.exists_clm h₂
  exact ⟨AronszajnRK.Inclusion.RKAux750.inter_part ι₁ ι₂,
    AronszajnRK.Inclusion.RKAux750.sum_part ι₁ ι₂⟩
