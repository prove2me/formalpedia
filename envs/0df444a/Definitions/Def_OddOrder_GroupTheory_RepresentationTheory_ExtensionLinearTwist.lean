-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtensionLinearTwist
-- name    : OddOrder_GroupTheory_RepresentationTheory_ExtensionLinearTwist
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:40:41.17404+00:00
-- url     : https://prove2.me/theorems/2fe56b78-d505-485f-879f-3cccd6397f26
-- title:
--   Extensions of an irreducible character differ by a linear character
-- statement:
--   Classification of extensions (Isaacs, *Character Theory*, Ch. 6, following Gallagher): let $H\trianglelefteq K$ and let $\chi_1,\chi_2\in\mathrm{Irr}(K)$ restrict to the same irreducible character of $H$. Then $\chi_2=\chi_1\beta$ for a linear character $\beta$ of $K$ trivial on $H$. The proof is Schur's lemma.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ExtensionLinearTwist.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ExtensionLinearTwist.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicCharacterExtension

namespace OddOrder.RepresentationTheory

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

/-- **Extensions of an irreducible character differ by a linear character trivial on the
subgroup** ([Is] Cor 6.17 companion).  If `χ₁, χ₂ ∈ Irr(K)` have equal irreducible
restrictions to `H ⊴ K`, then there is `β : K →* ℂˣ` with `β|_H = 1` and
`χ₂ = χ₁ · β`. -/
theorem exists_linearClassFunction_mul_of_restrict_eq_restrict [Finite K]
    {χ₁ χ₂ : ClassFunction K ℂ}
    (h₁ : IsIrreducibleCharacter χ₁) (h₂ : IsIrreducibleCharacter χ₂)
    (hres : ClassFunction.restrict H χ₁ = ClassFunction.restrict H χ₂)
    (hirr : IsIrreducibleCharacter (ClassFunction.restrict H χ₁)) :
    ∃ β : K →* ℂˣ, (∀ h : ↥H, β (h : K) = 1) ∧
      χ₂ = χ₁ * linearClassFunction β := by
  classical
  obtain ⟨V₁, _, _, _, ρ₁, hρ₁, hc₁⟩ := h₁
  obtain ⟨V₂, _, _, _, ρ₂, hρ₂, hc₂⟩ := h₂
  obtain ⟨Vθ, _, _, _, ρθ, hρθ, hcθ⟩ := hirr
  have := hρ₁; have := hρ₂; have := hρθ
  have : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set res₁ : Representation ℂ ↥H V₁ := ρ₁.comp H.subtype with hres₁def
  set res₂ : Representation ℂ ↥H V₂ := ρ₂.comp H.subtype with hres₂def
  -- both restrictions afford the character of `ρθ`
  have hchar₁ : res₁.character = ρθ.character := by
    funext h
    calc res₁.character h = χ₁ ((h : K)) := (congrFun hc₁ ((h : K))).symm
      _ = (ClassFunction.restrict H χ₁) h := (ClassFunction.restrict_apply H χ₁ h).symm
      _ = ρθ.character h := congrFun hcθ h
  have hchar₂ : res₂.character = ρθ.character := by
    funext h
    calc res₂.character h = χ₂ ((h : K)) := (congrFun hc₂ ((h : K))).symm
      _ = (ClassFunction.restrict H χ₂) h := (ClassFunction.restrict_apply H χ₂ h).symm
      _ = (ClassFunction.restrict H χ₁) h := by rw [hres]
      _ = ρθ.character h := congrFun hcθ h
  -- hence they are equivalent to `ρθ` (strong form: no irreducibility of the restriction
  -- assumed), and in particular irreducible
  obtain ⟨Φ₁⟩ := nonempty_equiv_of_character_eq ρθ res₁ hchar₁
  obtain ⟨Φ₂⟩ := nonempty_equiv_of_character_eq ρθ res₂ hchar₂
  have hResIrr₁ : Representation.IsIrreducible res₁ :=
    Representation.IsIrreducible.of_equiv Φ₁
  -- transport `ρ₂` onto `V₁` so that the restrictions agree on the nose
  set T : res₂.Equiv res₁ := Φ₂.symm.trans Φ₁ with hT
  set ρ₂' : Representation ℂ K V₁ := transportRep ρ₂ T.toLinearEquiv with hρ₂'
  have hchar₂' : ρ₂'.character = ρ₂.character := transportRep_character ρ₂ T.toLinearEquiv
  have hagree : ∀ h : ↥H, ρ₂' ((h : K)) = ρ₁ ((h : K)) := by
    intro h
    rw [hρ₂', transportRep_apply]
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    have h10 := T.isIntertwining' h
    have h11 := LinearMap.congr_fun h10 (T.toLinearEquiv.symm v)
    simp only [LinearMap.comp_apply] at h11
    calc T.toLinearEquiv ((ρ₂ ((h : K))) (T.toLinearEquiv.symm v))
        = res₁ h (T.toLinearMap (T.toLinearEquiv.symm v)) := h11
      _ = ρ₁ ((h : K)) v := by
          rw [show T.toLinearMap (T.toLinearEquiv.symm v)
              = T.toLinearEquiv (T.toLinearEquiv.symm v) from rfl,
            T.toLinearEquiv.apply_symm_apply]
          rfl
  -- agreement at the level of `asGroupHom` units
  have hagreeU : ∀ h : ↥H, ρ₂'.asGroupHom ((h : K)) = ρ₁.asGroupHom ((h : K)) := fun h =>
    Units.ext (by
      rw [Representation.asGroupHom_apply, Representation.asGroupHom_apply, hagree h])
  -- the twisting unit `S y = ρ₂'(y) · ρ₁(y)⁻¹` commutes with the irreducible restriction,
  -- by normality and the agreement on `H`
  have hScomm : ∀ (y : K) (h : ↥H),
      ρ₁.asGroupHom ((h : K)) * (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹)
        = (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹) * ρ₁.asGroupHom ((h : K)) := by
    intro y h
    have hmem : y⁻¹ * (h : K) * y ∈ H := by
      simpa using hH.conj_mem (h : K) h.2 y⁻¹
    -- conjugation identities for both representations
    have hconj₁ : (ρ₁.asGroupHom y)⁻¹ * ρ₁.asGroupHom ((h : K)) * ρ₁.asGroupHom y
        = ρ₁.asGroupHom (y⁻¹ * (h : K) * y) := by
      rw [← map_inv, ← map_mul, ← map_mul]
    have hconj₂ : ρ₂'.asGroupHom y * ρ₂'.asGroupHom (y⁻¹ * (h : K) * y)
        = ρ₂'.asGroupHom ((h : K)) * ρ₂'.asGroupHom y := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have hagree' : ρ₂'.asGroupHom (y⁻¹ * (h : K) * y) = ρ₁.asGroupHom (y⁻¹ * (h : K) * y) :=
      hagreeU ⟨y⁻¹ * (h : K) * y, hmem⟩
    calc ρ₁.asGroupHom ((h : K)) * (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹)
        = ρ₁.asGroupHom ((h : K)) * ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹ := by group
      _ = ρ₂'.asGroupHom ((h : K)) * ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹ := by
          rw [hagreeU h]
      _ = ρ₂'.asGroupHom y * ρ₂'.asGroupHom (y⁻¹ * (h : K) * y) * (ρ₁.asGroupHom y)⁻¹ := by
          rw [hconj₂]
      _ = ρ₂'.asGroupHom y * ρ₁.asGroupHom (y⁻¹ * (h : K) * y) * (ρ₁.asGroupHom y)⁻¹ := by
          rw [hagree']
      _ = ρ₂'.asGroupHom y * ((ρ₁.asGroupHom y)⁻¹ * ρ₁.asGroupHom ((h : K))
            * ρ₁.asGroupHom y) * (ρ₁.asGroupHom y)⁻¹ := by
          rw [hconj₁]
      _ = (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹) * ρ₁.asGroupHom ((h : K)) := by group
  -- Schur: each `S y` is a nonzero scalar
  have hSchur : ∀ y : K, ∃ cy : ℂ,
      ((ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹ : (Module.End ℂ V₁)ˣ) : Module.End ℂ V₁)
      = cy • LinearMap.id := by
    intro y
    refine exists_smul_id_of_forall_mul_comm res₁ _ (fun h => ?_)
    have h12 := congrArg Units.val (hScomm y h)
    simpa only [hres₁def, MonoidHom.comp_apply, Subgroup.subtype_apply, Units.val_mul,
      Representation.asGroupHom_apply] using h12
  choose c hc using hSchur
  -- scalar bookkeeping: uniqueness, nonvanishing, multiplicativity, triviality on `H`
  have : Nontrivial V₁ := by
    have h13 : Nontrivial (Subrepresentation ρ₁) := IsSimpleOrder.toNontrivial
    have h14 : Nontrivial (Submodule ℂ V₁) :=
      (Subrepresentation.toSubmodule_injective (ρ := ρ₁)).nontrivial
    exact (Submodule.nontrivial_iff ℂ).mp h14
  have huniq : ∀ {a b : ℂ}, (a • LinearMap.id : Module.End ℂ V₁) = b • LinearMap.id →
      a = b := by
    intro a b hab
    obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    have h15 := LinearMap.congr_fun hab v
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h15
    exact smul_left_injective ℂ hv h15
  have : Nontrivial (Module.End ℂ V₁) := ⟨1, 0, fun h15 => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V₁)
    exact hv (by simpa using LinearMap.congr_fun h15 v)⟩
  have hc0 : ∀ y : K, c y ≠ 0 := by
    intro y h0
    have h16 := hc y
    rw [h0, zero_smul] at h16
    exact Units.ne_zero (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹) h16
  -- scalar units are central, hence `S` is (anti)multiplicative
  have hcentral : ∀ (y : K) (x : (Module.End ℂ V₁)ˣ),
      (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹) * x
        = x * (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹) := by
    intro y x
    apply Units.ext
    rw [Units.val_mul, hc y, Units.val_mul, hc y]
    apply LinearMap.ext
    intro v
    simp
  have hSmul : ∀ y₁ y₂ : K,
      ρ₂'.asGroupHom (y₁ * y₂) * (ρ₁.asGroupHom (y₁ * y₂))⁻¹
        = (ρ₂'.asGroupHom y₂ * (ρ₁.asGroupHom y₂)⁻¹)
            * (ρ₂'.asGroupHom y₁ * (ρ₁.asGroupHom y₁)⁻¹) := by
    intro y₁ y₂
    have h17 : ρ₂'.asGroupHom (y₁ * y₂) * (ρ₁.asGroupHom (y₁ * y₂))⁻¹
        = ρ₂'.asGroupHom y₁ * (ρ₂'.asGroupHom y₂ * (ρ₁.asGroupHom y₂)⁻¹)
            * (ρ₁.asGroupHom y₁)⁻¹ := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [h17, ← hcentral y₂ (ρ₂'.asGroupHom y₁)]
    group
  have hcmul : ∀ y₁ y₂ : K, c (y₁ * y₂) = c y₁ * c y₂ := by
    intro y₁ y₂
    have h18 : c (y₁ * y₂) = c y₂ * c y₁ := by
      apply huniq
      rw [← hc (y₁ * y₂), hSmul y₁ y₂, Units.val_mul, hc y₁, hc y₂]
      apply LinearMap.ext
      intro v
      simp [smul_smul, mul_comm]
    rw [h18, mul_comm]
  have hcone : c 1 = 1 := by
    apply huniq
    rw [← hc 1]
    have h19 : (ρ₂'.asGroupHom (1 : K) * (ρ₁.asGroupHom (1 : K))⁻¹ : (Module.End ℂ V₁)ˣ)
        = 1 := by
      simp
    rw [h19, one_smul]
    rfl
  have hcH : ∀ h : ↥H, c ((h : K)) = 1 := by
    intro h
    apply huniq
    rw [← hc ((h : K))]
    have h19 : (ρ₂'.asGroupHom ((h : K)) * (ρ₁.asGroupHom ((h : K)))⁻¹
        : (Module.End ℂ V₁)ˣ) = 1 := by
      rw [hagreeU h, mul_inv_cancel]
    rw [h19, one_smul]
    rfl
  -- package `β` and conclude by reading off traces
  refine ⟨{ toFun := fun y => Units.mk0 (c y) (hc0 y)
            map_one' := Units.ext (by simpa using hcone)
            map_mul' := fun y₁ y₂ => Units.ext (by simpa using hcmul y₁ y₂) },
    fun h => Units.ext (by simpa using hcH h), ?_⟩
  ext y
  rw [ClassFunction.mul_apply, linearClassFunction_apply]
  have h20 : ρ₂' y = c y • ρ₁ y := by
    have h21 : (ρ₂'.asGroupHom y * (ρ₁.asGroupHom y)⁻¹) * ρ₁.asGroupHom y
        = ρ₂'.asGroupHom y := by group
    have h22 := congrArg Units.val h21
    rw [Units.val_mul, hc y, Representation.asGroupHom_apply,
      Representation.asGroupHom_apply] at h22
    rw [← h22]
    apply LinearMap.ext
    intro v
    simp
  calc χ₂ y = ρ₂.character y := congrFun hc₂ y
    _ = ρ₂'.character y := (congrFun hchar₂' y).symm
    _ = LinearMap.trace ℂ V₁ (c y • ρ₁ y) := by rw [Representation.character, h20]
    _ = c y * ρ₁.character y := by rw [map_smul]; rfl
    _ = χ₁ y * (Units.mk0 (c y) (hc0 y) : ℂ) := by
        rw [← congrFun hc₁ y]
        exact mul_comm _ _

end OddOrder.RepresentationTheory


