-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_forall_eq_mul_of_presentations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0a1d035a-faf4-5c19-a7b4-724b9286295a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsIntegral Scheme functionField_isFractionRing_of_isAffineOpen IsAffineOpen Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ functionField isBasis_affineOpens Modules Opens"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf isSheaf"
namespace PresUniq
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"
open TopologicalSpace Opposite

variable {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)

theorem map_ne_zero (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    {U V : X.Opens} (h : V ≤ U) [hV : Nonempty V] {m : Γ(M, U)} (hm : m ≠ 0) :
    M.presheaf.map (homOfLE h).op m ≠ 0 := by
  haveI : Nonempty U := let ⟨⟨z, hz⟩⟩ := hV; ⟨⟨z, h hz⟩⟩
  intro h0
  apply hm
  apply hinj U inferInstance
  rw [map_zero, ← hnat U V h hV m, h0, map_zero]

theorem ratio_eq_of_affine (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (m₁ m₂ : Γ(M, U)) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    φ' U m₁ / φ U m₁ = φ' U m₂ / φ U m₂ := by
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have hφ₁ : φ U m₁ ≠ 0 := fun h => h₁ (hinj U inferInstance (h.trans (map_zero _).symm))
  have hφ₂ : φ U m₂ ≠ 0 := fun h => h₂ (hinj U inferInstance (h.trans (map_zero _).symm))

  obtain ⟨a', a, ha, hq⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) (φ U m₁ / φ U m₂)
  have ha0 : algebraMap Γ(X, U) X.functionField a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
  have hrel : algebraMap Γ(X, U) X.functionField a * φ U m₁ = algebraMap Γ(X, U) X.functionField a' * φ U m₂ := by
    rw [div_eq_div_iff ha0 hφ₂] at hq

    calc algebraMap Γ(X, U) X.functionField a * φ U m₁ = φ U m₁ * algebraMap Γ(X, U) X.functionField a :=
          mul_comm _ _
      _ = algebraMap Γ(X, U) X.functionField a' * φ U m₂ := hq.symm

  have hsec : a • m₁ = a' • m₂ := by
    apply hinj U inferInstance
    rw [hsmul, hsmul, hrel]
  have hrel' : algebraMap Γ(X, U) X.functionField a * φ' U m₁ = algebraMap Γ(X, U) X.functionField a' * φ' U m₂ := by
    rw [← hsmul', ← hsmul', hsec]
  have ha'0 : algebraMap Γ(X, U) X.functionField a' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    exact (mul_ne_zero ha0 hφ₁) hrel

  rw [div_eq_div_iff hφ₁ hφ₂]
  have e1 := congrArg (· * (φ' U m₁ * φ U m₂)) hrel
  have e2 := congrArg (· * (φ U m₁ * φ U m₂)) hrel'

  have e3 : algebraMap Γ(X, U) X.functionField a' * φ U m₂ * (φ' U m₁ * φ U m₂)
      = algebraMap Γ(X, U) X.functionField a' * φ' U m₂ * (φ U m₁ * φ U m₂) := by
    rw [← e1, ← e2]; ring
  have hne : algebraMap Γ(X, U) X.functionField a' * φ U m₂ ≠ 0 := mul_ne_zero ha'0 hφ₂
  have e4 : φ' U m₁ * φ U m₂ * (algebraMap Γ(X, U) X.functionField a' * φ U m₂)
      = φ' U m₂ * φ U m₁ * (algebraMap Γ(X, U) X.functionField a' * φ U m₂) := by
    calc φ' U m₁ * φ U m₂ * (algebraMap Γ(X, U) X.functionField a' * φ U m₂)
        = algebraMap Γ(X, U) X.functionField a' * φ U m₂ * (φ' U m₁ * φ U m₂) := by ring
      _ = algebraMap Γ(X, U) X.functionField a' * φ' U m₂ * (φ U m₁ * φ U m₂) := e3
      _ = φ' U m₂ * φ U m₁ * (algebraMap Γ(X, U) X.functionField a' * φ U m₂) := by ring
  exact mul_right_cancel₀ hne e4

variable (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
  (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
  (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
  (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
  (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
    φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
  (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
  (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))

include hnat hnat' hsmul hsmul' hinj in

theorem ratio_eq (U₁ U₂ : X.Opens) [Nonempty U₁] [Nonempty U₂] (m₁ : Γ(M, U₁)) (m₂ : Γ(M, U₂))
    (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) :
    φ' U₁ m₁ / φ U₁ m₁ = φ' U₂ m₂ / φ U₂ m₂ := by

  obtain ⟨⟨u, hu⟩⟩ := (inferInstance : Nonempty U₁)
  obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty U₂)
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U₁.isOpen U₂.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  obtain ⟨W, hWaff, hzW, hW⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show z ∈ U₁ ⊓ U₂ from hz)
  haveI : Nonempty W := ⟨⟨z, hzW⟩⟩
  have hW₁ : W ≤ U₁ := hW.trans inf_le_left
  have hW₂ : W ≤ U₂ := hW.trans inf_le_right
  have hr₁ := map_ne_zero M φ hnat hinj hW₁ h₁
  have hr₂ := map_ne_zero M φ hnat hinj hW₂ h₂
  rw [← hnat U₁ W hW₁ inferInstance m₁, ← hnat' U₁ W hW₁ inferInstance m₁,
    ← hnat U₂ W hW₂ inferInstance m₂, ← hnat' U₂ W hW₂ inferInstance m₂]
  exact ratio_eq_of_affine M φ φ' hsmul hsmul' hinj W hWaff _ _ hr₁ hr₂

include hnat hnat' hsmul hsmul' hinj hinj' in

theorem exists_eq_mul (U₀ : X.Opens) [Nonempty U₀] (m₀ : Γ(M, U₀)) (hm₀ : m₀ ≠ 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m := by
  refine ⟨φ' U₀ m₀ / φ U₀ m₀, ?_, ?_⟩
  · have hφ : φ U₀ m₀ ≠ 0 := fun h => hm₀ (hinj U₀ inferInstance (h.trans (map_zero _).symm))
    have hφ' : φ' U₀ m₀ ≠ 0 := fun h => hm₀ (hinj' U₀ inferInstance (h.trans (map_zero _).symm))
    exact div_ne_zero hφ' hφ
  · intro U _ m
    by_cases hm : m = 0
    · rw [hm, map_zero, map_zero, mul_zero]
    · have hφ : φ U m ≠ 0 := fun h => hm (hinj U inferInstance (h.trans (map_zero _).symm))
      rw [ratio_eq M φ φ' hnat hnat' hsmul hsmul' hinj U₀ U m₀ m hm₀ hm, div_mul_cancel₀ _ hφ]

end AlgebraicGeometry.Scheme.Modules.PresUniq

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsIntegral Scheme functionField_isFractionRing_of_isAffineOpen IsAffineOpen Scheme.Modules" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Γ functionField isBasis_affineOpens Modules Opens" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf isSheaf" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
open AlgebraicGeometry.Scheme.Modules.PresUniq in

theorem AlgebraicGeometry.Scheme.Modules.exists_forall_eq_mul_of_presentations'
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m := by
  obtain ⟨U₀, m₀, hm₀⟩ := hsec
  by_cases hU₀ : Nonempty U₀
  · exact exists_eq_mul M φ φ' hnat hnat' hsmul hsmul' hinj hinj' U₀ m₀ hm₀
  ·
    exfalso
    apply hm₀
    have hbot : U₀ = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hU₀ ⟨⟨z, hz⟩⟩
    subst hbot
    let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
    refine TopCat.Sheaf.eq_of_locally_eq' F (fun i : Empty => (⊥ : X.Opens)) ⊥ (fun i => i.elim) ?_ m₀ 0
      (fun i => i.elim)
    intro z hz
    exact hz.elim

open AlgebraicGeometry.Scheme.Modules.PresUniq in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m :=
  AlgebraicGeometry.Scheme.Modules.exists_forall_eq_mul_of_presentations' M φ φ' hnat hnat' hsmul hsmul' hinj hinj' hsec

end S_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations (solution)
