-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0b15de1a-0805-5785-8078-d03a06e852d3

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesWedge
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_exists_basis
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_basis_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact.AlgebraicGeometry Opposite TopologicalSpace CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme Scheme.Modules Scheme.Modules.exteriorPower Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.IsInvertible Scheme.Modules.sheafify Scheme.Modules.wedgeVec"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Hom Γ Modules Opens PresheafOfModules Modules.exteriorPower Modules.IsLocallyFreeOfRank Modules.IsInvertible Modules.sheafify Modules.wedgeVec"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom mapPresheaf_app map_smul presheafExteriorPower exteriorPower IsLocallyFreeOfRank IsInvertible sheafify wedgeVec whiskerRight_exteriorPower_map_comp_wedgeVec epi_sheafification_map_of_locallySurjective Hom.epi_iff_locallySurjective exists_app_eq_of_exact_of_app_eq_zero"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma ιMulti_comp_mem {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ}
    (w : Fin m → M) (P : Submodule A (⋀[A]^m M)) (hP : exteriorPower.ιMulti A m w ∈ P)
    (φ : Fin m → Fin m) : exteriorPower.ιMulti A m (w ∘ φ) ∈ P := by
  by_cases hφ : Function.Injective φ
  · have hbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφ
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective φ hbij
    have : (w ∘ φ) = w ∘ σ := rfl
    rw [this, AlternatingMap.map_perm]
    exact P.smul_of_tower_mem _ hP
  ·
    rw [Function.Injective] at hφ
    push_neg at hφ
    obtain ⟨i, j, hij, hne⟩ := hφ
    have : exteriorPower.ιMulti A m (w ∘ φ) = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ (w ∘ φ) (by simp [hij]) hne
    rw [this]
    exact P.zero_mem

lemma exteriorPower_le_of_span_eq_top {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M] {m : ℕ}
    (w : Fin m → M) (hw : Submodule.span A (Set.range w) = ⊤) (P : Submodule A (⋀[A]^m M))
    (hP : exteriorPower.ιMulti A m w ∈ P) : ⊤ ≤ P := by
  rw [← exteriorPower.ιMulti_family_span_of_span (n := m) A hw, Submodule.span_le]
  rintro _ ⟨s, rfl⟩

  exact ιMulti_comp_mem w P hP _

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact.AlgebraicGeometry.Scheme.Modules in
theorem solution {X : Scheme.{u}} {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsLocallyFreeOfRank n S.X₁) (h₃ : Scheme.Modules.IsInvertible S.X₃) :
    Epi (((Scheme.Modules.exteriorPower X n).map S.f ▷ S.X₂) ≫ Scheme.Modules.wedgeVec n S.X₂) := by
  haveI := hS.mono_f
  haveI := hS.epi_g

  rw [whiskerRight_exteriorPower_map_comp_wedgeVec]
  set θ : (presheafExteriorPower X n).obj S.X₁.val ⊗ S.X₂.val ⟶ (presheafExteriorPower X (n + 1)).obj S.X₂.val :=
    ((presheafExteriorPower X n).map S.f.val ▷ S.X₂.val) ≫ PresheafOfModules.wedgeVec n S.X₂.val with hθdef

  suffices hθ : Epi ((Scheme.Modules.sheafify X).map θ) by infer_instance
  change Epi ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map θ)
  refine epi_sheafification_map_of_locallySurjective θ (fun U s x hxU => ?_)

  obtain ⟨V₁, hx₁, e', he'⟩ := h₁.exists_basis x
  obtain ⟨V₀, hx₀, u, hu⟩ := h₃.exists_basis_one x
  obtain ⟨V₂, i₂, hx₂, et, het⟩ : ∃ (V₂ : X.Opens) (i : V₂ ≤ V₀), x ∈ V₂ ∧
      ∃ et : Γ(S.X₂, V₂), S.g.app V₂ et = S.X₃.presheaf.map (homOfLE i).op u := by
    obtain ⟨V₂, i, hx₂, ⟨et, het⟩⟩ := (Hom.epi_iff_locallySurjective S.g).mp inferInstance V₀ u x hx₀
    exact ⟨V₂, i, hx₂, et, het⟩
  let V : X.Opens := U ⊓ V₁ ⊓ V₂
  have hVU : V ≤ U := inf_le_left.trans inf_le_left
  have hV₁ : V ≤ V₁ := inf_le_left.trans inf_le_right
  have hV₂ : V ≤ V₂ := inf_le_right
  have hV₀ : V ≤ V₀ := hV₂.trans i₂
  have hxV : x ∈ V := ⟨⟨hxU, hx₁⟩, hx₂⟩
  refine ⟨V, hVU, hxV, ?_⟩

  suffices hsurj : Function.Surjective (θ.app (op V)) from hsurj _

  let A : Type u := Γ(X, V)
  let E₁ : Type u := Γ(S.X₁, V)
  let E₂ : Type u := Γ(S.X₂, V)
  let E₃ : Type u := Γ(S.X₃, V)
  obtain ⟨b₁, hb₁⟩ := he' V hV₁
  obtain ⟨b₃, hb₃⟩ := hu V hV₀
  let fV : E₁ →ₗ[A] E₂ := PresheafOfModules.ExteriorPower.appₗ S.f.val (op V)
  let gV : E₂ →ₗ[A] E₃ := PresheafOfModules.ExteriorPower.appₗ S.g.val (op V)
  have hfV : ∀ e, fV e = S.f.app V e := fun e => rfl
  have hgV : ∀ e, gV e = S.g.app V e := fun e => rfl

  let etV : E₂ := S.X₂.presheaf.map (homOfLE hV₂).op et
  have hget : gV etV = b₃ 0 := by
    rw [hgV, hb₃]
    change S.g.app V (S.X₂.presheaf.map (homOfLE hV₂).op et) = _
    have hnat := congr($(S.g.mapPresheaf.naturality (homOfLE hV₂).op) et)
    simp only [CategoryTheory.comp_apply, mapPresheaf_app] at hnat
    rw [hnat, het, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE hV₂ ≫ homOfLE i₂) (homOfLE hV₀)]

  let w : Fin (n + 1) → E₂ := Fin.append (fun i => fV (b₁ i)) (fun _ : Fin 1 => etV)
  have hw : Submodule.span A (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    rintro m -

    let c : A := b₃.repr (gV m) 0
    have hc : gV m = c • b₃ 0 := by
      conv_lhs => rw [← b₃.sum_repr (gV m)]
      simp [c]
    have hker : S.g.app V (m - c • etV) = 0 := by
      rw [← hgV, LinearMap.map_sub, LinearMap.map_smul, hget, hc, sub_self]
    obtain ⟨e₁, he₁⟩ := exists_app_eq_of_exact_of_app_eq_zero S hS.exact V (m - c • etV) hker
    have hm : m = fV e₁ + c • etV := by rw [hfV, he₁, sub_add_cancel]
    rw [hm]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd n 0, by simp [w]⟩))

    have : fV e₁ = ∑ i, (b₁.repr e₁ i) • fV (b₁ i) := by
      conv_lhs => rw [← b₁.sum_repr e₁]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => LinearMap.map_smul fV _ _)
    rw [this]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castAdd 1 i, by simp [w]⟩))

  let θV := (θ.app (op V)).hom
  have hθV : θV ((show ((presheafExteriorPower X n).obj S.X₁.val).obj (op V) from
      exteriorPower.ιMulti A n (fun i => b₁ i)) ⊗ₜ etV) =
        (show ((presheafExteriorPower X (n + 1)).obj S.X₂.val).obj (op V) from exteriorPower.ιMulti A (n + 1) w) := by
    change exteriorPower.mulVec A E₂ n (exteriorPower.map n fV (exteriorPower.ιMulti A n (fun i => b₁ i))) etV =
      exteriorPower.ιMulti A (n + 1) w
    rw [exteriorPower.map_apply_ιMulti, exteriorPower.mulVec_ιMulti]
    rfl

  intro z
  have hz : (show ⋀[A]^(n + 1) E₂ from z) ∈ LinearMap.range θV := by
    refine exteriorPower_le_of_span_eq_top w hw (LinearMap.range θV) ?_ Submodule.mem_top
    exact ⟨_, hθV⟩
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, hy⟩

end S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact (solution)
