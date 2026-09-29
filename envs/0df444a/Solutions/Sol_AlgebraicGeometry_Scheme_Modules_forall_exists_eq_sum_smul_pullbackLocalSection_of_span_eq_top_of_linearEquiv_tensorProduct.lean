-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/af69e7bb-b944-5883-8505-c2c6cbed9e53

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (M : X.Modules)
    {n : ℕ} (σ : Fin n → Γ(M, ⊤))
    (hσ : letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      Submodule.span S (Set.range σ) = ⊤)
    (S' : Type u) [CommRing S'] (φ : S →+* S')
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hbc : letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      letI : Module S' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
        Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
      letI : Algebra S S' := φ.toAlgebra
      ∃ e : S' ⊗[S] Γ(M, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤),
        ∀ (s' : S') (τ : Γ(M, ⊤)), e (s' ⊗ₜ[S] τ) = s' • Scheme.Modules.pullbackLocalSection g τ)
    (t : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤)) :
    letI : Module S' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
    ∃ c : Fin n → S', t = ∑ i, c i • Scheme.Modules.pullbackLocalSection g (σ i) := by
  classical
  letI mS : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
  letI mS' : Module S' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom
  letI : Algebra S S' := φ.toAlgebra
  show ∃ c : Fin n → S', t = ∑ i, c i • Scheme.Modules.pullbackLocalSection g (σ i)
  obtain ⟨e, he⟩ := hbc
  let N : Submodule S' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ ⊤) :=
    Submodule.span S' (Set.range fun i => Scheme.Modules.pullbackLocalSection g (σ i))

  have hscal : ∀ a : S, (g.app ⊤).hom (((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom a) =
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom (φ a) := by
    intro a
    change ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop ≫ g.appTop).hom a =
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ ⊤ le_top).hom (φ a)
    have happ : f'.appLE ⊤ ⊤ le_top = f'.appTop := f'.appLE_eq_app
    rw [happ, ← Scheme.Hom.comp_appTop, hg.w, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hkey : ∀ τ : Γ(M, ⊤), Scheme.Modules.pullbackLocalSection g τ ∈ N := by
    intro τ
    have hτ : τ ∈ Submodule.span S (Set.range σ) := hσ.symm ▸ Submodule.mem_top
    induction hτ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [Scheme.Modules.pullbackLocalSection_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Scheme.Modules.pullbackLocalSection_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have h1 : Scheme.Modules.pullbackLocalSection g (a • x) = (φ a) • Scheme.Modules.pullbackLocalSection g x := by
        show Scheme.Modules.pullbackLocalSection g ((((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom a) • x) =
          ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (g ⁻¹ᵁ ⊤) le_top).hom (φ a) •
            Scheme.Modules.pullbackLocalSection g x
        rw [Scheme.Modules.pullbackLocalSection_smul, ← hscal]
      rw [h1]
      exact N.smul_mem _ hx
  have hrange : ∀ z : S' ⊗[S] Γ(M, ⊤), e z ∈ N := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul s' τ => rw [he]; exact N.smul_mem _ (hkey τ)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  have ht : t ∈ N := by
    obtain ⟨z, rfl⟩ := e.surjective t
    exact hrange z
  have ht' : t ∈ Submodule.span S' (Set.range fun i => Scheme.Modules.pullbackLocalSection g (σ i)) := ht
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := S')).mp ht'
  exact ⟨c, hc.symm⟩

end S_AlgebraicGeometry_Scheme_Modules_forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_exists_eq_sum_smul_pullbackLocalSection_of_span_eq_top_of_linearEquiv_tensorProduct (solution)
