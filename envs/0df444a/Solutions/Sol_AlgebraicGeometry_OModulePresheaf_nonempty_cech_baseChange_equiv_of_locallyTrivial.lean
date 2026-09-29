-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c4156fdb-6416-5d46-a8ec-52a3fe66d858

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace LinearMap
p2m_export "LinearMap" "mem_range range snd exact_map_mkQ_range codRestrict zero_apply exact_subtype_ker_map fst ker_comp coe_coe ext comp baseChange ker mem_ker comp_apply baseChange_comp mem_range_self lTensor_surjective"
namespace HomologyTransport
p2m_open "LinearMap"

variable {S : Type u} [CommRing S]
variable {P₀ P₁ P₂ Q₀ Q₁ Q₂ : Type u}
  [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
  [AddCommGroup Q₀] [Module S Q₀] [AddCommGroup Q₁] [Module S Q₁] [AddCommGroup Q₂] [Module S Q₂]
variable (e₀ : P₀ ≃ₗ[S] Q₀) (e₁ : P₁ ≃ₗ[S] Q₁) (e₂ : P₂ ≃ₗ[S] Q₂)
variable (f : P₀ →ₗ[S] P₁) (g : P₁ →ₗ[S] P₂) (f' : Q₀ →ₗ[S] Q₁) (g' : Q₁ →ₗ[S] Q₂)
variable (hf : e₁.toLinearMap ∘ₗ f = f' ∘ₗ e₀.toLinearMap) (hg : e₂.toLinearMap ∘ₗ g = g' ∘ₗ e₁.toLinearMap)

include hf in
theorem apply_f (x : P₀) : e₁ (f x) = f' (e₀ x) := by
  have := LinearMap.congr_fun hf x
  simpa using this

include hf in
theorem comap_ker : (LinearMap.ker f').comap e₀.toLinearMap = LinearMap.ker f := by
  ext x
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, LinearMap.mem_ker]
  rw [← apply_f e₀ e₁ f f' hf, map_eq_zero_iff _ e₁.injective]

def kerEquiv : LinearMap.ker f ≃ₗ[S] LinearMap.ker f' :=
  (LinearEquiv.ofEq _ _ (comap_ker e₀ e₁ f f' hf).symm).trans (e₀.ofSubmodule' (LinearMap.ker f'))

theorem kerEquiv_apply_coe (x : LinearMap.ker f) : (kerEquiv e₀ e₁ f f' hf x : Q₀) = e₀ x := rfl

include hf hg in

theorem comap_kerEquiv_comap_range :
    ((LinearMap.range f').comap (LinearMap.ker g').subtype).comap (kerEquiv e₁ e₂ g g' hg).toLinearMap
      = (LinearMap.range f).comap (LinearMap.ker g).subtype := by
  ext z
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Submodule.coe_subtype, LinearMap.mem_range,
    kerEquiv_apply_coe]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₀.symm y, e₁.injective ?_⟩
    rw [apply_f e₀ e₁ f f' hf, e₀.apply_symm_apply, hy]
  · rintro ⟨x, hx⟩
    exact ⟨e₀ x, by rw [← apply_f e₀ e₁ f f' hf, hx]⟩

include hf hg in
theorem map_kerEquiv_comap_range :
    ((LinearMap.range f).comap (LinearMap.ker g).subtype).map (kerEquiv e₁ e₂ g g' hg).toLinearMap
      = (LinearMap.range f').comap (LinearMap.ker g').subtype := by
  rw [← comap_kerEquiv_comap_range e₀ e₁ e₂ f g f' g' hf hg]
  exact Submodule.map_comap_eq_of_surjective (kerEquiv e₁ e₂ g g' hg).surjective _

end LinearMap.HomologyTransport

namespace LinearMap
p2m_export "LinearMap" "mem_range range snd exact_map_mkQ_range codRestrict zero_apply exact_subtype_ker_map fst ker_comp coe_coe ext comp baseChange ker mem_ker comp_apply baseChange_comp mem_range_self lTensor_surjective"
namespace FlatKerBC
p2m_open "LinearMap"

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {M₀ M₁ M₂ : Type u} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]
variable (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)

theorem subtype_baseChange_injective [Module.Flat R A] :
    Function.Injective ((LinearMap.ker g).subtype.baseChange A) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := A) (LinearMap.ker g).subtype
    (LinearMap.ker g).injective_subtype

theorem range_subtype_baseChange [Module.Flat R A] :
    LinearMap.range ((LinearMap.ker g).subtype.baseChange A) = LinearMap.ker (g.baseChange A) := by
  have hexact : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  have hexA : Function.Exact ((LinearMap.ker g).subtype.baseChange A) (g.baseChange A) := by
    have := Module.Flat.lTensor_exact A hexact
    intro y; exact this y
  exact hexA.linearMap_ker_eq.symm

def theta [Module.Flat R A] : A ⊗[R] LinearMap.ker g ≃ₗ[A] LinearMap.ker (g.baseChange A) :=
  (LinearEquiv.ofInjective _ (subtype_baseChange_injective A g)).trans
    (LinearEquiv.ofEq _ _ (range_subtype_baseChange A g))

theorem theta_apply_coe [Module.Flat R A] (z : A ⊗[R] LinearMap.ker g) :
    (theta A g z : A ⊗[R] M₁) = ((LinearMap.ker g).subtype.baseChange A) z := rfl

variable (hgf : g ∘ₗ f = 0)

def toKer : M₀ →ₗ[R] LinearMap.ker g :=
  LinearMap.codRestrict (LinearMap.ker g) f fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hgf, LinearMap.zero_apply]

theorem subtype_comp_toKer : (LinearMap.ker g).subtype ∘ₗ toKer f g hgf = f := rfl

theorem range_toKer : LinearMap.range (toKer f g hgf) = (LinearMap.range f).comap (LinearMap.ker g).subtype := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨y, hy⟩ ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

include hgf in
theorem comap_theta [Module.Flat R A] :
    ((LinearMap.range (f.baseChange A)).comap (LinearMap.ker (g.baseChange A)).subtype).comap
        (theta A g).toLinearMap
      = LinearMap.range ((toKer f g hgf).baseChange A) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, subtype_baseChange_injective A g ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_toKer, hx]
    rfl
  · rintro _ ⟨x, rfl⟩
    show (((theta A g) ((toKer f g hgf).baseChange A x) : LinearMap.ker (g.baseChange A)) : A ⊗[R] M₁)
      ∈ LinearMap.range (f.baseChange A)
    rw [theta_apply_coe, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, subtype_comp_toKer]
    exact LinearMap.mem_range_self _ x

include hgf in

theorem nonempty_quotEquiv :
    Nonempty (((A ⊗[R] LinearMap.ker g) ⧸ LinearMap.range ((toKer f g hgf).baseChange A))
      ≃ₗ[A] A ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype)) := by
  have hr : LinearMap.range (toKer f g hgf) = (LinearMap.range f).comap (LinearMap.ker g).subtype :=
    range_toKer f g hgf
  have hexact : Function.Exact (toKer f g hgf) ((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ := by
    rw [← hr]; exact LinearMap.exact_map_mkQ_range _
  have hsurj : Function.Surjective ((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ :=
    Submodule.mkQ_surjective _
  have hexA : Function.Exact ((toKer f g hgf).baseChange A)
      (((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ.baseChange A) := by
    have := lTensor_exact A hexact hsurj
    intro y; exact this y
  have hsurjA : Function.Surjective (((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ.baseChange A) := by
    have := LinearMap.lTensor_surjective A hsurj
    intro y; exact this y
  exact ⟨hexA.linearEquivOfSurjective hsurjA⟩

end LinearMap.FlatKerBC

end

set_option maxHeartbeats 1600000 in
open LinearMap.HomologyTransport LinearMap.FlatKerBC in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    (Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
        ≃ₗ[A] LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 0).baseChange A)) ∧
      ∀ i : ℕ, ∃ φ : LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A) →ₗ[A]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i,
        Function.Surjective φ ∧
          LinearMap.ker φ = (LinearMap.range (((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A)).comap
            (LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)).subtype) ∧
    (Module.Flat R A →
      Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).H0 𝒰) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i
          ≃ₗ[A] A ⊗[R] (OModulePresheaf.ofModules π M).HSucc 𝒰 i)) := by
  obtain ⟨E, hEd, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial π 𝒰 M htriv A

  have h0 : Nonempty ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0 (𝒰.baseChange π A)
        ≃ₗ[A] LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 0).baseChange A)) :=
    ⟨(kerEquiv (E 0) (E 1) _ _ (hEd 0)).symm⟩

  have h1 : ∀ i : ℕ, ∃ φ : LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A) →ₗ[A]
          (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc (𝒰.baseChange π A) i,
        Function.Surjective φ ∧
          LinearMap.ker φ = (LinearMap.range (((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A)).comap
            (LinearMap.ker (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)).subtype := by
    intro i
    let κ := kerEquiv (E (i + 1)) (E (i + 2)) _ _ (hEd (i + 1))
    refine ⟨(Submodule.mkQ _) ∘ₗ κ.toLinearMap, ?_, ?_⟩
    · exact (Submodule.mkQ_surjective _).comp κ.surjective
    · rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      exact comap_kerEquiv_comap_range (E i) (E (i + 1)) (E (i + 2)) _ _ _ _ (hEd i) (hEd (i + 1))
  refine ⟨⟨h0, h1⟩, fun hflat => ?_⟩
  haveI := hflat
  have hdd : ∀ i : ℕ, (OModulePresheaf.ofModules π M).d 𝒰 (i + 1) ∘ₗ (OModulePresheaf.ofModules π M).d 𝒰 i = 0 :=
    fun i => AlgebraicGeometry.OModulePresheaf.d_comp_d _ 𝒰 i
  refine ⟨?_, fun i => ?_⟩
  ·
    obtain ⟨e'⟩ := h0
    exact ⟨e' ≪≫ₗ (theta A ((OModulePresheaf.ofModules π M).d 𝒰 0)).symm⟩
  ·
    let κ := kerEquiv (E (i + 1)) (E (i + 2)) (((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)).baseChange A)
      _ (hEd (i + 1))
    let Φ := (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).trans κ
    have hΦ : (LinearMap.range ((toKer ((OModulePresheaf.ofModules π M).d 𝒰 i)
          ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)).baseChange A)).map Φ.toLinearMap
        = (LinearMap.range ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d
              (𝒰.baseChange π A) i)).comap
          (LinearMap.ker ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d
              (𝒰.baseChange π A) (i + 1))).subtype := by
      rw [← map_kerEquiv_comap_range (E i) (E (i + 1)) (E (i + 2)) _ _ _ _ (hEd i) (hEd (i + 1)),
        ← comap_theta A ((OModulePresheaf.ofModules π M).d 𝒰 i) ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)]
      show Submodule.map (κ.toLinearMap ∘ₗ (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).toLinearMap) _ = _
      rw [Submodule.map_comp, Submodule.map_comap_eq_of_surjective
        (theta A ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1))).surjective]
    obtain ⟨e₁⟩ := nonempty_quotEquiv A ((OModulePresheaf.ofModules π M).d 𝒰 i)
      ((OModulePresheaf.ofModules π M).d 𝒰 (i + 1)) (hdd i)
    let e₂ := Submodule.Quotient.equiv _ _ Φ hΦ
    exact ⟨e₂.symm ≪≫ₗ e₁⟩

end S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial (solution)
