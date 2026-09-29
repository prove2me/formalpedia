-- Prove2me | solution 1 for AlgebraicGeometry.exists_isGalois_functionField_of_quotient_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/95e2b388-2844-589d-ba93-8fd1be16f7ee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.germToFunctionField Scheme.Hom.id_app Scheme.Hom Opens.isDominant_ι IsFinite spread_out_unique_of_isGermInjective Spec IsIntegral Scheme ext_of_isDominant_of_isSeparated functionField_isFractionRing_of_isAffineOpen genericPoint_eq_of_isOpenImmersion IsSeparated IsDominant IsAffineOpen Scheme.Hom.germ_stalkMap Scheme.Hom.stalkMap_id Scheme.Hom.comp_preimage Scheme.Hom.appLE range_eq_univ"
namespace FFGaloisQuot
p2m_open "AlgebraicGeometry"

variable {C D X : Scheme.{u}}

section Pull

variable [IrreducibleSpace C] [IrreducibleSpace D] [IrreducibleSpace X]

noncomputable def ffPull (f : C ⟶ X) (hf : f (genericPoint C) = genericPoint X) :
    X.functionField ⟶ C.functionField :=
  X.presheaf.stalkSpecializes (specializes_of_eq hf) ≫ f.stalkMap (genericPoint C)

@[reassoc]
lemma germ_ffPull (f : C ⟶ X) (hf : f (genericPoint C) = genericPoint X)
    (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint C ∈ f ⁻¹ᵁ V) :
    X.presheaf.germ V (genericPoint X) hV ≫ ffPull f hf =
      f.app V ≫ C.presheaf.germ (f ⁻¹ᵁ V) (genericPoint C) hV' := by
  simp only [ffPull, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

lemma ffPull_germ_apply (f : C ⟶ X) (hf : f (genericPoint C) = genericPoint X)
    (V : X.Opens) (hV : Nonempty V) (hV' : Nonempty (f ⁻¹ᵁ V)) (s : Γ(X, V)) :
    ffPull f hf (X.germToFunctionField V s) =
      C.germToFunctionField (f ⁻¹ᵁ V) (f.app V s) := by
  change (X.germToFunctionField V ≫ ffPull f hf) s =
    (f.app V ≫ C.germToFunctionField (f ⁻¹ᵁ V)) s
  rw [Scheme.germToFunctionField, germ_ffPull]

lemma ffPull_congr {f f' : C ⟶ X} (e : f = f') (hf : f (genericPoint C) = genericPoint X)
    (hf' : f' (genericPoint C) = genericPoint X) : ffPull f hf = ffPull f' hf' := by
  subst e; rfl

lemma ffPull_id : ffPull (𝟙 C) rfl = 𝟙 C.functionField := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  rw [germ_ffPull (𝟙 C) rfl U hU (show genericPoint C ∈ U from hU)]
  simp only [Scheme.Hom.id_app, Category.comp_id]
  erw [Category.id_comp]
  rfl

lemma ffPull_comp (f : C ⟶ D) (g : D ⟶ X) (hf : f (genericPoint C) = genericPoint D)
    (hg : g (genericPoint D) = genericPoint X) (hfg : (f ≫ g) (genericPoint C) = genericPoint X) :
    ffPull (f ≫ g) hfg = ffPull g hg ≫ ffPull f hf := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  have hU' : genericPoint D ∈ g ⁻¹ᵁ U := by
    change g (genericPoint D) ∈ U; rwa [hg]
  have hU'' : genericPoint C ∈ f ⁻¹ᵁ g ⁻¹ᵁ U := by
    change f (genericPoint C) ∈ g ⁻¹ᵁ U; rwa [hf]
  rw [germ_ffPull _ _ U hU hU'', germ_ffPull_assoc _ _ U hU hU', germ_ffPull _ _ _ hU' hU'']
  simp

end Pull

section Aut

variable [IrreducibleSpace C]

noncomputable def pullAut (e : Aut C) : C.functionField ⟶ C.functionField :=
  ffPull e.hom (genericPoint_eq_of_isOpenImmersion e.hom)

lemma pullAut_one : pullAut (1 : Aut C) = 𝟙 C.functionField := ffPull_id

lemma pullAut_mul (e₁ e₂ : Aut C) : pullAut (e₁ * e₂) = pullAut e₁ ≫ pullAut e₂ :=
  ffPull_comp _ _ _ _ _

lemma pullAut_mul_apply (e₁ e₂ : Aut C) (x : C.functionField) :
    pullAut (e₁ * e₂) x = pullAut e₂ (pullAut e₁ x) := by
  rw [pullAut_mul, CommRingCat.comp_apply]

lemma pullAut_one_apply (x : C.functionField) : pullAut (1 : Aut C) x = x := by
  rw [pullAut_one, CommRingCat.id_apply]

lemma pullAut_germ_apply (e : Aut C) (U : C.Opens) (hU : Nonempty U)
    (hU' : Nonempty (e.hom ⁻¹ᵁ U)) (s : Γ(C, U)) :
    pullAut e (C.germToFunctionField U s) = C.germToFunctionField (e.hom ⁻¹ᵁ U) (e.hom.app U s) :=
  ffPull_germ_apply _ _ _ hU hU' _

end Aut

end AlgebraicGeometry.FFGaloisQuot

open AlgebraicGeometry.FFGaloisQuot

theorem solution
    {B : Type} [CommRing B]
    {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (πC : C ⟶ Spec (CommRingCat.of B)) [IsSeparated πC]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut C) (hρ : ∀ g : G, (ρ g).hom ≫ πC = πC)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) :
    ∃ (_ : Algebra X.functionField C.functionField)
      (θ : G →* (C.functionField ≃ₐ[X.functionField] C.functionField)),

      (∀ (V : X.Opens) [Nonempty (V : Scheme.{0})] [Nonempty ((π ⁻¹ᵁ V : C.Opens) : Scheme.{0})] (f : Γ(X, V)),
        algebraMap X.functionField C.functionField (X.germToFunctionField V f) =
          C.germToFunctionField (π ⁻¹ᵁ V) (π.app V f)) ∧

      (∀ (g : G) (U : C.Opens) [Nonempty (U : Scheme.{0})] [Nonempty (((ρ g).inv ⁻¹ᵁ U : C.Opens) : Scheme.{0})] (f : Γ(C, U)),
        θ g (C.germToFunctionField U f) = C.germToFunctionField ((ρ g).inv ⁻¹ᵁ U) ((ρ g).inv.app U f)) ∧
      FiniteDimensional X.functionField C.functionField ∧ IsGalois X.functionField C.functionField ∧
      Function.Surjective θ ∧ (∀ g : G, θ g = 1 ↔ ρ g = 1) := by
  classical

  have hgen : π (genericPoint C) = genericPoint X := by
    apply ((genericPoint_spec X).eq _).symm
    have h := (genericPoint_spec C).image π.continuous
    rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj, closure_univ] at h
  haveI : Fintype G := Fintype.ofFinite G

  let φ : X.functionField ⟶ C.functionField := ffPull π hgen
  letI alg : Algebra X.functionField C.functionField := φ.hom.toAlgebra
  have alg_def : algebraMap X.functionField C.functionField = φ.hom := rfl

  let Θ : G → (C.functionField ⟶ C.functionField) := fun g => pullAut (ρ g⁻¹)
  have Θ_one : Θ 1 = 𝟙 _ := by
    simp only [Θ, inv_one, map_one, pullAut_one]
  have Θ_mul : ∀ g h : G, ∀ x, Θ (g * h) x = Θ g (Θ h x) := by
    intro g h x
    simp only [Θ, mul_inv_rev, map_mul, pullAut_mul_apply]
  have hρinv : ∀ g : G, (ρ g).inv ≫ π = π := by
    intro g
    rw [Iso.inv_comp_eq]
    exact (hπ g).symm
  have Θ_φ : ∀ (g : G) (y : X.functionField), Θ g (φ y) = φ y := by
    intro g y
    have hc : φ ≫ pullAut (ρ g⁻¹) = φ := by
      rw [pullAut, ← ffPull_comp (ρ g⁻¹).hom π _ hgen (by rw [hπ]; exact hgen)]
      exact ffPull_congr (hπ _) _ _
    change (φ ≫ pullAut (ρ g⁻¹)) y = φ y
    rw [hc]

  let θa : G → (C.functionField →ₐ[X.functionField] C.functionField) := fun g =>
    { (Θ g).hom with
      commutes' := fun y => Θ_φ g y }
  have θa_apply : ∀ g x, θa g x = Θ g x := fun _ _ => rfl
  let θ₁ : G → (C.functionField ≃ₐ[X.functionField] C.functionField) := fun g =>
    AlgEquiv.ofAlgHom (θa g) (θa g⁻¹)
      (by ext x; simp [θa_apply, ← Θ_mul, Θ_one])
      (by ext x; simp [θa_apply, ← Θ_mul, Θ_one])
  have θ₁_apply : ∀ g x, θ₁ g x = Θ g x := fun _ _ => rfl
  let θ : G →* (C.functionField ≃ₐ[X.functionField] C.functionField) :=
    { toFun := θ₁
      map_one' := by ext x; simp [θ₁_apply, Θ_one]
      map_mul' := by intro g h; ext x; simp [θ₁_apply, Θ_mul, AlgEquiv.mul_apply] }
  have θ_apply : ∀ g x, θ g x = Θ g x := fun _ _ => rfl

  have key : ∀ x : C.functionField, (∀ g : G, Θ g x = x) → x ∈ Set.range φ := by

    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    obtain ⟨_, ⟨V, hV, rfl⟩, hx₀V, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
    change IsAffineOpen V at hV
    haveI hVne : Nonempty V := ⟨⟨x₀, hx₀V⟩⟩
    haveI hUne : Nonempty (π ⁻¹ᵁ V) := by
      obtain ⟨c, hc⟩ := hsurj x₀
      exact ⟨⟨c, show π c ∈ V by rw [hc]; exact hx₀V⟩⟩
    have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
    haveI := functionField_isFractionRing_of_isAffineOpen X V hV
    haveI := functionField_isFractionRing_of_isAffineOpen C (π ⁻¹ᵁ V) hU
    set U : C.Opens := π ⁻¹ᵁ V with hUdef
    let ιU : Γ(C, U) →+* C.functionField := algebraMap Γ(C, U) C.functionField
    have ιU_def : ιU = (C.germToFunctionField U).hom := rfl
    have ιU_inj : Function.Injective ιU := C.germToFunctionField_injective U
    let α : G → (Γ(C, U) →+* Γ(C, U)) := fun g =>
      ((ρ g).hom.appLE U U (by rw [hUdef, ← Scheme.Hom.comp_preimage, hπ g])).hom

    have compat : ∀ (g : G) (s : Γ(C, U)), ιU (α g s) = pullAut (ρ g) (ιU s) := by
      intro g s
      have hUne' : Nonempty ((ρ g).hom ⁻¹ᵁ U) := by
        rw [hUdef, ← Scheme.Hom.comp_preimage, hπ g]; exact hUne
      rw [ιU_def, pullAut_germ_apply (ρ g) U hUne hUne' s]
      simp only [α, Scheme.Hom.appLE, CommRingCat.comp_apply]
      exact TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE _) _ _ _
    have α_one : ∀ s, α 1 s = s := fun s =>
      ιU_inj (by rw [compat, map_one, pullAut_one_apply])

    intro x hx
    have hx' : ∀ g : G, pullAut (ρ g) x = x := fun g => by
      have := hx g⁻¹
      simp only [Θ, inv_inv] at this
      exact this
    obtain ⟨a, b, hb, hxab⟩ := IsFractionRing.div_surjective (A := Γ(C, U)) x
    change ιU a / ιU b = x at hxab
    have hb0 : ιU b ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero hb (ιU_inj (h.trans (map_zero ιU).symm))
    let P : Γ(C, U) := ∏ g ∈ Finset.univ.erase 1, α g b
    let N₀ : Γ(C, U) := ∏ g, α g b
    let c₀ : Γ(C, U) := a * P
    have hN₀ : N₀ = b * P := by
      have := Finset.mul_prod_erase Finset.univ (fun g => α g b) (Finset.mem_univ (1 : G))
      beta_reduce at this
      rw [α_one] at this
      exact this.symm
    have hιN : ιU N₀ = ∏ g, pullAut (ρ g) (ιU b) := by
      simp only [N₀, map_prod, compat]
    have hpull_inj : ∀ g : G, Function.Injective (pullAut (C := C) (ρ g)) := fun g =>
      (pullAut (ρ g)).hom.injective
    have hP0 : ιU P ≠ 0 := by
      simp only [P, map_prod]
      rw [Finset.prod_ne_zero_iff]
      intro g _
      rw [compat]
      exact (map_ne_zero (pullAut (ρ g)).hom).mpr hb0
    have hN0 : ιU N₀ ≠ 0 := by
      rw [hN₀, map_mul]; exact mul_ne_zero hb0 hP0
    have hNinv : ∀ h : G, pullAut (ρ h) (ιU N₀) = ιU N₀ := by
      intro h
      rw [hιN, map_prod]
      simp_rw [← pullAut_mul_apply, ← map_mul]
      exact Fintype.prod_equiv (Equiv.mulRight h) _ _ (fun g => rfl)
    have hc : ιU c₀ = x * ιU N₀ := by
      rw [← hxab, hN₀]
      simp only [c₀, map_mul]
      field_simp
    have hcinv : ∀ h : G, pullAut (ρ h) (ιU c₀) = ιU c₀ := by
      intro h
      rw [hc, map_mul, hx' h, hNinv h]
    have hc₀ : ∀ g, α g c₀ = c₀ := fun g => ιU_inj (by rw [compat, hcinv])
    have hN₀' : ∀ g, α g N₀ = N₀ := fun g => ιU_inj (by rw [compat, hNinv])
    have hc₀mem : c₀ ∈ Set.range (π.app V) := by
      rw [hinv V]; exact hc₀
    have hN₀mem : N₀ ∈ Set.range (π.app V) := by
      rw [hinv V]; exact hN₀'
    obtain ⟨c₁, hc₁⟩ := hc₀mem
    obtain ⟨N₁, hN₁⟩ := hN₀mem
    refine ⟨X.germToFunctionField V c₁ / X.germToFunctionField V N₁, ?_⟩
    change φ.hom (_ / _) = x
    rw [map_div₀]
    change φ _ / φ _ = x
    rw [ffPull_germ_apply π hgen V hVne hUne, ffPull_germ_apply π hgen V hVne hUne, hc₁, hN₁]
    change ιU c₀ / ιU N₀ = x
    rw [hc, mul_div_cancel_right₀ _ hN0]
  have range_iff : ∀ x : C.functionField, (∀ g : G, θ g x = x) ↔ x ∈ Set.range φ := by
    intro x
    refine ⟨fun h => key x (fun g => (θ_apply g x) ▸ h g), ?_⟩
    rintro ⟨y, rfl⟩ g
    rw [θ_apply, Θ_φ]

  letI act : MulSemiringAction G C.functionField := MulSemiringAction.compHom _ θ
  have smul_def : ∀ (g : G) (x : C.functionField), g • x = θ g x := fun _ _ => rfl
  have hfix : ∀ x : C.functionField,
      x ∈ FixedPoints.subfield G C.functionField ↔ x ∈ Set.range φ := by
    intro x
    rw [← range_iff]
    exact Iff.rfl
  have hfd : FiniteDimensional X.functionField C.functionField := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (FixedPoints.subfield G C.functionField) C.functionField)
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Submodule.span (FixedPoints.subfield G C.functionField)
        (s : Set C.functionField) := by
      rw [hs]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨d, hd⟩ := (hfix c).mp c.2
      have : (c • y : C.functionField) = d • y := by
        rw [Algebra.smul_def, Algebra.smul_def, alg_def]
        congr 1
        exact hd.symm
      rw [this]
      exact Submodule.smul_mem _ d hy
  haveI := hfd
  have hgal : IsGalois X.functionField C.functionField := by
    apply IsGalois.of_fixedField_eq_bot
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_bot, alg_def]
    apply (range_iff x).mp
    intro g
    exact (IntermediateField.mem_fixedField_iff _ _).mp hx (θ g) (Subgroup.mem_top _)
  have hsurjθ : Function.Surjective θ := by
    rw [← MonoidHom.range_eq_top]
    have h1 : IntermediateField.fixedField θ.range = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [IntermediateField.mem_bot, alg_def]
      apply (range_iff x).mp
      intro g
      exact (IntermediateField.mem_fixedField_iff _ _).mp hx (θ g) ⟨g, rfl⟩
    rw [← IntermediateField.fixingSubgroup_fixedField θ.range, h1,
      IntermediateField.fixingSubgroup_bot]
  have hker : ∀ g : G, θ g = 1 ↔ ρ g = 1 := by
    intro g
    constructor
    · intro hθ
      have hΘ : ∀ x, pullAut (ρ g⁻¹) x = x := fun x => by
        rw [← θ_apply, hθ, AlgEquiv.one_apply]
      suffices h : (ρ g⁻¹).hom = 𝟙 C by
        have : ρ g⁻¹ = 1 := Iso.ext h
        rwa [map_inv, inv_eq_one] at this
      have hP : pullAut (ρ g⁻¹) = 𝟙 _ := CommRingCat.hom_ext (RingHom.ext hΘ)
      set e : Aut C := ρ g⁻¹ with he_def
      have he : e.hom (genericPoint C) = genericPoint C := genericPoint_eq_of_isOpenImmersion e.hom
      have he' : e.hom (genericPoint C) = (𝟙 C : C ⟶ C) (genericPoint C) := he

      have hS : C.presheaf.stalkSpecializes (specializes_of_eq he.symm) ≫
          C.presheaf.stalkSpecializes (specializes_of_eq he) = 𝟙 _ := by
        rw [TopCat.Presheaf.stalkSpecializes_comp]
        exact TopCat.Presheaf.stalkSpecializes_refl _ _
      have hM : e.hom.stalkMap (genericPoint C) =
          C.presheaf.stalkSpecializes (specializes_of_eq he.symm) := by
        have h2 : C.presheaf.stalkSpecializes (specializes_of_eq he) ≫
            e.hom.stalkMap (genericPoint C) = 𝟙 _ := hP
        calc e.hom.stalkMap (genericPoint C)
            = (C.presheaf.stalkSpecializes (specializes_of_eq he.symm) ≫
                C.presheaf.stalkSpecializes (specializes_of_eq he)) ≫
                e.hom.stalkMap (genericPoint C) := by rw [hS, Category.id_comp]
          _ = C.presheaf.stalkSpecializes (specializes_of_eq he.symm) := by
                rw [Category.assoc, h2, Category.comp_id]
      have H : e.hom.stalkMap (genericPoint C) =
          C.presheaf.stalkSpecializes (Inseparable.of_eq he'.symm).specializes ≫
            (𝟙 C : C ⟶ C).stalkMap (genericPoint C) := by
        rw [Scheme.Hom.stalkMap_id]
        erw [Category.comp_id]
        exact hM
      obtain ⟨U, hηU, hUeq⟩ := spread_out_unique_of_isGermInjective e.hom (𝟙 C) he' H
      have hdense : Dense (U : Set C) := by
        rw [dense_iff_closure_eq]
        apply Set.eq_univ_of_univ_subset
        have h0 : closure ({genericPoint C} : Set C) = Set.univ := genericPoint_spec C
        rw [← h0]
        exact closure_mono (Set.singleton_subset_iff.mpr hηU)
      haveI : IsDominant U.ι := Opens.isDominant_ι hdense
      exact ext_of_isDominant_of_isSeparated πC (by rw [hρ, Category.id_comp]) U.ι hUeq
    · intro hρg
      ext x
      rw [θ_apply, AlgEquiv.one_apply]
      change pullAut (ρ g⁻¹) x = x
      rw [map_inv, hρg, inv_one, pullAut_one_apply]
  refine ⟨alg, θ, ?_, ?_, hfd, hgal, hsurjθ, hker⟩
  · intro V hV hV' f
    rw [alg_def]
    exact ffPull_germ_apply π hgen V hV hV' f
  · intro g U hU hU' f
    rw [θ_apply]
    change pullAut (ρ g⁻¹) _ = _
    rw [map_inv]
    exact pullAut_germ_apply (ρ g)⁻¹ U hU hU' f

end S_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite (solution)
