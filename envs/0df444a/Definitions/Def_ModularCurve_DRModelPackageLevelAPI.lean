-- Prove2me | Definitions.Def_ModularCurve_DRModelPackageLevelAPI
-- name    : ModularCurve_DRModelPackageLevelAPI
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2fc9b583-774e-5ad9-b9e6-f00c451416d2
-- title:
--   Fibre calculus for the Deligne–Rapoport level package
-- statement:
--   Standing context: a level $N_0$ with $N_0 \neq 0$, a prime $q$ with $q \nmid N_0$, the base ring $R q$ (the localisation of $\mathbb{Q}$ at $q$ supplied by [`GaloisRep.ratLocalizedAt`](../def/GaloisRep_Flat.html#L8)), the two Igusa schemes $X =$ `IgusaScheme (N₀ * q) q` and $X_0 =$ `IgusaScheme N₀ q` with their structure morphisms `toBase`, `toBase0` to $\operatorname{Spec}(R q)$, and, in the second half, a package $\mathfrak{X}$ of type `DRModelPackageLevel N₀ q hqN`. For a ring map $\mathrm{to}\kappa : R q \to \kappa$ the fibres `fibre`, `fibre0` are the fibre products of `toBase`, `toBase0` with $\operatorname{Spec}$ of that map. The first group of results records the two projections of the morphisms built from these fibre products: `sectionFibre` of a section of `toBase`, `sectionFibreOver` for a map into a local ring composed with its residue map, and the base-changed maps `fibreMap`, `fibreMap0` of a morphism over the base; with these, `fibreMap` is shown to be functorial (identity and composites), to be compatible with `fibreMap0` and with sections, and the fibres, their second projections, base-changed sections, and `fibreMap`/`fibreMap0` are identified with the `SmoothProperCurve.specMap`/`baseChange`/`sectionBaseChange` and `RelPicard.curveChange` spellings.
--
--   The second group concerns a package $\mathfrak{X}$. Over any $\kappa$ the fibre of its Atkin–Lehner isomorphism is an involution, the fibre of $\pi w = w \,;\, \pi$ factors as the fibre of $w$ followed by that of $\pi$, and the cusp section $\varepsilon_\infty$ followed by $w$ is $\varepsilon_0$. For $\kappa$ an algebraically closed field of characteristic $q$: the components satisfy $c_1 \,;\, w_\kappa = c_0$, $c_1 \,;\, (\pi w)_\kappa = \mathrm{id}$ and $c_0 \,;\, (\pi w)_\kappa = c_1 \,;\, \pi_\kappa$; the point $\varepsilon_\infty \,;\, \pi_\kappa$ of `fibre0` is the unique one whose composite with $c_0$ is $\varepsilon_\infty$, and the package's two cusp identities are restated in reassociated form. Transporting along the package's isomorphism `efib` with its curve model, `fibre0` is integral and its structure morphism to $\operatorname{Spec}\kappa$ is proper and smooth of relative dimension one, while the structure morphism of `fibre` is proper. Finally, a section of the structure sheaf of `fibre` on an open set whose pullbacks along $c_0$ and $c_1$ both vanish is zero, so the special fibre is covered, as a reduced scheme, by its two components.
--
--   **Relation to Mathlib.** The fibres here are Mathlib's scheme-theoretic fibre products and the transported properties are Mathlib's `IsProper`, `SmoothOfRelativeDimension` and `IsIntegral`; the Deligne–Rapoport package, the Igusa schemes and the relative Picard machinery being matched against are the project's own notions.
--
--   **Where it is used.** These identities are the component calculus of $X_0(N_0 q)$ in characteristic $q$ — two copies of $X_0(N_0)$ crossing at the supersingular points, exchanged by the Atkin–Lehner involution, with the two degeneracy maps restricting to the identity and to Frobenius — which underlies the analysis of $J_0(N_0 q)$ at $q$ used in level lowering and in the local study at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRModelPackageLevelAPI.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

section
variable {κ : Type} [CommRing κ] (toκ : R q →+* κ)

@[reassoc (attr := simp)]
theorem sectionFibre_fst (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibre ε toκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom toκ) ≫ ε.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sectionFibre_snd (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibre ε toκ ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem fibreMap_fst (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreMap_snd (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [fibreMap]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem fibreMap0_fst (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap0 π toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreMap0_snd (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap0 π toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [fibreMap0]; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem fibreMap_id : fibreMap (𝟙 (X N₀ q)) (Category.id_comp _) toκ = 𝟙 (fibre (N₀ := N₀) toκ) := by
  apply pullback.hom_ext <;> simp

theorem fibreMap_comp (φ ψ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) (hψ : ψ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) toκ = fibreMap φ hφ toκ ≫ fibreMap ψ hψ toκ := by
  apply pullback.hom_ext <;> simp

theorem fibreMap_comp_fibreMap0 (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q)
    (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap φ hφ toκ ≫ fibreMap0 π toκ = fibreMap0 ⟨φ ≫ π.1, by rw [Category.assoc, π.2, hφ]⟩ toκ := by
  apply pullback.hom_ext <;> simp

theorem sectionFibre_comp_fibreMap (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q))
    (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    sectionFibre ε toκ ≫ fibreMap φ hφ toκ = sectionFibre ⟨ε.1 ≫ φ, by rw [Category.assoc, hφ, ε.2]⟩ toκ := by
  apply pullback.hom_ext <;> simp

end

section
variable {A : Type} [CommRing A] [IsLocalRing A] (ρ : R q →+* A)
  (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ q))

@[reassoc (attr := simp)]
theorem sectionFibreOver_fst :
    sectionFibreOver ρ s ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem sectionFibreOver_snd : sectionFibreOver ρ s ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem sectionFibreOver_specMap_comp (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibreOver ρ ⟨Spec.map (CommRingCat.ofHom ρ) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩ =
      sectionFibre ε ((IsLocalRing.residue A).comp ρ) := by
  apply pullback.hom_ext
  · rw [sectionFibreOver_fst, sectionFibre_fst]
    show Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ (Spec.map (CommRingCat.ofHom ρ) ≫ ε.1) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue A).comp ρ)) ≫ ε.1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rw [sectionFibreOver_snd, sectionFibre_snd]

end

section curveChange
variable {κ : Type} [CommRing κ] (toκ : R q →+* κ)

theorem fibreMap0_eq_curveChange (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q)) :
    fibreMap0 π toκ = RelPicard.curveChange π.1 π.2 (Spec.map (CommRingCat.ofHom toκ)) := rfl

theorem fibreMap_eq_curveChange (φ : X N₀ q ⟶ X N₀ q) (hφ : φ ≫ toBase N₀ q = toBase N₀ q) :
    fibreMap φ hφ toκ = RelPicard.curveChange φ hφ (Spec.map (CommRingCat.ofHom toκ)) := rfl

end curveChange

section bridges
variable (κ : Type) [CommRing κ] [Algebra (R q) κ]

theorem fibre_eq_pullback_specMap :
    fibre (N₀ := N₀) (algebraMap (R q) κ) = pullback (toBase N₀ q) (SmoothProperCurve.specMap (R q) κ) := rfl

theorem fibre_snd_eq_baseChange :
    pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) =
      SmoothProperCurve.baseChange (R q) (toBase N₀ q) κ := rfl

theorem fibre0_eq_pullback_specMap :
    fibre0 (N₀ := N₀) (algebraMap (R q) κ) = pullback (toBase0 N₀ q) (SmoothProperCurve.specMap (R q) κ) := rfl

theorem fibre0_snd_eq_baseChange :
    pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) =
      SmoothProperCurve.baseChange (R q) (toBase0 N₀ q) κ := rfl

theorem sectionFibre_eq_sectionBaseChange (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R q)))) (toBase N₀ q)) :
    sectionFibre ε (algebraMap (R q) κ) = (SmoothProperCurve.sectionBaseChange κ ε).1 := rfl

end bridges

end DRLevel

open DRLevel

namespace DRModelPackageLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)

section
variable {κ : Type} [CommRing κ] (toκ : R q →+* κ)

theorem fibreMap_w_w : fibreMap 𝔛.w.hom 𝔛.w_over toκ ≫ fibreMap 𝔛.w.hom 𝔛.w_over toκ = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [𝔛.w_invol]

theorem fibreMap0_πw : fibreMap0 𝔛.πw toκ = fibreMap 𝔛.w.hom 𝔛.w_over toκ ≫ fibreMap0 𝔛.π toκ := by
  apply pullback.hom_ext <;> simp [DRModelPackageLevel.πw]

theorem sectionFibre_εinf_fibreMap_w :
    sectionFibre 𝔛.εinf toκ ≫ fibreMap 𝔛.w.hom 𝔛.w_over toκ = sectionFibre 𝔛.εzero toκ := by
  apply pullback.hom_ext <;> simp [𝔛.w_sections]

@[reassoc (attr := simp)]
theorem εinf0_snd : 𝔛.εinf0 toκ ≫ pullback.snd _ _ = 𝟙 _ := by
  simp [DRModelPackageLevel.εinf0]

end

section
variable {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : R q →+* κ)

theorem comp1_fibreMap_w : 𝔛.comp κ toκ 1 ≫ fibreMap 𝔛.w.hom 𝔛.w_over toκ = 𝔛.comp κ toκ 0 := by
  rw [← 𝔛.comp_w κ toκ, Category.assoc, fibreMap_w_w, Category.comp_id]

theorem comp1_πw : 𝔛.comp κ toκ 1 ≫ fibreMap0 𝔛.πw toκ = 𝟙 _ := by
  rw [fibreMap0_πw, ← Category.assoc, comp1_fibreMap_w, 𝔛.comp_pi]

theorem comp0_πw : 𝔛.comp κ toκ 0 ≫ fibreMap0 𝔛.πw toκ = 𝔛.comp κ toκ 1 ≫ fibreMap0 𝔛.π toκ := by
  rw [fibreMap0_πw, ← Category.assoc, 𝔛.comp_w]

theorem eq_εinf0_of_comp_comp0 (e : Spec (CommRingCat.of κ) ⟶ fibre0 (N₀ := N₀) toκ)
    (h : e ≫ 𝔛.comp κ toκ 0 = sectionFibre 𝔛.εinf toκ) : e = 𝔛.εinf0 toκ := by
  show e = sectionFibre 𝔛.εinf toκ ≫ fibreMap0 𝔛.π toκ
  rw [← h, Category.assoc, 𝔛.comp_pi, Category.comp_id]

theorem εinf0_comp0_assoc {Z : Scheme.{0}} (g : fibre (N₀ := N₀) toκ ⟶ Z) :
    𝔛.εinf0 toκ ≫ 𝔛.comp κ toκ 0 ≫ g = sectionFibre 𝔛.εinf toκ ≫ g := by
  simpa only [Category.assoc] using congrArg (· ≫ g) (𝔛.εinf0_comp0 κ toκ)

theorem εinf0_comp1_assoc {Z : Scheme.{0}} (g : fibre (N₀ := N₀) toκ ⟶ Z) :
    𝔛.εinf0 toκ ≫ 𝔛.comp κ toκ 1 ≫ g = sectionFibre 𝔛.εzero toκ ≫ g := by
  simpa only [Category.assoc] using congrArg (· ≫ g) (𝔛.εinf0_comp1 κ toκ)

theorem fibre0_snd_eq :
    pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) = inv (𝔛.efib κ toκ) ≫ (𝔛.Mfib κ toκ).toBase := by
  rw [IsIso.eq_inv_comp, 𝔛.hefib]

include 𝔛 in
theorem isProper_fibre0 : IsProper (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := by
  rw [𝔛.fibre0_snd_eq toκ]; infer_instance

include 𝔛 in
theorem smoothOfRelativeDimension_one_fibre0 :
    SmoothOfRelativeDimension 1 (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := by
  rw [𝔛.fibre0_snd_eq toκ]
  exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

include 𝔛 in
theorem isIntegral_fibre0 : IsIntegral (fibre0 (N₀ := N₀) toκ) :=
  haveI : Nonempty ↥(fibre0 (N₀ := N₀) toκ) := ⟨(𝔛.efib κ toκ).base (Nonempty.some inferInstance)⟩
  isIntegral_of_isOpenImmersion (inv (𝔛.efib κ toκ))

include 𝔛 in

theorem isProper_fibre : IsProper (pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
  MorphismProperty.pullback_snd (P := @IsProper) _ _ 𝔛.isProper

theorem fibre_section_eq_zero_of_comp_app_eq_zero (U : (fibre (N₀ := N₀) toκ).Opens) (s : Γ(fibre (N₀ := N₀) toκ, U))
    (h0 : ((𝔛.comp κ toκ 0).app U).hom s = 0) (h1 : ((𝔛.comp κ toκ 1).app U).hom s = 0) : s = 0 := by
  haveI := 𝔛.fibre_reduced κ toκ
  rw [← basicOpen_eq_bot_iff]
  ext x
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  rcases 𝔛.comp_jointly_surjective κ toκ x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · have hy : y ∈ (𝔛.comp κ toκ 0) ⁻¹ᵁ ((fibre (N₀ := N₀) toκ).basicOpen s) := hx
    rw [Scheme.preimage_basicOpen] at hy
    have : ((𝔛.comp κ toκ 0).app U).hom s = (𝔛.comp κ toκ 0).app U s := rfl
    rw [← this, h0, Scheme.basicOpen_zero] at hy
    exact hy
  · have hy : y ∈ (𝔛.comp κ toκ 1) ⁻¹ᵁ ((fibre (N₀ := N₀) toκ).basicOpen s) := hx
    rw [Scheme.preimage_basicOpen] at hy
    have : ((𝔛.comp κ toκ 1).app U).hom s = (𝔛.comp κ toκ 1).app U s := rfl
    rw [← this, h1, Scheme.basicOpen_zero] at hy
    exact hy

end

end DRModelPackageLevel

end ModularCurve

end


