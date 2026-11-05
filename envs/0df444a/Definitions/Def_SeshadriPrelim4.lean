-- Prove2me | Definitions.Def_SeshadriPrelim4
-- name    : SeshadriPrelim4
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:44:19.447203+00:00
-- url     : https://prove2.me/theorems/dd73364d-13f4-40e2-8b4d-569ae594af41
-- title:
--   Maximal Seshadri constants: supporting development, part 4
-- statement:
--   Part 4 of 6 of the supporting Lean development for the maximal Seshadri constants theorem. It holds the definitions that the statements of the published child theorems refer to, in source order, together with the proved lemmas that their bodies and type class instances rely on. No result is assumed: every lemma here has a proof. Source modules: `Analytic.CoordinateJets`, `Analytic.FormalSeries`, `Cohomology.AffineVanishing`, `Cohomology.FiniteCover`, `Cohomology.RestrictionComparison`, `Cohomology.ToricH1`, `Cohomology.ToricPresentation`, `Cohomology.ToricSpan`, `Configurations.AffinePointParameters`, `Divisors.BaseSections`, `Divisors.MixedSections`, `Divisors.OpenSectionsLinear`, `Interpolation.ConvergentSeries`, `Interpolation.InitialBasis`, `Interpolation.PrimitiveDirections`, `Interpolation.QuadrilateralRows`, `Interpolation.TriangleJets`, `Interpolation.WeightedRescaling`, `Lattice.InitialWeights`, `Lattice.NodePolygon`, `Sheaves.CartierModule`, `Sheaves.CartierTensor`, `Sheaves.PowerExtension`, `Sheaves.PushforwardTensor`, `Sheaves.RestrictedSections`, `Sheaves.SectionOpens`, `Sheaves.Sections`, `Sheaves.TensorPure`.
--
--   **Formalization Note** Definitions of this development carry proof fields, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/AlgebraicGeometry/Seshadri` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`. Edits for the port: in `ExtSectionComparison.mapFrom_bijective`, the line `rfl` is added.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim3

set_option linter.all false

section
namespace OAI

section

namespace MaximalSeshadri.TensorPure
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}}

local instance sectionModule (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (op U)) :=
  (M.val.obj (op U)).isModule

abbrev presheaf (M N : X.Modules) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val

abbrev adj (X : Scheme.{0}) :=
  PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

def pure (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.obj (op U) :=
  (((adj X).unit.app (presheaf M N)).app (op U)).hom (m ⊗ₜ[Γ(X,U)] n)

@[simp] lemma pure_add_left (M N : X.Modules) (U : X.Opens) (m m' : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (m+m') n = pure M N U m n + pure M N U m' n := by
  unfold pure
  rw [TensorProduct.add_tmul]
  exact map_add _ _ _

@[simp] lemma pure_add_right (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n n' : N.val.obj (op U)) :
    pure M N U m (n+n') = pure M N U m n + pure M N U m n' := by
  unfold pure
  rw [TensorProduct.tmul_add]
  exact map_add _ _ _

@[simp] lemma pure_smul_left (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (a • m) n = a • pure M N U m n := by
  unfold pure
  rw [← TensorProduct.smul_tmul']
  exact (((adj X).unit.app (presheaf M N)).app (op U)).hom.map_smul a
    (m ⊗ₜ[Γ(X,U)] n)

@[simp] lemma pure_smul_right (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U m (a • n) = a • pure M N U m n := by
  unfold pure
  rw [TensorProduct.tmul_smul]
  exact (((adj X).unit.app (presheaf M N)).app (op U)).hom.map_smul a
    (m ⊗ₜ[Γ(X,U)] n)

lemma pure_restrict (M N : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.map i.op (pure M N U m n) =
      pure M N V (M.val.map i.op m) (N.val.map i.op n) := by
  exact (PresheafOfModules.naturality_apply ((adj X).unit.app (presheaf M N)) i.op
    (m ⊗ₜ[Γ(X,U)] n)).symm

end
end MaximalSeshadri.TensorPure

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri
open scoped BigOperators Topology
open Filter Set
noncomputable def exponentWeight (t : ℝ) (p : Exponent) : ℝ := p.1 + t * p.2

def LexInitial (c : Exponent → ℂ) (t : ℝ) (e : Exponent) : Prop :=
  c e ≠ 0 ∧ ∀ p, c p ≠ 0 →
    exponentWeight t e ≤ exponentWeight t p ∧
    (exponentWeight t e = exponentWeight t p → e.2 ≤ p.2)

end MaximalSeshadri

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma spec_openScalars {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (openScalars f U.1)) = U.2.fromSpec ≫ f := by
  change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U.1 (by simp)) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)

def affineComplexPoint {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens)
    (ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ) :
    Over.mk (𝟙 complexBase) ⟶ Over.mk f := by
  letI := (openScalars f U.1).toAlgebra
  refine Over.homMk (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ U.2.fromSpec) ?_
  rw [Category.assoc,← spec_openScalars,← Spec.map_comp,← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact ρ.comp_algebraMap

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

def compressedTriangle (d H t : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(-(d * H / (1 + t)), 0), (d * H * t / (1 + t), 0), (0, 1 / d)}

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise

noncomputable def polynomialMoment (xs : Finset ℤ) (d : ℤ → ℂ) :
    Polynomial ℂ →ₗ[ℂ] ℂ :=
  ∑ x ∈ xs, d x • Polynomial.leval (x : ℂ)

@[simp] theorem polynomialMoment_apply (xs : Finset ℤ) (d : ℤ → ℂ) (p : Polynomial ℂ) :
    polynomialMoment xs d p = ∑ x ∈ xs, d x * p.eval (x : ℂ) := by
  simp [polynomialMoment]

noncomputable def laurentEval (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (u z : ℂ) : ℂ :=
  ∑ y ∈ rows s, (∑ x ∈ row s y, c (x, y) * u ^ x) * z ^ y

def MixedJetZero (f : ℂ → ℂ → ℂ) (u z : ℂ) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    iteratedDeriv b (fun v : ℂ => iteratedDeriv a (fun w : ℂ => f w v) u) z = 0

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set
abbrev Exponent := ℕ × ℕ

noncomputable def seriesEval (c : Exponent → ℂ) (x z : ℂ) : ℂ :=
  ∑' p : Exponent, c p * x ^ p.1 * z ^ p.2

noncomputable def derivativeMajorant (c : Exponent → ℂ) (R : ℝ) (a b : ℕ)
    (p : Exponent) : ℝ :=
  ‖c p‖ * ((p.1.descFactorial a : ℝ) * R ^ (p.1 - a)) *
    ((p.2.descFactorial b : ℝ) * R ^ (p.2 - b))

def DerivativeSummable (c : Exponent → ℂ) (R : ℝ) : Prop :=
  ∀ a b : ℕ, Summable (derivativeMajorant c R a b)

def AbsolutelyConvergentAt (c : Exponent → ℂ) (R : ℝ) : Prop :=
  Summable (fun p : Exponent => ‖c p‖ * R ^ (p.1 + p.2))

def ConvergentSeries (c : Exponent → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ AbsolutelyConvergentAt c R

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FlasqueCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Abelian
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def sectionsTopEquiv (M : SheafOfModules.{u} R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def globalHomEquiv (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op ⊤) :=
  M.unitHomEquiv.trans (sectionsTopEquiv R M)

lemma globalHomEquiv_comp {M N : SheafOfModules.{u} R}
    (f : SheafOfModules.unit R ⟶ M) (g : M ⟶ N) :
    globalHomEquiv R N (f ≫ g) = g.val.app (op ⊤) (globalHomEquiv R M f) := rfl

theorem globalHom_surjective {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)] :
    Function.Surjective (fun f : SheafOfModules.unit R ⟶ S.X₂ => f ≫ S.g) := by
  have h := ModuleSheafExact.shortExact_map R hS
  let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
    ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)›
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) h
  have hs := (AddCommGrpCat.epi_iff_surjective
    (((SheafOfModules.toSheaf R).map S.g).hom.app (op ⊤))).mp he
  intro f
  obtain ⟨t, ht⟩ := hs (globalHomEquiv R S.X₃ f)
  let t' : S.X₂.val.obj (op ⊤) := t
  have ht' : S.g.val.app (op ⊤) t' = globalHomEquiv R S.X₃ f := ht
  refine ⟨(globalHomEquiv R S.X₂).symm t', ?_⟩
  apply (globalHomEquiv R S.X₃).injective
  rw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  exact ht'

instance moduleSheafHasExt : HasExt.{u+1} (SheafOfModules.{u} R) :=
  HasExt.standard _

theorem flasque_ext_zero (n : ℕ) (M : SheafOfModules.{u} R)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)]
    (x : Ext.{u+1} (SheafOfModules.unit R) M (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g, rfl⟩ := globalHom_surjective R hS f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
      ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)›
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₂) :=
      ModuleFlasque.injective_isFlasque R (Injective.under M)
    have : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₃) :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (ModuleSheafExact.shortExact_map R hS)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

end
end MaximalSeshadri.FlasqueCohomology

namespace MaximalSeshadri.AffineCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open FlasqueCohomology
universe u
variable {R : CommRingCat.{u}}

def structureSheafUnit (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def schemeGlobalHomEquiv (X : Scheme.{u}) (M : X.Modules) :
    (structureSheafUnit X ⟶ M) ≃ (Scheme.Modules.presheaf M).obj (op ⊤) :=
  globalHomEquiv X.ringCatSheaf M

lemma globalHom_tilde_surjective {M N : ModuleCat.{u} R} (g : M ⟶ N) [Epi g] :
    Function.Surjective (fun f : structureSheafUnit (Spec R) ⟶ tilde M =>
      f ≫ tilde.map g) := by
  intro f
  obtain ⟨q,hq⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).surjective
    (schemeGlobalHomEquiv (Spec R) (tilde N) f)
  obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance q
  let lifted : (Scheme.Modules.presheaf (tilde M)).obj (op ⊤) := tilde.toOpen M ⊤ p
  refine ⟨(schemeGlobalHomEquiv (Spec R) (tilde M)).symm lifted, ?_⟩
  apply (schemeGlobalHomEquiv (Spec R) (tilde N)).injective
  change ((tilde.map g).app ⊤)
    ((schemeGlobalHomEquiv (Spec R) (tilde M))
      ((schemeGlobalHomEquiv (Spec R) (tilde M)).symm lifted)) = _
  rw [Equiv.apply_symm_apply]
  change ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op ⊤)) (tilde.toOpen M ⊤ p) = _
  have h := CategoryTheory.congr_fun (tilde.toOpen_map_app g ⊤) p
  exact h.trans (by change tilde.toOpen N ⊤ (g p) = _; rw [hp, hq])

local instance affineHasExt : HasExt.{u+1} (Spec R).Modules := HasExt.standard _

theorem tilde_ext_zero [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R)
    (x : Ext.{u+1} (C := (Spec R).Modules)
      (structureSheafUnit (Spec R)) (tilde M) (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T : ShortComplex (Spec R).Modules :=
      { X₁ := tilde S.X₁
        X₂ := tilde S.X₂
        X₃ := tilde S.X₃
        f := tilde.map S.f
        g := tilde.map S.g
        zero := (S.map (tilde.functor R)).zero }
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf 0 (tilde S.X₂) _) rfl
    obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g,rfl⟩ := globalHom_tilde_surjective S.g f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      show (Ext.mk₀ (tilde.map S.g)).comp hT.extClass rfl = 0 from hT.comp_extClass,
      Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T : ShortComplex (Spec R).Modules :=
      { X₁ := tilde S.X₁
        X₂ := tilde S.X₂
        X₃ := tilde S.X₃
        f := tilde.map S.f
        g := tilde.map S.g
        zero := (S.map (tilde.functor R)).zero }
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf (n+1) (tilde S.X₂) _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

theorem quasicoherent_ext_zero [IsNoetherianRing R] (n : ℕ) (M : (Spec R).Modules)
    [M.IsQuasicoherent]
    (x : Ext.{u+1} (C := (Spec R).Modules)
      (structureSheafUnit (Spec R)) M (n+1)) : x = 0 := by
  let e := asIso M.fromTildeΓ
  have hx := tilde_ext_zero n _ (x.comp (Ext.mk₀ e.inv) (add_zero _))
  have h := congrArg (fun y => y.comp (Ext.mk₀ e.hom) (add_zero (n+1))) hx
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    e.inv_hom_id, Ext.comp_mk₀_id, Ext.zero_comp] using h

end
end MaximalSeshadri.AffineCohomology

namespace MaximalSeshadri.RestrictionExact
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_mono {M N : Y.Modules} (g : M ⟶ N) [Mono g] :
    Mono ((Scheme.Modules.restrictFunctor f).map g) := by
  apply (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map g))
  exact PresheafOfModules.injective_of_mono g.val (op (f ''ᵁ U.unop))

instance restriction_preservesMonomorphisms :
    (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves g _ := restriction_mono f g

instance restriction_additive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext; rfl

instance restriction_preservesHomology :
    (Scheme.Modules.restrictFunctor f).PreservesHomology :=
  (Scheme.Modules.restrictFunctor f).preservesHomology_of_preservesMonos_and_cokernels

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictFunctor f).preservesFiniteLimits_of_preservesHomology

instance restriction_flasque (M : Y.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (M.restrict f)) where
  epi {U V} i := by
    change Epi (((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj.map
      (f.opensFunctor.map i.unop).op)
    exact TopCat.Presheaf.IsFlasque.epi _

end
end MaximalSeshadri.RestrictionExact

namespace MaximalSeshadri.AffineSchemeCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open Scheme.Modules
universe u

def restrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId (X := Y)).symm ≪≫ (restrictFunctorCongr e.inv_hom_id).symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId (X := X))

local instance hasExtScheme (X : Scheme.{u}) : HasExt.{u+1} X.Modules := HasExt.standard _

theorem affine_ext_zero (X : Scheme.{u}) [IsAffine X] [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules)
      (AffineCohomology.structureSheafUnit X) M (n+1)) : x = 0 := by
  let : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let E := restrictionEquivalence X.isoSpec.symm
  let F := E.functor
  let : F.Additive := RestrictionExact.restriction_additive _
  let : EnoughInjectives X.Modules := ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  let e : F.obj (AffineCohomology.structureSheafUnit X) ≅
      AffineCohomology.structureSheafUnit (Spec Γ(X, ⊤)) :=
    restrictUnitIso X.isoSpec.inv
  let z : Ext.{u+1} (F.obj (AffineCohomology.structureSheafUnit X)) (F.obj M) (n+1) :=
    x.mapExactFunctor F
  have hz : z = 0 := by
    have hw : (Ext.mk₀ e.inv).comp z (zero_add _) = 0 :=
      AffineCohomology.quasicoherent_ext_zero n (M.restrict X.isoSpec.inv)
        ((Ext.mk₀ e.inv).comp z (zero_add _))
    have h := congrArg (fun y => (Ext.mk₀ e.hom).comp y (zero_add (n+1))) hw
    simpa only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp,
      Ext.comp_zero] using h
  have hb : Function.Injective (F.mapExtAddHom (AffineCohomology.structureSheafUnit X) M (n+1) :
      Ext.{u+1} (C := X.Modules) (AffineCohomology.structureSheafUnit X) M (n+1) →
      Ext.{u+1} (F.obj (AffineCohomology.structureSheafUnit X)) (F.obj M) (n+1)) :=
    (F.mapExt_bijective_of_preservesInjectiveObjects _ _ (n+1)).injective
  apply hb
  simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_zero] using hz

end
end MaximalSeshadri.AffineSchemeCohomology

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter

local instance : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite

lemma absolute_add {c d : Exponent → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R) :
    AbsolutelyConvergentAt (c + d) R := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hc.add hd)
  change ‖c p + d p‖ * R ^ (p.1 + p.2) ≤ _
  calc
    _ ≤ (‖c p‖ + ‖d p‖) * R ^ (p.1 + p.2) :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hR _)
    _ = _ := by ring

lemma seriesEval_add {c d : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R)
    {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    seriesEval (c + d) x z = seriesEval c x z + seriesEval d x z := by
  simp only [seriesEval, Pi.add_apply, add_mul]
  exact (absolute_terms_summable hc hx hz).of_norm.tsum_add
    (absolute_terms_summable hd hx hz).of_norm

lemma eventually_polydisk {R : ℝ} (hR : 0 < R) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 0, ‖q.1‖ < R ∧ ‖q.2‖ < R := by
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨R, hR, fun q hq => ?_⟩
  simpa only [dist_zero_right, Prod.norm_def, max_lt_iff] using hq

lemma common_absolute_radius {c d : Exponent → ℂ}
    (hc : ConvergentSeries c) (hd : ConvergentSeries d) :
    ∃ R : ℝ, 0 < R ∧ AbsolutelyConvergentAt c R ∧ AbsolutelyConvergentAt d R := by
  obtain ⟨R, hR, hc⟩ := hc
  obtain ⟨S, hS, hd⟩ := hd
  refine ⟨min R S, lt_min hR hS, ?_, ?_⟩
  · exact absolute_mono hc (le_min hR.le hS.le) (min_le_left _ _)
  · exact absolute_mono hd (le_min hR.le hS.le) (min_le_right _ _)

lemma analyticCoefficients_add (f g : analyticFunctionAlgebra) :
    analyticCoefficients (f + g) = analyticCoefficients f + analyticCoefficients g := by
  obtain ⟨R, hR, hf, hg⟩ := common_absolute_radius
    (analyticCoefficients_spec f).1 (analyticCoefficients_spec g).1
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec (f + g)).1
    ⟨R, hR, absolute_add hR.le hf hg⟩
  filter_upwards [(analyticCoefficients_spec (f + g)).2,
    (analyticCoefficients_spec f).2, (analyticCoefficients_spec g).2,
    eventually_polydisk hR] with q hfg hfe hge hq
  rw [← hfg, seriesEval_add hf hg hq.1.le hq.2.le]
  change f.val q + g.val q = _
  rw [hfe, hge]

lemma analyticCoefficients_mul (f g : analyticFunctionAlgebra) :
    analyticCoefficients (f * g) = coeffConvolution (analyticCoefficients f)
      (analyticCoefficients g) := by
  obtain ⟨R, hR, hf, hg⟩ := common_absolute_radius
    (analyticCoefficients_spec f).1 (analyticCoefficients_spec g).1
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec (f * g)).1
    ⟨R, hR, absolute_convolution hR.le hf hg⟩
  filter_upwards [(analyticCoefficients_spec (f * g)).2,
    (analyticCoefficients_spec f).2, (analyticCoefficients_spec g).2,
    eventually_polydisk hR] with q hfg hfe hge hq
  rw [← hfg, seriesEval_convolution hf hg hq.1.le hq.2.le]
  change f.val q * g.val q = _
  rw [hfe, hge]

lemma analyticCoefficients_const (a : ℂ) :
    analyticCoefficients (algebraMap ℂ analyticFunctionAlgebra a) =
      fun e => if e = (0,0) then a else 0 := by
  let c : Exponent → ℂ := fun e => if e = (0,0) then a else 0
  have hc : ConvergentSeries c := by
    refine ⟨1, zero_lt_one, ?_⟩
    simp only [AbsolutelyConvergentAt, c, apply_ite, norm_zero, one_pow, mul_one]
    exact (hasSum_ite_eq (0,0) ‖a‖).summable
  have he (x z : ℂ) : seriesEval c x z = a := by
    simp [seriesEval, c, ite_mul]
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec _).1 hc
  filter_upwards [(analyticCoefficients_spec (algebraMap ℂ analyticFunctionAlgebra a)).2]
    with q hq
  rw [← hq, he]
  rfl

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open PowerSeries Filter

local instance : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite

abbrev BiSeries := PowerSeries (PowerSeries ℂ)

def biCoeff (f : BiSeries) (e : Exponent) : ℂ := coeff e.1 (coeff e.2 f)

def biSeries (c : Exponent → ℂ) : BiSeries :=
  PowerSeries.mk (fun b => PowerSeries.mk (fun a => c (a,b)))

@[simp] lemma biCoeff_biSeries (c : Exponent → ℂ) (e : Exponent) :
    biCoeff (biSeries c) e = c e := by simp [biCoeff, biSeries]

lemma biCoeff_injective : Function.Injective biCoeff := by
  intro f g h
  apply PowerSeries.ext
  intro b
  apply PowerSeries.ext
  intro a
  exact congrFun h (a,b)

lemma biCoeff_mul (f g : BiSeries) (e : Exponent) :
    biCoeff (f * g) e = coeffConvolution (biCoeff f) (biCoeff g) e := by
  classical
  simp only [biCoeff, coeff_mul, map_sum]
  rw [← Finset.sum_product _ _
    (fun ij : (ℕ × ℕ) × (ℕ × ℕ) =>
      (coeff ij.2.1 (coeff ij.1.1 f)) * (coeff ij.2.2 (coeff ij.1.2 g)))]
  apply Finset.sum_bij (fun ij _ => ((ij.2.1,ij.1.1),(ij.2.2,ij.1.2)))
  · intro ij hij
    rcases Finset.mem_product.mp hij with ⟨h₁,h₂⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h₁ h₂ ⊢
    exact Prod.ext h₂ h₁
  · intro i hi j hj he
    have h₁ := congrArg (fun p : Exponent × Exponent => (p.1.2,p.2.2)) he
    have h₂ := congrArg (fun p : Exponent × Exponent => (p.1.1,p.2.1)) he
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)
  · intro p hp
    refine ⟨((p.1.2,p.2.2),(p.1.1,p.2.1)), ?_, rfl⟩
    rw [Finset.mem_product]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    refine ⟨congrArg Prod.snd hp, ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact congrArg Prod.fst hp
  · intro ij hij
    rfl

def analyticFormal : analyticFunctionAlgebra →ₐ[ℂ] BiSeries where
  toFun f := biSeries (analyticCoefficients f)
  map_one' := by
    apply biCoeff_injective
    ext e
    have h := analyticCoefficients_const 1
    simp only [map_one] at h
    simp only [biCoeff_biSeries, h]
    rcases e with ⟨a,b⟩
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [biCoeff, ha, hb]
  map_mul' f g := by
    apply biCoeff_injective
    ext e
    simp only [biCoeff_biSeries, analyticCoefficients_mul, biCoeff_mul]
    congr 1 <;> ext a <;> exact biCoeff_biSeries _ _ |>.symm
  map_zero' := by
    apply biCoeff_injective
    ext e
    have h := analyticCoefficients_const 0
    simp only [map_zero, ite_self] at h
    simp [h, biCoeff, biSeries]
  map_add' f g := by
    apply biCoeff_injective
    ext e
    simp [analyticCoefficients_add, biCoeff, biSeries]
  commutes' a := by
    apply biCoeff_injective
    ext e
    simp only [biCoeff_biSeries, analyticCoefficients_const]
    rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
    simp only [Algebra.algebraMap_self]
    rcases e with ⟨k,b⟩
    by_cases hk : k = 0 <;> by_cases hb : b = 0 <;> simp [biCoeff, coeff_C, hk, hb]

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open PowerSeries

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

def powerSeriesMapEquiv (e : A ≃ₐ[F] B) : PowerSeries A ≃ₐ[F] PowerSeries B :=
  AlgEquiv.ofAlgHom (PowerSeries.mapAlgHom e.toAlgHom)
    (PowerSeries.mapAlgHom e.symm.toAlgHom)
    (by ext f n; simp [PowerSeries.mapAlgHom_apply])
    (by ext f n; simp [PowerSeries.mapAlgHom_apply])

def binaryEquiv (F : Type*) [CommRing F] :
    MvPowerSeries (Fin 2) F ≃ₐ[F] PowerSeries (PowerSeries F) :=
  (MvPowerSeries.finSuccEquiv F 1).trans (powerSeriesMapEquiv
    ((MvPowerSeries.finSuccEquiv F 0).trans
      (powerSeriesMapEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) F))))

end
end MaximalSeshadri.FormalCoordinates

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.SectionOpens
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N : X.Modules}

lemma isIso_of_stalks (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf)) :
    IsIso f := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let A : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let B : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let φ : A ⟶ B := ⟨f.mapPresheaf⟩
  let (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map φ.hom) := h x.val
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso φ U

lemma stalk_isIso_of_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    [IsIso ((Scheme.Modules.restrictFunctor φ).map f)] (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf) := by
  apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
    ((Scheme.Modules.toPresheaf Y).map ((Scheme.Modules.restrictFunctor φ).map f)))
  infer_instance

lemma restrict_isIso_of_stalks (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    (h : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf)) :
    IsIso ((Scheme.Modules.restrictFunctor φ).map f) := by
  apply isIso_of_stalks
  intro y
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mpr (h y)

lemma isIso_of_locally_isIso (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  apply isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x, hx⟩

def isoOpen (f : M ⟶ N) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)), U

lemma mem_isoOpen_iff (f : M ⟶ N) (x : X) :
    x ∈ isoOpen f ↔ ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  simp only [isoOpen, Opens.mem_iSup]
  aesop

theorem isIso_restrict_isoOpen (f : M ⟶ N) :
    IsIso ((Scheme.Modules.restrictFunctor (isoOpen f).ι).map f) := by
  apply restrict_isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := (mem_isoOpen_iff f x.val).mp x.property
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x.val, hx⟩

end
end MaximalSeshadri.SectionOpens

namespace MaximalSeshadri.SectionOpens
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N P : X.Modules}

lemma isoOpen_precomp (e : P ≅ M) (f : M ⟶ N) :
    isoOpen (e.hom ≫ f) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (e.hom ≫ f) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictFunctor U.ι).map e.hom) ((Scheme.Modules.restrictFunctor U.ι).map f)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (e.hom ≫ f) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    isoOpen ((Scheme.Modules.restrictFunctor φ).map f) = φ ⁻¹ᵁ isoOpen f := by
  ext y
  constructor
  · intro hy
    obtain ⟨V, hyV, hV⟩ := (mem_isoOpen_iff _ y).mp hy
    let := hV
    apply (mem_isoOpen_iff f (φ y)).mpr
    refine ⟨φ ''ᵁ V, ⟨y, hyV, rfl⟩, ?_⟩
    apply restrict_isIso_of_stalks
    intro x
    obtain ⟨z, hz, he⟩ := x.property
    change φ z = x.val at he
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map f.mapPresheaf)
    rw [← he]
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z) f).mp
    exact stalk_isIso_of_restrict ((Scheme.Modules.restrictFunctor φ).map f) V.ι ⟨z, hz⟩
  · intro hy
    change φ y ∈ isoOpen f at hy
    let U := φ ⁻¹ᵁ isoOpen f
    apply (mem_isoOpen_iff _ y).mpr
    refine ⟨U, hy, ?_⟩
    apply restrict_isIso_of_stalks
    intro z
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z.val) f).mpr
    let := isIso_restrict_isoOpen f
    exact stalk_isIso_of_restrict f (isoOpen f).ι ⟨φ z.val, z.property⟩

end
end MaximalSeshadri.SectionOpens
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma isoOpen_restrictSection {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    SectionOpens.isoOpen (restrictSection φ s) = φ ⁻¹ᵁ SectionOpens.isoOpen s := by
  exact (SectionOpens.isoOpen_precomp (Scheme.Modules.restrictUnitIso φ).symm
    ((Scheme.Modules.restrictFunctor φ).map s)).trans (SectionOpens.isoOpen_restrict s φ)

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleSectionsTopEquiv {T : TopCat} (R : Sheaf (Opens.grothendieckTopology T) RingCat)
    (M : SheafOfModules R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def moduleSectionEquiv (M : X.Modules) : (O X ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (moduleSectionsTopEquiv X.ringCatSheaf M)

@[simp] lemma moduleSectionEquiv_apply (M : X.Modules) (s : O X ⟶ M) :
    moduleSectionEquiv M s = s.app ⊤ (1 : Γ(X, ⊤)) := rfl

def openSectionEquiv (M : X.Modules) (U : X.Opens) :
    (O U.toScheme ⟶ M.restrict U.ι) ≃ Γ(M, U) :=
  (moduleSectionEquiv (M.restrict U.ι)).trans
    (let e := M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
     { toFun := e.hom
       invFun := e.inv
       left_inv := fun t => Iso.hom_inv_id_apply e t
       right_inv := fun t => Iso.inv_hom_id_apply e t })

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open MaximalSeshadri.Frames
variable {X : Scheme}

def mixedPowMap {M N : X.Modules} :
    ∀ n, (Fin n → (M ⟶ N)) → (modulePow X M n ⟶ modulePow X N n)
  | 0, _ => 𝟙 _
  | n + 1, f => moduleTensorMap (f 0) (mixedPowMap n (fun i => f i.succ))

lemma mixedPowMap_const {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    mixedPowMap n (fun _ => f) = modulePowMap f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change moduleTensorMap f (mixedPowMap n (fun _ => f)) =
      moduleTensorMap f (modulePowMap f n)
    rw [ih]

def mixedPowerSection {M : X.Modules} (n : ℕ) (s : Fin n → (structureSheaf X ⟶ M)) :
    structureSheaf X ⟶ modulePow X M n := (unitPowerIso n).inv ≫ mixedPowMap n s

lemma mixedPowerSection_const {M : X.Modules} (n : ℕ) (s : structureSheaf X ⟶ M) :
    mixedPowerSection n (fun _ => s) = powerSection s n := by
  simp only [mixedPowerSection, powerSection, mixedPowMap_const]

end
end MaximalSeshadri.Geometry

end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ModuleFlasque

variable {X : Scheme.{0}}

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)
instance (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

local instance (M : X.Modules) (U : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) :=
  sheafHomModule X _ _

def freeOpenLinearEquiv (M : X.Modules) (U : X.Opens) :
    ((freeOpen X.ringCatSheaf U : X.Modules) ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U where
  toEquiv := freeOpenEquiv X.ringCatSheaf M U
  map_add' := by intro f g; rfl
  map_smul' := by intro r f; rfl

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro scalar value
    change Γ(M,V) at value
    let : Module Γ(X,V) Γ(M,V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) Γ(M,U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V scalar • value) =
      restrictScalar X U scalar • M.presheaf.map (homOfLE h).op value
    exact (M.map_smul (homOfLE h) (restrictScalar X V scalar) value).trans
      (congrArg (fun coefficient : Γ(X,U) =>
        coefficient • M.presheaf.map (homOfLE h).op value)
        (restrictScalar_naturality X (homOfLE h) scalar))

lemma freeOpenLinearEquiv_naturality (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (f : (freeOpen X.ringCatSheaf V : X.Modules) ⟶ M) :
    freeOpenLinearEquiv M U (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ f) =
      openRestriction M h (freeOpenLinearEquiv M V f) :=
  freeOpenEquiv_naturality X.ringCatSheaf M _ f

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M]

def weight : Fin 3 → ℤ × ℤ := ![(0,0),(1,0),(0,1)]
def vertexCone : Fin 3 → Set (ℤ × ℤ) :=
  ![coneA ∩ coneB,coneA ∩ coneC 0,coneB ∩ coneC 0]

end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.PushforwardTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def presheafHom (M N : X.Modules) :
    presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      ((Scheme.Modules.pushforward f).obj (moduleTensor X M N)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n => pure M N (f ⁻¹ᵁ U.unop) m n)
    (fun m m' n => pure_add_left M N _ m m' n)
    (fun a m n => pure_smul_left M N _ ((f.app U.unop).hom a) m n)
    (fun m n n' => pure_add_right M N _ m n n')
    (fun a m n => pure_smul_right M N _ ((f.app U.unop).hom a) m n)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (pure_restrict M N ((Opens.map f.base).map i.unop) m n).symm

def hom (M N : X.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (moduleTensor X M N) :=
  ((adj Y).homEquiv _ _).symm (presheafHom f M N)

end
end MaximalSeshadri.PushforwardTensor

namespace MaximalSeshadri.PullbackTensor
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def hom (M N : Y.Modules) : (Scheme.Modules.pullback f).obj (moduleTensor Y M N) ⟶
    moduleTensor X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _)

end
end MaximalSeshadri.PullbackTensor

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.NodalLocal
noncomputable section
open PowerSeries
open scoped BigOperators

def bivariateCoeff {K : Type*} [Field K] (f : Bivariate K) (e : Exponent) : K :=
  coeff e.1 (coeff e.2 f)

end
end MaximalSeshadri.NodalLocal

namespace MaximalSeshadri
noncomputable section
open scoped BigOperators

def nodeQuadrilateral (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(0, 0), (a, 0), (c, c), (0, b)}

namespace NodalLocal

end NodalLocal
end
end MaximalSeshadri

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set
noncomputable def exponentWeight (t : ℝ) (p : Exponent) : ℝ := p.1 + t * p.2

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.IdealModule
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureMap : unit Y ⟶
    (Scheme.Modules.pushforward f).obj (unit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp] lemma structureMap_app (U : Y.Opens) (x : Γ(Y, U)) :
    ((structureMap f).val.app (op U)) x = (f.app U) x := rfl

def idealModule : Y.Modules := kernel (structureMap f)

def inclusion : idealModule f ⟶ unit Y :=
  kernel.ι (structureMap f)

instance : Mono (inclusion f) := inferInstanceAs (Mono (kernel.ι (structureMap f)))

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def closedModule (I : X.IdealSheafData) : X.Modules := idealModule I.subschemeι

def closedInclusion (I : X.IdealSheafData) : closedModule I ⟶ unit X :=
  inclusion I.subschemeι

def multiply (r : Γ(X, ⊤)) : unit X ⟶ unit X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma multiply_app (r : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (multiply r).val.app (op U) a = X.presheaf.map (homOfLE le_top).op r * a := rfl

lemma multiply_structure_zero (f : Y ⟶ X) (r : Γ(X, ⊤))
    (hr : (f.app ⊤) r = 0) : multiply r ≫ structureMap f = 0 := by
  ext U a
  change Γ(X, U) at a
  change (f.app U) ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) *
    (a : Γ(X, U))) = 0
  rw [map_mul]
  have he : (f.app U) (X.presheaf.map (homOfLE le_top).op r) = 0 := by
    rw [← CommRingCat.comp_apply, f.naturality, CommRingCat.comp_apply, hr, map_zero]
  rw [he, zero_mul]

def equationToIdeal (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    unit X ⟶ idealModule f :=
  kernel.lift (structureMap f) (multiply r) (multiply_structure_zero f r hr)

@[reassoc (attr := simp)] lemma equationToIdeal_inclusion
    (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    equationToIdeal f r hr ≫ inclusion f = multiply r := kernel.lift_ι _ _ _

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}

def sectionFamily {M : X.Modules} (s : Γ(M, ⊤)) : M.sections where
  val U := M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s
  property {U V} i := by
    change (M.presheaf.map (homOfLE le_top).op ≫ M.presheaf.map i) s = _
    rw [← Functor.map_comp]
    rfl

def fromSection {M : X.Modules} (s : Γ(M, ⊤)) : unit X ⟶ M :=
  M.unitHomEquiv.symm (sectionFamily s)

@[simp] lemma fromSection_app {M : X.Modules} (s : Γ(M, ⊤))
    (U : X.Opens) (a : Γ(X, U)) :
    (fromSection s).val.app (op U) a = a • M.presheaf.map (homOfLE le_top).op s := rfl

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def restrictedInclusion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ unit X :=
  (Scheme.Modules.restrictFunctor f).map (closedInclusion I) ≫
    (Scheme.Modules.restrictUnitIso f).hom

instance restrictedInclusion_mono (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : Mono (restrictedInclusion I f) := by
  let : Mono (closedInclusion I) := inferInstanceAs (Mono (inclusion I.subschemeι))
  let : Mono ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) :=
    MaximalSeshadri.RestrictionExact.restriction_mono f (closedInclusion I)
  let unitIso : (unit Y).restrict f ≅ unit X := Scheme.Modules.restrictUnitIso f
  exact mono_comp ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) unitIso.hom

end

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

end
end MaximalSeshadri.IdealModule

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

end

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def specIdeal (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

@[simp] lemma specIdeal_top (I : Ideal R) :
    (specIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  simp [specIdeal]

end

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry
variable (X : Scheme)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
variable {X Y : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}

end

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry

end
end MaximalSeshadri.InvertibleLocal
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.TensorLocalization
noncomputable section
open CategoryTheory MonoidalCategory
universe v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

lemma map_tensor_right_unit {P Q L : C} (f : P ⟶ Q) (e : L ≅ 𝟙_ C)
    [IsIso (F.map f)] : IsIso (F.map (f ⊗ₘ 𝟙 L)) := by
  let ε (A : C) : A ⊗ L ≅ A := tensorIso (Iso.refl A) e ≪≫ ρ_ A
  have h : (f ⊗ₘ 𝟙 L) ≫ (ε Q).hom = (ε P).hom ≫ f := by
    simp only [ε, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have ht : f ⊗ₘ e.hom = (𝟙 P ⊗ₘ e.hom) ≫ (f ⊗ₘ 𝟙 (𝟙_ C)) := by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.id_comp, Category.comp_id]
    rw [ht, Category.assoc, tensorHom_id, rightUnitor_naturality, Category.assoc]
  have hh : IsIso (F.map ((f ⊗ₘ 𝟙 L) ≫ (ε Q).hom)) := by
    rw [h, F.map_comp]
    infer_instance
  rw [F.map_comp] at hh
  exact (isIso_comp_right_iff _ _).mp hh

end
end MaximalSeshadri.TensorLocalization

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_right_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val))) := by
  let sheafificationIso := asIso
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)
  apply SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let R := modulePresheafRestrict U.ι
  let S := PresheafOfModules.sheafification (R := U.toScheme.ringCatSheaf)
    (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  have hf : IsIso (S.map (R.map f)) := by
    apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) f).mp
    change IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f))
    exact ((Scheme.Modules.restrictFunctor U.ι).mapIso sheafificationIso).isIso_hom
  let ep : R.obj L.sheaf.val ≅ 𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  have ht : IsIso (S.map ((R.map f) ⊗ₘ 𝟙 (R.obj L.sheaf.val))) :=
    TensorLocalization.map_tensor_right_unit S (R.map f) ep
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) _).mpr
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val)
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U f (𝟙 L.sheaf.val)
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U Q L.sheaf.val).hom)) := by
    rw [heq]
    erw [S.map_comp]
    have ht' : IsIso (S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))) := by
      erw [R.map_id]
      exact ht
    exact IsIso.comp_isIso'
      (S.mapIso (modulePresheafTensorRestrict U P L.sheaf.val)).isIso_hom ht'
  erw [S.map_comp] at hcomp
  have : IsIso (S.map (modulePresheafTensorRestrict U Q L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U Q L.sheaf.val)).isIso_hom
  exact (isIso_comp_right_iff _ _).mp hcomp

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory BraidedCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_left_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 L.sheaf.val) f)) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have := sheafification_tensor_right_isIso f L
  have h : IsIso (F.map ((𝟙 L.sheaf.val ⊗ₘ f) ≫ (β_ L.sheaf.val Q).hom)) := by
    rw [braiding_naturality, F.map_comp]
    infer_instance
  rw [F.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

def sheafificationTensorRight (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) P L.sheaf.val) ≅
    moduleTensor X ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
      L.sheaf := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  have ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      η (𝟙 L.sheaf.val))) := sheafification_tensor_right_isIso η L
  exact @asIso _ _ _ _ (F.map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      η (𝟙 L.sheaf.val))) ht

def sheafificationTensorLeft (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val P) ≅
    moduleTensor X L.sheaf
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  have ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      (𝟙 L.sheaf.val) η)) := sheafification_tensor_left_isIso η L
  exact @asIso _ _ _ _ (F.map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      (𝟙 L.sheaf.val) η)) ht

def lineTensorAssoc (L M N : LineBundle X) :
    moduleTensor X (moduleTensor X L.sheaf M.sheaf) N.sheaf ≅
      moduleTensor X L.sheaf (moduleTensor X M.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (L.sheaf.val ⊗ M.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ L.sheaf.val M.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeft (M.sheaf.val ⊗ N.sheaf.val) L

def linePowerAdd (L : LineBundle X) : ∀ m n : ℕ,
    modulePow X L.sheaf (m + n) ≅
      moduleTensor X (modulePow X L.sheaf m) (modulePow X L.sheaf n)
  | 0, n => by
      simpa only [Nat.zero_add, modulePow, structureSheaf] using (moduleTensorUnit (modulePow X L.sheaf n)).symm
  | m + 1, n => by
      rw [Nat.succ_add]
      exact moduleTensorIso (Iso.refl _) (linePowerAdd L m n) ≪≫
        (lineTensorAssoc L (L.pow m) (L.pow n)).symm

def linePowerMul (L : LineBundle X) (m : ℕ) : ∀ n : ℕ,
    modulePow X (modulePow X L.sheaf m) n ≅ modulePow X L.sheaf (m * n)
  | 0 => Iso.refl _
  | n + 1 => by
      rw [Nat.mul_succ, Nat.add_comm (m * n) m]
      exact moduleTensorIso (Iso.refl _) (linePowerMul L m n) ≪≫
        (linePowerAdd L m (m * n)).symm

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.ExtSectionComparison
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D] {A : C} {B : D} (e : B ⟶ F.obj A)

def mapFrom (Y : C) (n : ℕ) : Ext.{w} A Y n →+ Ext.{w'} B (F.obj Y) n :=
  ((Ext.mk₀ e).precomp (F.obj Y) (zero_add n)).comp (F.mapExtAddHom A Y n)

lemma mapFrom_apply (Y : C) (n : ℕ) (x : Ext.{w} A Y n) :
    mapFrom F e Y n x = (Ext.mk₀ e).comp (x.mapExactFunctor F) (zero_add n) := rfl

@[simp] lemma mapFrom_mk₀ {Y : C} (f : A ⟶ Y) :
    mapFrom F e Y 0 (Ext.mk₀ f) = Ext.mk₀ (e ≫ F.map f) := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

lemma mapFrom_comp {Y Z : C} {n m k : ℕ} (x : Ext.{w} A Y n)
    (y : Ext.{w} Y Z m) (h : n+m=k) :
    mapFrom F e Z k (x.comp y h) =
      (mapFrom F e Y n x).comp (y.mapExactFunctor F) h := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem mapFrom_bijective [EnoughInjectives C]
    (hhom : ∀ Y : C, Function.Bijective (fun f : A ⟶ Y => e ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I] (n : ℕ)
      (x : Ext.{w'} B (F.obj I) (n+1)), x = 0)
    (Y : C) (n : ℕ) : Function.Bijective (mapFrom F e Y n) := by
  induction n generalizing Y with
  | zero =>
    constructor
    · intro x y h
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
      rw [mapFrom_mk₀, mapFrom_mk₀] at h
      exact congrArg Ext.mk₀ ((hhom Y).injective ((Ext.mk₀_bijective _ _).injective h))
    · intro x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (hhom Y).surjective f
      exact ⟨Ext.mk₀ g, mapFrom_mk₀ F e g⟩
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let : Injective S.X₂ := I.injective
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (mapFrom F e S.X₂ n) (mapFrom F e S.X₃ n) (mapFrom F e S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _)
      (fun x => Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ B (hS.map F) x (hacyclic S.X₂ n _) rfl)
    · ext x
      symm
      change mapFrom F e _ _ (x.comp (Ext.mk₀ S.g) (add_zero n)) =
        (mapFrom F e _ _ x).comp (Ext.mk₀ (F.map S.g)) (add_zero n)
      rw [mapFrom_comp, Ext.mapExactFunctor_mk₀]
    · ext x
      symm
      change mapFrom F e _ _ (x.comp hS.extClass rfl) =
        (mapFrom F e _ _ x).comp (hS.map F).extClass rfl
      rw [mapFrom_comp, Ext.mapExactFunctor_extClass]
      rfl

end
end MaximalSeshadri.ExtSectionComparison

namespace MaximalSeshadri.RestrictionCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

def restrictionSectionsIso (M : X.Modules) : Γ(M.restrict U.ι,⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def restrictionHomEquiv (M : X.Modules) :
    (freeOpen X.ringCatSheaf U ⟶ M) ≃
      (SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ M.restrict U.ι) :=
  (freeOpenEquiv X.ringCatSheaf M U).trans
    ((restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.toEquiv.symm.trans
      (globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm)

lemma restrictionHomEquiv_comp {M N : X.Modules}
    (f : freeOpen X.ringCatSheaf U ⟶ M) (g : M ⟶ N) :
    restrictionHomEquiv U N (f ≫ g) =
      restrictionHomEquiv U M f ≫ (Scheme.Modules.restrictFunctor U.ι).map g := by
  apply (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).injective
  change (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι))
      ((globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).symm
        ((restrictionSectionsIso U N).inv
          (g.val.app (op U) (freeOpenEquiv X.ringCatSheaf M U f)))) =
    (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι))
      ((globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm
          ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f)) ≫
        ((Scheme.Modules.restrictFunctor U.ι).map g : SheafOfModules.Hom _ _))
  erw [Equiv.apply_symm_apply, globalHomEquiv_comp, Equiv.apply_symm_apply]
  change (restrictionSectionsIso U N).inv (g.val.app (op U)
    (freeOpenEquiv X.ringCatSheaf M U f)) =
    ((Scheme.Modules.restrictFunctor U.ι).map g).val.app (op ⊤)
      ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f))
  exact (CategoryTheory.congr_fun (g.mapPresheaf.naturality
    (eqToHom U.ι_image_top).op) _).symm

def restrictionGenerator : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (freeOpen X.ringCatSheaf U) :=
  restrictionHomEquiv U _ (𝟙 _)

lemma restrictionGenerator_comp {M : X.Modules}
    (f : freeOpen X.ringCatSheaf U ⟶ M) :
    restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
      restrictionHomEquiv U M f := by
  exact (restrictionHomEquiv_comp U (𝟙 _) f).symm.trans
    (congrArg (restrictionHomEquiv U M) (Category.id_comp f))

theorem restriction_ext_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective
      (ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
        (restrictionGenerator U) M n) := by
  let : EnoughInjectives X.Modules :=
    ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply ExtSectionComparison.mapFrom_bijective
  · intro N
    have heq : (fun f : freeOpen X.ringCatSheaf U ⟶ N =>
        restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
        restrictionHomEquiv U N := funext (restrictionGenerator_comp U)
    change Function.Bijective (fun f : freeOpen X.ringCatSheaf U ⟶ N =>
      restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f)
    rw [heq]
    exact (restrictionHomEquiv U N).bijective
  · intro I hI n x
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      @ModuleFlasque.injective_isFlasque _ X.ringCatSheaf I hI
    exact flasque_ext_zero U.toScheme.ringCatSheaf n (I.restrict U.ι) x

end
end MaximalSeshadri.RestrictionCohomology

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeOpenFunctor : Opens X ⥤ SheafOfModules.{u} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

lemma freeOpen_isPushout (U V : Opens X) :
    ((Opens.mayerVietorisSquare U V).toSquare.map (freeOpenFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  have h := (Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M))
  apply (Square.IsPullback.iff_of_equiv _ _
    (freeOpenEquiv R M (U ⊔ V)) (freeOpenEquiv R M U)
    (freeOpenEquiv R M V) (freeOpenEquiv R M (U ⊓ V))
    ?_ ?_ ?_ ?_).mpr h
  all_goals
    ext f
    exact freeOpenEquiv_naturality R M _ f

def shortComplex (U V : Opens X) : ShortComplex (SheafOfModules.{u} R) where
  X₁ := freeOpen R (U ⊓ V)
  X₂ := freeOpen R U ⊞ freeOpen R V
  X₃ := freeOpen R (U ⊔ V)
  f := biprod.lift (freeOpenMap R (homOfLE inf_le_left))
    (-(freeOpenMap R (homOfLE inf_le_right)))
  g := biprod.desc (freeOpenMap R (homOfLE le_sup_left))
    (freeOpenMap R (homOfLE le_sup_right))
  zero := ((Opens.mayerVietorisSquare U V).toSquare.map
    (freeOpenFunctor R)).cokernelCofork.condition

instance shortComplex_mono (U V : Opens X) : Mono (shortComplex R U V).f := by
  have : Mono ((shortComplex R U V).f ≫ biprod.snd) := by
    dsimp [shortComplex]
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

variable [HasExt.{w} (SheafOfModules.{u} R)]

end
end MaximalSeshadri.ModuleMayerVietoris

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    rfl
  rw [he] at h
  exact h

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

def monomialSpan {ι : Type*} (S : Set (ℤ × ℤ)) (g : ι → M) : Submodule K M :=
  Submodule.span K {v | ∃ i z, z ∈ S ∧ v = T (K := K) z • g i}

end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
open scoped BigOperators Topology
open Filter Set

def LexInitial (c : Exponent → ℂ) (t : ℝ) (e : Exponent) : Prop :=
  c e ≠ 0 ∧ ∀ p, c p ≠ 0 →
    exponentWeight t e ≤ exponentWeight t p ∧
    (exponentWeight t e = exponentWeight t p → e.2 ≤ p.2)

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FiniteCoverCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

def freeOpenModule (U : X.Opens) : X.Modules :=
  freeOpen (X := X.carrier) X.ringCatSheaf U

theorem affine_open_ext_zero (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules)
      (freeOpenModule U) M (n+1)) : x = 0 := by
  let : IsAffine U := hU
  let : IsNoetherian U := ⟨⟩
  let f : Ext.{u+1} (C := X.Modules) (freeOpenModule U) M (n+1) →+
      Ext.{u+1} (C := U.toScheme.Modules) (AffineCohomology.structureSheafUnit U)
        (M.restrict U.ι) (n+1) :=
    ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
      (RestrictionCohomology.restrictionGenerator U) M (n+1)
  apply (RestrictionCohomology.restriction_ext_bijective U M (n+1)).injective
  change f x = f 0
  rw [map_zero]
  exact AffineSchemeCohomology.affine_ext_zero U (M.restrict U.ι) n (f x)

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

end
end MaximalSeshadri.FiniteCoverCohomology

namespace MaximalSeshadri.FreeOpenUnit
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque FlasqueCohomology
universe u v

def isoFromHomEquiv {C : Type u} [Category.{v} C] {A B : C}
    (e : ∀ M, (A ⟶ M) ≃ (B ⟶ M))
    (hnat : ∀ {M N} (f : A ⟶ M) (g : M ⟶ N), e N (f ≫ g) = e M f ≫ g) :
    A ≅ B where
  hom := (e B).symm (𝟙 B)
  inv := e A (𝟙 A)
  hom_inv_id := by
    apply (e A).injective
    rw [hnat, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    rw [← hnat, Category.id_comp, Equiv.apply_symm_apply]

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeTopIso : freeOpen R ⊤ ≅ SheafOfModules.unit R :=
  isoFromHomEquiv
    (fun M => (freeOpenEquiv R M ⊤).trans (globalHomEquiv R M).symm)
    (by
      intro M N f g
      apply (globalHomEquiv R N).injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, globalHomEquiv_comp]
      rfl)

end
end MaximalSeshadri.FreeOpenUnit

namespace MaximalSeshadri.FiniteCoverCohomology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance hasExtScheme' (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

end
end MaximalSeshadri.FiniteCoverCohomology

end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def Sections (_ : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) := OpenSections M U
instance (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    AddCommGroup (Sections k M U) := inferInstanceAs (AddCommGroup (OpenSections M U))
instance globalModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (Sections k M U) := inferInstanceAs (Module Γ(X,⊤) (OpenSections M U))
instance baseModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K (Sections k M U) := Module.compHom (OpenSections M U) k

def res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Sections k M V →ₗ[K] Sections k M U where
  toFun := openRestriction M h
  map_add' := map_add _
  map_smul' r m := (openRestriction M h).map_smul (k r) m

def congr (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Sections k M U ≃ₗ[K] Sections k M V := by
  subst V
  exact LinearEquiv.refl K _

def restrictEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens) :
    Sections (f.appTop.hom.comp k) (M.restrict f) U ≃ₗ[K]
      Sections k M (f ''ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r m := (restrictedOpenSections M f U).map_smul (k r) m

lemma chart_image_top (U : X.Opens) : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

def chartTop (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤ ≃ₗ[K] Sections k M U :=
  (restrictEquiv k M U.ι ⊤).trans (congr k M (chart_image_top U))

end
end MaximalSeshadri.Geometry.BaseSections
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Tensor
noncomputable section
open TensorProduct
variable {R S A B P : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]
  [NoZeroSMulDivisors S P]

end
end MaximalSeshadri.Tensor

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry TensorProduct
variable {X : Scheme} (L : LineBundle X)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry TensorProduct
variable {X : Scheme} [IsIntegral X]

def sectionMultiplyPresheaf (L M : LineBundle X) (s : GlobalSections X L.sheaf) :
    M.sheaf.val ⟶ PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      L.sheaf.val M.sheaf.val := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (λ_ M.sheaf.val).inv ≫ (s.val ⊗ₘ 𝟙 M.sheaf.val)

def sectionMultiply (L M : LineBundle X) (s : GlobalSections X L.sheaf) :
    M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
  ((asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app
    M.sheaf).inv ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (sectionMultiplyPresheaf L M s)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme} [IsIntegral X]

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M]

def vertexBoundaries (A B C : Submodule K M) (V : Fin 3 → Submodule K M) :
    Submodule K (cycles A B C) :=
  boundaries A B C ((V 0).comap (A ⊓ B).subtype)
    ((V 1).comap (A ⊓ C).subtype) ((V 2).comap (B ⊓ C).subtype)

variable [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

end
end MaximalSeshadri.PlaneCech

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.Interpolation
open scoped BigOperators Pointwise
open scoped BigOperators ContDiff
open Filter Topology
def nodeQuadrilateral (a b c : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {(0, 0), (a, 0), (c, c), (0, b)}

open scoped BigOperators Topology
open Filter Set

end MaximalSeshadri.Interpolation
end

end OAI
end

section
namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter PowerSeries
open MaximalSeshadri.FormalCoordinates

variable {S : Type*} [CommRing S] [Algebra ℂ S]

def analyticPullback (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) : S →ₐ[ℂ] analyticFunctionAlgebra where
  toFun s := ⟨fun z => q z s, hq s⟩
  map_one' := Subtype.ext (funext fun z => (q z).map_one)
  map_mul' s t := Subtype.ext (funext fun z => (q z).map_mul s t)
  map_zero' := Subtype.ext (funext fun z => (q z).map_zero)
  map_add' s t := Subtype.ext (funext fun z => (q z).map_add s t)
  commutes' c := Subtype.ext (funext fun z => (q z).commutes c)

def analyticTaylor (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) :
    S →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ :=
  (binaryEquiv ℂ).symm.toAlgHom.comp (analyticFormal.comp (analyticPullback q hq))

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

variable [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open MaximalSeshadri.AlgebraicJets
variable {S : Type*} [CommRing S] [Algebra ℂ S]
  [Algebra (MvPolynomial (Fin 2) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]

end
end MaximalSeshadri.AnalyticCoordinates

end
end
end

end OAI
end


