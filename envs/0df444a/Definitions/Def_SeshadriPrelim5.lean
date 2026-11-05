-- Prove2me | Definitions.Def_SeshadriPrelim5
-- name    : SeshadriPrelim5
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T14:47:43.892454+00:00
-- url     : https://prove2.me/theorems/48e547d5-393d-44c0-b49c-391efad5a55d
-- title:
--   Maximal Seshadri constants: supporting development, part 5
-- statement:
--   Part 5 of 6 of the supporting Lean development for the maximal Seshadri constants theorem. It holds the definitions that the statements of the published child theorems refer to, in source order, together with the proved lemmas that their bodies and type class instances rely on. No result is assumed: every lemma here has a proof. Source modules: `Blowup.FiniteCenters`, `Blowup.Gluing`, `Blowup.LocalEquations`, `Blowup.LocalUniversal`, `Blowup.PlaneCharts`, `Blowup.Uniqueness`, `Cohomology.CurveCech`, `Cohomology.CurveH0Finite`, `Cohomology.PlanePairToric`, `Cohomology.PlaneVertex`, `Cohomology.SurfaceBaseCech`, `Cohomology.SurfaceCech`, `Cohomology.TripleComplex`, `Cohomology.TripleEvaluation`, `Cohomology.TripleExt`, `Cohomology.TripleFree`, `Cohomology.TripleTopExt`, `Divisors.SectionChart`, `Divisors.SectionIdeal`, `Geometry.ChartCoherence`, `Geometry.LineClosedUnit`, `Geometry.NestedChart`, `Geometry.NormalizedMixed`, `Geometry.PlaneCoordinates`, `Interpolation.GermInterpolation`, `Jets.NodalTaylor`, `Jets.QuadraticJets`, `Projective.GlobalQuartic`, `Projective.HyperplaneIdeal`, `Projective.HyperplaneSection`, `Projective.PolynomialCharts`, `Projective.ProjectiveRefinement`, `Projective.QuarticReindex`, `Projective.QuarticSubsystem`, `Projective.SectionMaps`, `Sheaves.ChartModuleMap`, `Sheaves.PlaneModules`, `Sheaves.PlaneProjectionModule`, `Sheaves.RestrictionLocalization`.
--
--   **Formalization Note** Definitions of this development carry proof fields, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/AlgebraicGeometry/Seshadri` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim4

set_option linter.all false

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque

variable {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X
local instance : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

local instance curveCechFreeHomGroup (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance curveCechFreeHomModule (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _

def extSourceIso {E F : X.Modules} (e : E ≅ F) (M : X.Modules) (n : ℕ) :
    Ext.{1} E M n ≃ₗ[Γ(X,⊤)] Ext.{1} F M n where
  toFun := (Ext.mk₀ e.inv).precompOfLinear Γ(X,⊤) M (zero_add n)
  invFun := (Ext.mk₀ e.hom).precompOfLinear Γ(X,⊤) M (zero_add n)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

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

namespace MaximalSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def map (L : LineBundle Y) : L.sheaf ⟶
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf

end
end MaximalSeshadri.LineClosedUnit

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
def initialExponentSet (V : Submodule ℂ (Exponent → ℂ)) (t : ℝ) : Set Exponent :=
  {e | ∃ c ∈ V, LexInitial c t e}

end MaximalSeshadri.Interpolation

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.ExtCokernel
noncomputable section
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

end
end MaximalSeshadri.ExtCokernel

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpenMap_comp {U V W : Opens X} (h : U ⟶ V) (g : V ⟶ W) :
    freeOpenMap R h ≫ freeOpenMap R g = freeOpenMap R (h ≫ g) := by
  exact ((freeOpenFunctor R).map_comp h g).symm

end
end MaximalSeshadri.ModuleMayerVietoris

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance surfaceCechLinear : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) :=
  sheafLinear X
local instance surfaceCechHasExt : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

local instance surfaceCechFreeHomGroup (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance surfaceCechFreeHomModule (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _

def tripleOpen (U V W : X.Opens) : X.Opens := (U ⊓ W) ⊓ (V ⊓ W)

end
end MaximalSeshadri.Geometry

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
open AlgebraicJets FormalCoordinates LocalComparison NodalLocal IsLocalRing
open scoped Topology

variable {R : Type*} [CommRing R] [Algebra ℂ R]

def bivariateTaylor (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) : R →ₐ[ℂ] Bivariate ℂ :=
  analyticFormal.comp (analyticPullback q hq)

end
end MaximalSeshadri.AnalyticCoordinates
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

variable {X Y Z : Scheme.{0}}

def moduleIsoSections {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections N U where
  toFun := e.hom.val.app (op U)
  invFun := e.inv.val.app (op U)
  left_inv m := by
    have h := congrArg (fun f : M ⟶ M => f.val.app (op U) m) e.hom_inv_id
    exact h
  right_inv m := by
    have h := congrArg (fun f : N ⟶ N => f.val.app (op U) m) e.inv_hom_id
    exact h
  map_add' := map_add _
  map_smul' r m := (e.hom.val.app (op U)).hom.map_smul (restrictScalar X U r) m

def openImmersionTop (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections (M.restrict f) ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (restrictedOpenSections M f ⊤).symm.toLinearMap ∘ₗ
    openRestriction M (show f ''ᵁ ⊤ ≤ ⊤ from le_top)

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

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [Field K] {X : Scheme.{0}}

def tripleBaseImage (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V W : X.Opens) :
    Submodule K (Sections k M (tripleOpen U V W)) :=
  ((res k M (show tripleOpen U V W ≤ U ⊓ W from inf_le_left)).range ⊔
   (res k M (show tripleOpen U V W ≤ V ⊓ W from inf_le_right)).range) ⊔
   (res k M (show tripleOpen U V W ≤ U ⊓ V from
      inf_le_inf inf_le_left inf_le_left)).range

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpen_hom_ext {A B Q : Opens X} (hA : A ≤ Q) (hB : B ≤ Q) (h : A ⊔ B = Q)
    {N : SheafOfModules R} {f g : freeOpen R Q ⟶ N}
    (ha : freeOpenMap R (homOfLE hA) ≫ f = freeOpenMap R (homOfLE hA) ≫ g)
    (hb : freeOpenMap R (homOfLE hB) ≫ f = freeOpenMap R (homOfLE hB) ≫ g) : f = g := by
  subst Q
  apply CategoryTheory.IsPushout.hom_ext (freeOpen_isPushout R A B) ha hb

end
end MaximalSeshadri.ModuleMayerVietoris

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.SpecMaps
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

def coordinate (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

@[simp] lemma coordinate_comp (f : X ⟶ Y) (g : Y ⟶ Spec R) :
    coordinate (f ≫ g) = coordinate g ≫ f.appTop := by
  simp [coordinate]

@[simp] lemma coordinate_spec (f : R ⟶ S) : coordinate (Spec.map f) = f ≫ (Scheme.ΓSpecIso S).inv := by
  simp [coordinate]

@[simp] lemma coordinate_comp_spec (f : X ⟶ Spec S) (g : R ⟶ S) :
    coordinate (f ≫ Spec.map g) = g ≫ coordinate f := by
  simp [coordinate]

end
end MaximalSeshadri.SpecMaps

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open SpecMaps
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

end
end MaximalSeshadri.ReesGrading

namespace MaximalSeshadri.SchematicExt
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {W X Y Z : Scheme.{u}}

end
end MaximalSeshadri.SchematicExt

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open SpecMaps
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

end
end MaximalSeshadri.ReesGrading

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

def chartModuleEquiv (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections (M.restrict f) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let E := moduleIsoSections e ⊤
  exact { E.toEquiv with
    map_add' := E.map_add
    map_smul' := fun r m => E.map_smul (f.appTop r) m }

def chartModuleMap (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (chartModuleEquiv M f e).toLinearMap ∘ₗ openImmersionTop M f

namespace BaseSections
variable {K : Type} [CommRing K]

def chartMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) :
    Sections kX M ⊤ →ₗ[K] Sections kY N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  refine { toFun := chartModuleMap M f e
           map_add' := (chartModuleMap M f e).map_add
           map_smul' := ?_ }
  intro r m
  have h := (chartModuleMap M f e).map_smul (kX r) m
  change _ = (f.appTop (kX r)) • (chartModuleMap M f e m) at h
  exact h.trans (congrArg (fun c : Γ(Y,⊤) => c • chartModuleMap M f e m)
    (RingHom.congr_fun hk r))

end BaseSections
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

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev tripleVertices (U V W : Opens X) := freeOpen R U ⊞ (freeOpen R V ⊞ freeOpen R W)
abbrev triplePairs (U V W : Opens X) := freeOpen R (U ⊓ V) ⊞ (freeOpen R (U ⊓ W) ⊞ freeOpen R (V ⊓ W))
def tripleD (U V W : Opens X) : triplePairs R U V W ⟶ tripleVertices R U V W :=
  biprod.desc
    (freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl -
      freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inl ≫ biprod.inr)
    (biprod.desc
      (-freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl +
        freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inr ≫ biprod.inr)
      (freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl ≫ biprod.inr -
        freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inr ≫ biprod.inr))
def tripleG (U V W : Opens X) : tripleVertices R U V W ⟶ freeOpen R ((U ⊔ V) ⊔ W) :=
  biprod.desc (freeOpenMap R (homOfLE (le_sup_left.trans le_sup_left)))
    (biprod.desc (freeOpenMap R (homOfLE (le_sup_right.trans le_sup_left)))
      (freeOpenMap R (homOfLE le_sup_right)))

lemma tripleDG (U V W : Opens X) : tripleD R U V W ≫ tripleG R U V W = 0 := by
  apply biprod.hom_ext'
  · simp [tripleD,tripleG,Preadditive.sub_comp,Category.assoc,freeOpenMap_comp]
  · apply biprod.hom_ext' <;>
      simp [tripleD,tripleG,Preadditive.sub_comp,Preadditive.add_comp,Preadditive.neg_comp,
        Category.assoc,freeOpenMap_comp]

instance tripleG_epi (U V W : Opens X) : Epi (tripleG R U V W) := by
  constructor
  intro N f g h
  apply freeOpen_hom_ext R (A := U ⊔ V) (B := W) le_sup_left le_sup_right rfl
  · apply freeOpen_hom_ext R (A := U) (B := V) le_sup_left le_sup_right rfl
    · have hh := congrArg (fun z => biprod.inl ≫ z) h
      simp only [← Category.assoc,freeOpenMap_comp]
      simpa [tripleG,Category.assoc] using hh
    · have hh := congrArg (fun z => biprod.inl ≫ biprod.inr ≫ z) h
      simp only [← Category.assoc,freeOpenMap_comp]
      simpa [tripleG,Category.assoc] using hh
  · have hh := congrArg (fun z => biprod.inr ≫ biprod.inr ≫ z) h
    simpa [tripleG,Category.assoc] using hh

abbrev tripleRelations (U V W : Opens X) := kernel (tripleG R U V W)
def tripleToRelations (U V W : Opens X) : triplePairs R U V W ⟶ tripleRelations R U V W :=
  kernel.lift (tripleG R U V W) (tripleD R U V W) (tripleDG R U V W)

lemma tripleToRelations_cycle {U V W T : Opens X} (hU : T ≤ U) (hV : T ≤ V) (hW : T ≤ W) :
    freeOpenMap R (homOfLE (le_inf hU hV)) ≫ biprod.inl ≫ tripleToRelations R U V W +
    freeOpenMap R (homOfLE (le_inf hU hW)) ≫ biprod.inl ≫ biprod.inr ≫ tripleToRelations R U V W +
    freeOpenMap R (homOfLE (le_inf hV hW)) ≫ biprod.inr ≫ biprod.inr ≫ tripleToRelations R U V W = 0 := by
  apply (cancel_mono (kernel.ι (tripleG R U V W))).mp
  simp only [Preadditive.add_comp,Category.assoc,tripleToRelations,kernel.lift_ι,Limits.zero_comp]
  apply biprod.hom_ext
  · simp [tripleD,Category.assoc,Preadditive.comp_sub,Preadditive.comp_add,
      Preadditive.comp_neg,freeOpenMap_comp]
  · apply biprod.hom_ext <;> simp [tripleD,Category.assoc,Preadditive.comp_sub,
      Preadditive.comp_add,Preadditive.comp_neg,freeOpenMap_comp]

abbrev tripleKernelComplex (U V W : Opens X) :=
  ShortComplex.mk (kernel.ι (tripleG R U V W)) (tripleG R U V W) (kernel.condition _)
lemma tripleKernelComplex_shortExact (U V W : Opens X) :
    (tripleKernelComplex R U V W).ShortExact := by
  exact ⟨(tripleKernelComplex R U V W).exact_of_f_is_kernel (kernelIsKernel _)⟩

end
end MaximalSeshadri.ModuleMayerVietoris

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.UnitEndomorphism
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}
def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
variable (g : unit X ⟶ unit X)

end
end MaximalSeshadri.UnitEndomorphism
namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)

variable {I f}

def restrictedInclusion (j : Z ⟶ Y) [IsOpenImmersion j] :
    J.sheaf.restrict j ⟶ structureSheaf Z :=
  (Scheme.Modules.restrictFunctor j).map ι ≫ (Scheme.Modules.restrictUnitIso j).hom

instance restrictedInclusion_mono (j : Z ⟶ Y) [IsOpenImmersion j] [Mono ι] :
    Mono (restrictedInclusion J ι j) := by
  have : Mono (C := Z.Modules) ((Scheme.Modules.restrictFunctor j).map ι) := by
    apply (Scheme.Modules.toPresheafOfModules Z).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    let : Mono ι.val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map ι))
    exact PresheafOfModules.injective_of_mono ι.val (op (j ''ᵁ U.unop))
  let unitIso : (Scheme.Modules.restrictFunctor j).obj (structureSheaf Y) ≅
      structureSheaf Z := Scheme.Modules.restrictUnitIso j
  exact mono_comp (C := Z.Modules) ((Scheme.Modules.restrictFunctor j).map ι) unitIso.hom

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.ReesGrading
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry
open SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)

end
end MaximalSeshadri.ReesGrading

end

end OAI
end

section
namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

lemma homogeneous_eval₂_scale {R S σ : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (u : σ → S) (a : S) :
    eval₂ f (fun j => a * u j) p = a ^ n * eval₂ f u p := by
  classical
  rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd]
  ring

variable {R σ : Type*} [CommRing R] (i : σ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev PolyGrade (R σ : Type*) [CommRing R] := MvPolynomial.homogeneousSubmodule σ R
lemma poly_X_mem : X (R := R) i ∈ PolyGrade R σ 1 := isHomogeneous_X R i

abbrev PolyChart := HomogeneousLocalization.Away (PolyGrade R σ) (X i)
abbrev ChartVariables := {j : σ // j ≠ i}

def chartCoordinate (j : σ) : PolyChart (R := R) i :=
  Away.mk _ (poly_X_mem (R := R) i) 1 (X j) (by simpa using poly_X_mem (R := R) j)

def dehomogenize : MvPolynomial σ R →+* MvPolynomial (ChartVariables i) R :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp] lemma dehomogenize_X_self : dehomogenize (R := R) i (X i) = 1 := by
  classical
  simp [dehomogenize]

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] [Fintype σ]

def linearEquation (t : σ → R) : MvPolynomial σ R := ∑ i, C (t i) * X i

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R σ : Type u} [CommRing R] [Fintype σ]

omit [Fintype σ] in

def projectiveConstants : R →+* PolyGrade R σ 0 :=
  { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
    map_one' := Subtype.ext C_1
    map_mul' := fun _ _ => Subtype.ext C_mul
    map_zero' := Subtype.ext C_0
    map_add' := fun _ _ => Subtype.ext C_add }

omit [Fintype σ] in
def projectiveToSpec : Proj (PolyGrade R σ) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom projectiveConstants)

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveHyperplane {K : Type} [Field K] {n : ℕ} {X : Scheme}
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n)))) (t : Option (Fin n) → K) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n))) (linearEquation t)).compl

end
end MaximalSeshadri.BertiniIntegral

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

variable {K : Type} [CommRing K] {X : Scheme.{0}}

lemma congr_apply (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens}
    (h : U = V) (m : Sections k M U) :
    congr k M h m = M.presheaf.map (eqToHom h.symm).op m := by
  subst V
  change m = M.presheaf.map (𝟙 (op U)) m
  exact congrArg (fun f : M.presheaf.obj (op U) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_id (op U)).symm

def nestedRestriction (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    (M.restrict U.ι).restrict (X.homOfLE h) ≅ M.restrict W.ι :=
  ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M

lemma nestedBase (k : K →+* Γ(X,⊤)) {U W : X.Opens} (h : W ≤ U) :
    (X.homOfLE h).appTop.hom.comp (U.ι.appTop.hom.comp k) = W.ι.appTop.hom.comp k := by
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι]

lemma chartTop_nested (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartTop k M W (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k)
      (X.homOfLE h) (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h) m) =
        res k M h (chartTop k M U m) := by
  simp only [chartTop, LinearEquiv.trans_apply, restrictEquiv, congr_apply,
    chartMap, chartModuleMap, LinearMap.coe_comp,
    chartModuleEquiv, moduleIsoSections, openImmersionTop, restrictedOpenSections,
    nestedRestriction, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫
    M.presheaf.map _) m = (M.presheaf.map _ ≫ M.presheaf.map _) m
  simp only [← M.presheaf.map_comp]
  apply congrArg (fun morphism :
    M.presheaf.obj (op (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) ⟶ M.presheaf.obj (op W) =>
      morphism m)
  exact (M.presheaf.map_comp _ _).symm.trans
    ((congrArg M.presheaf.map (Subsingleton.elim _ _)).trans
      (M.presheaf.map_comp _ _))

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

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

@[instance_reducible]
def laurentModule (k : K →+* Γ(Y,⊤)) (u v : Γ(Y,⊤)ˣ) (N : Y.Modules) :
    Module (LaurentPlane.Ring K) (Sections k N ⊤) :=
  Module.compHom (Sections k N ⊤) (LaurentPlane.eval k u v)

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance tripleExtLinear : Linear Γ(X,⊤) X.Modules := sheafLinear X
local instance tripleExtHasExt : HasExt.{1} X.Modules := schemeHasExt

def tripleHomExtEquiv [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ((complex.X₁ ⟶ M) ⧸ (Linear.leftComp Γ(X,⊤) M complex.f).range) ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) complex.X₃ M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  let exactness : complex.ShortExact :=
    tripleKernelComplex_shortExact (X := X.carrier) X.ringCatSheaf U V W
  refine ExtCokernel.quotientEquiv (C := X.Modules) (K := Γ(X,⊤))
    (S := complex) exactness M ?_
  change ∀ middleClass : Ext.{1} (C := X.Modules)
    (FiniteCoverCohomology.freeOpenModule U ⊞
      (FiniteCoverCohomology.freeOpenModule V ⊞ FiniteCoverCohomology.freeOpenModule W))
    M 1, middleClass = 0
  intro middleClass
  apply (Ext.biprodAddEquiv (C := X.Modules)).injective
  apply Prod.ext
  · simpa only [map_zero,Ext.biprodAddEquiv_apply_fst,Prod.fst_zero] using
       FiniteCoverCohomology.affine_open_ext_zero (X := X) U hU M 0
        ((Ext.mk₀ biprod.inl).comp middleClass (zero_add _))
  · have h (z : Ext.{1} (C := X.Modules)
        (FiniteCoverCohomology.freeOpenModule V ⊞ FiniteCoverCohomology.freeOpenModule W)
        M 1) : z = 0 := by
      apply (Ext.biprodAddEquiv (C := X.Modules)).injective
      apply Prod.ext
      · simpa only [map_zero,Ext.biprodAddEquiv_apply_fst,Prod.fst_zero] using
           FiniteCoverCohomology.affine_open_ext_zero (X := X) V hV M 0
            ((Ext.mk₀ biprod.inl).comp z (zero_add _))
      · simpa only [map_zero,Ext.biprodAddEquiv_apply_snd,Prod.snd_zero] using
           FiniteCoverCohomology.affine_open_ext_zero (X := X) W hW M 0
            ((Ext.mk₀ biprod.inr).comp z (zero_add _))
    simpa only [map_zero,Ext.biprodAddEquiv_apply_snd,Prod.snd_zero] using
      h ((Ext.mk₀ biprod.inr).comp middleClass (zero_add _))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.hom_ext (hπ : IsBlowup I π) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) {g h : Y ⟶ B}
    (hg : g ≫ π = f) (hh : h ≫ π = f) : g = h := by
  obtain ⟨l, _, hl⟩ := hπ.2 Y f hf
  exact (hl g hg).trans (hl h hh).symm

def IsBlowup.iso {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : B ≅ B' where
  hom := (hπ'.2 B π hπ.1).choose
  inv := (hπ.2 B' π' hπ'.1).choose
  hom_inv_id := by
    apply hπ.hom_ext π hπ.1
    · rw [Category.assoc, (hπ.2 B' π' hπ'.1).choose_spec.1]
      exact (hπ'.2 B π hπ.1).choose_spec.1
    · simp
  inv_hom_id := by
    apply hπ'.hom_ext π' hπ'.1
    · rw [Category.assoc, (hπ'.2 B π hπ.1).choose_spec.1]
      exact (hπ.2 B' π' hπ'.1).choose_spec.1
    · simp

@[reassoc (attr := simp)]
lemma IsBlowup.iso_hom_comp {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : (hπ.iso hπ').hom ≫ π' = π :=
  (hπ'.2 B π hπ.1).choose_spec.1

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B B' Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.AffineBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

abbrev scheme : Scheme := ReesGrading.affineBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)

def projection : scheme I ⟶ X :=
  ReesGrading.projection (I.ideal ⟨⊤, isAffineOpen_top X⟩) ≫ X.isoSpec.inv

end
end MaximalSeshadri.AffineBlowup

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
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {A R σ : Type u} [CommRing A] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  (f : A →+* R)

def evalAway (s : A) (hs : IsUnit (f s)) : Away 𝒜 s →+* R :=
  (IsLocalization.Away.lift s hs : Localization.Away s →+* R).comp
    (algebraMap (Away 𝒜 s) (Localization.Away s))

lemma evalAway_val (s : A) (hs : IsUnit (f s)) (x : Away 𝒜 s) :
    evalAway f s hs x = IsLocalization.Away.lift s hs x.val := rfl

lemma evalAway_transition {s t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hs : IsUnit (f s)) (hst : IsUnit (f (s * t))) :
    (evalAway f (s * t) hst).comp (awayMap 𝒜 ht rfl) = evalAway f s hs := by
  have hunit : IsUnit (algebraMap A (Localization.Away (s * t)) s) :=
    IsLocalization.Away.isUnit_of_dvd (s * t) (dvd_mul_right s t)
  have H : (IsLocalization.Away.lift (s * t) hst : Localization.Away (s * t) →+* R).comp
      (Localization.awayLift (algebraMap A (Localization.Away (s * t))) s hunit) =
      (IsLocalization.Away.lift s hs : Localization.Away s →+* R) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  apply RingHom.ext
  intro x
  simpa only [RingHom.comp_apply, evalAway_val, val_awayMap] using RingHom.congr_fun H x.val

lemma evalAway_natural {T : Type u} [CommRing T] (g : R →+* T)
    (s : A) (hs : IsUnit (f s)) :
    g.comp (evalAway (𝒜 := 𝒜) f s hs) = evalAway (g.comp f) s (hs.map g) := by
  have H : g.comp (IsLocalization.Away.lift s hs : Localization.Away s →+* R) =
      (IsLocalization.Away.lift (g := g.comp f) s (hs.map g) : Localization.Away s →+* T) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  exact congrArg (fun h : Localization.Away s →+* T =>
    h.comp (algebraMap (Away 𝒜 s) (Localization.Away s))) H

lemma evalAway_mk_clear {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n = f a := by
  rw [evalAway_val, Away.val_mk, Localization.mk_eq_mk']
  have H := IsLocalization.mk'_spec (Localization.Away s) a
    (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s)
  apply_fun (IsLocalization.Away.lift s hu : Localization.Away s →+* R) at H
  simpa only [map_mul, IsLocalization.Away.lift_eq, map_pow] using H

lemma evalAway_scale {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (g : A →+* R) (hv : IsUnit (g s)) (c : Rˣ)
    (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    evalAway (𝒜 := 𝒜) f s hu = evalAway g s hv := by
  apply RingHom.ext
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  apply (hv.pow n).mul_right_cancel
  have Hf := evalAway_mk_clear f hs hu n a ha
  have Hg := evalAway_mk_clear g hs hv n a ha
  rw [Hg, hscale d s hs, hscale _ a ha, mul_pow, ← pow_mul]
  rw [smul_eq_mul, Nat.mul_comm n d]
  calc
    _ = (c : R) ^ (d * n) * (evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n) := by ring
    _ = _ := by rw [Hf]

def fromUnitCoordinate {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d)
    (hu : IsUnit (f s)) : Spec (CommRingCat.of R) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (evalAway f s hu)) ≫ Proj.awayι 𝒜 s hs hd

lemma fromUnitCoordinate_mul {s t : A} {d e : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s))
    (hut : IsUnit (f (s * t))) :
    fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate f (Nat.add_pos_left hd e) (SetLike.mul_mem_graded hs ht) hut := by
  unfold fromUnitCoordinate
  rw [← Proj.SpecMap_awayMap_awayι 𝒜 hs hd ht rfl, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_transition f ht hu hut]

@[reassoc]
lemma fromUnitCoordinate_natural {T : Type u} [CommRing T] (g : R →+* T)
    {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) :
    Spec.map (CommRingCat.ofHom g) ≫ fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate (g.comp f) hd hs (hu.map g) := by
  unfold fromUnitCoordinate
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_natural]

lemma fromUnitCoordinate_scale {s : A} {d : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) (g : A →+* R) (hv : IsUnit (g s))
    (c : Rˣ) (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate g hd hs hv := by
  unfold fromUnitCoordinate
  rw [evalAway_scale f hs hu g hv c hscale]

theorem fromUnitCoordinate_eq {s t : A} {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s)) (hv : IsUnit (f t)) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate f he ht hv := by
  have huv : IsUnit (f (s * t)) := by rw [map_mul]; exact hu.mul hv
  have hvu : IsUnit (f (t * s)) := by rw [map_mul]; exact hv.mul hu
  rw [fromUnitCoordinate_mul f hd hs ht hu huv,
    fromUnitCoordinate_mul f he ht hs hv hvu]
  congr 1 <;> ac_rfl

open MvPolynomial

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinates_X_mem (i : σ) : MvPolynomial.X i ∈ homogeneousSubmodule σ K 1 :=
  isHomogeneous_X K i

def coordinatesMap (X : Scheme.{u}) (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤))
    (i : σ) (hi : a i = 1) : X ⟶ Proj (homogeneousSubmodule σ K) :=
  X.toSpecΓ ≫ fromUnitCoordinate (eval₂Hom k a) (by decide)
    (coordinates_X_mem (K := K) i) (by simpa only [eval₂Hom_X', hi] using isUnit_one)

lemma coordinates_eval_natural {R T : Type u} [CommRing R] [CommRing T]
    (g : R →+* T) (k : K →+* R) (a : σ → R) :
    g.comp (eval₂Hom k a) = eval₂Hom (g.comp k) (fun j => g (a j)) := by
  apply MvPolynomial.ringHom_ext <;> intro j <;> simp

@[reassoc]
lemma coordinatesMap_natural {X Y : Scheme.{u}} (φ : Y ⟶ X)
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    φ ≫ coordinatesMap X k a i hi =
      coordinatesMap Y (φ.appTop.hom.comp k) (fun j => φ.appTop (a j)) i
        (by simp only [hi, map_one]) := by
  unfold coordinatesMap
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ]
  congr 1
  change Spec.map (CommRingCat.ofHom φ.appTop.hom) ≫ _ = _
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural φ.appTop.hom k a

lemma coordinatesMap_scale (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a b : σ → Γ(X, ⊤)) (i j : σ) (hi : a i = 1) (hj : b j = 1)
    (c : Γ(X, ⊤)ˣ) (hscale : ∀ q, b q = (c : Γ(X, ⊤)) * a q) :
    coordinatesMap X k a i hi = coordinatesMap X k b j hj := by
  let f := eval₂Hom k a
  let g := eval₂Hom k b
  have hf : IsUnit (f (MvPolynomial.X (R := K) i)) := by
    simpa only [f, eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have hg : IsUnit (g (MvPolynomial.X (R := K) i)) := by
    simpa only [g, eval₂Hom_X', hscale i, hi, mul_one] using c.isUnit
  have hg' : IsUnit (g (MvPolynomial.X (R := K) j)) := by
    simpa only [g, eval₂Hom_X', hj] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have H : ∀ n p, p ∈ homogeneousSubmodule σ K n →
      g p = (c : Γ(X, ⊤)) ^ n * f p := by
    intro n p hp
    change eval₂ k b p = _
    have hb : b = fun q => (c : Γ(X, ⊤)) * a q := funext hscale
    rw [hb]
    exact homogeneous_eval₂_scale hp k a c
  unfold coordinatesMap
  congr 1
  exact (fromUnitCoordinate_scale (𝒜 := homogeneousSubmodule σ K) (d := 1) f (by decide) (coordinates_X_mem (K := K) i)
    hf g hg c H).trans
      (fromUnitCoordinate_eq (𝒜 := homogeneousSubmodule σ K) (d := 1) (e := 1) g (by decide) (by decide)
        (coordinates_X_mem (K := K) i) (coordinates_X_mem (K := K) j) hg hg')

structure CoordinateAtlas (X : Scheme.{u}) where
  cover : X.OpenCover
  scalars : ∀ i : cover.I₀, K →+* Γ(cover.X i, ⊤)
  coordinates : ∀ i : cover.I₀, σ → Γ(cover.X i, ⊤)
  index : cover.I₀ → σ
  normalized : ∀ i, coordinates i (index i) = 1
  scalarOverlap : ∀ i j,
    (pullback.fst (cover.f i) (cover.f j)).appTop.hom.comp (scalars i) =
      (pullback.snd (cover.f i) (cover.f j)).appTop.hom.comp (scalars j)
  coordinateOverlap : ∀ i j,
    ∃ c : Γ(pullback (cover.f i) (cover.f j), ⊤)ˣ, ∀ q,
      (pullback.snd (cover.f i) (cover.f j)).appTop (coordinates j q) =
        (c : Γ(pullback (cover.f i) (cover.f j), ⊤)) *
          (pullback.fst (cover.f i) (cover.f j)).appTop (coordinates i q)

variable {X : Scheme.{u}} (D : CoordinateAtlas (K := K) (σ := σ) X)

def CoordinateAtlas.localMap (i : D.cover.I₀) :
    D.cover.X i ⟶ Proj (homogeneousSubmodule σ K) :=
  coordinatesMap _ (D.scalars i) (D.coordinates i) (D.index i) (D.normalized i)

lemma CoordinateAtlas.compatible (i j : D.cover.I₀) :
    pullback.fst (D.cover.f i) (D.cover.f j) ≫ D.localMap i =
      pullback.snd (D.cover.f i) (D.cover.f j) ≫ D.localMap j := by
  unfold CoordinateAtlas.localMap
  rw [coordinatesMap_natural, coordinatesMap_natural]
  obtain ⟨c, hc⟩ := D.coordinateOverlap i j
  simpa only [D.scalarOverlap i j] using
    coordinatesMap_scale _
      ((pullback.fst (D.cover.f i) (D.cover.f j)).appTop.hom.comp (D.scalars i))
      _ _ (D.index i) (D.index j)
      (by simp only [D.normalized, map_one])
      (by simp only [D.normalized, map_one]) c hc

def CoordinateAtlas.morphism : X ⟶ Proj (homogeneousSubmodule σ K) :=
  D.cover.glueMorphisms D.localMap D.compatible

@[reassoc, simp]
lemma CoordinateAtlas.cover_morphism (i : D.cover.I₀) :
    D.cover.f i ≫ D.morphism = D.localMap i :=
  D.cover.ι_glueMorphisms _ _ i

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

def atlasOfFramedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (𝒰 : X.OpenCover)
    (e : ∀ i, M.restrict (𝒰.f i) ≅ O (𝒰.X i)) (index : 𝒰.I₀ → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (𝒰.f i) (s (index i))) = 1) :
    CoordinateAtlas (K := K) (σ := σ) X where
  cover := 𝒰
  scalars i := (𝒰.f i).appTop.hom.comp k
  coordinates i q := coefficient (e i) (restrictSection (𝒰.f i) (s q))
  index := index
  normalized := hnorm
  scalarOverlap i j := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun f : pullback (𝒰.f i) (𝒰.f j) ⟶ X => f.appTop.hom)
        (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j))
  coordinateOverlap i j := by
    obtain ⟨c, hc⟩ := overlap_coefficients (𝒰.f i) (𝒰.f j)
      (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)) (e i) (e j)
    exact ⟨c, fun q => hc (s q)⟩

def sectionFrame {M : X.Modules} (s : O X ⟶ M) :
    M.restrict (SectionOpens.isoOpen s).ι ≅ O (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact (asIso ((Scheme.Modules.restrictFunctor (SectionOpens.isoOpen s).ι).map s)).symm ≪≫
    Scheme.Modules.restrictUnitIso (SectionOpens.isoOpen s).ι

lemma sectionFrame_normalized {M : X.Modules} (s : O X ⟶ M) :
    coefficient (sectionFrame s) (restrictSection (SectionOpens.isoOpen s).ι s) = 1 := by
  exact coefficient_frame (sectionFrame s)

def sectionsMorphism {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s
    (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover)
    (fun i => sectionFrame (s i)) id (fun i => sectionFrame_normalized (s i))).morphism

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

end
end MaximalSeshadri.Projective

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

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} {R : Type} [CommRing R]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ]

def ambientHyperplane (t : σ → K) : (Proj (PolyGrade K σ)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Proj.basicOpen (PolyGrade K σ) (linearEquation t)).compl

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}
local instance tripleTopExtLinear : Linear Γ(X,⊤) X.Modules := sheafLinear X
local instance tripleTopExtHasExt : HasExt.{1} X.Modules := schemeHasExt

def tripleTopHomExtEquiv [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ((complex.X₁ ⟶ M) ⧸ (Linear.leftComp Γ(X,⊤) M complex.f).range) ≃ₗ[Γ(X,⊤)]
      cohomology M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  let topIso : complex.X₃ ≅ structureSheaf X :=
    eqToIso (congrArg (FiniteCoverCohomology.freeOpenModule (X := X)) hc) ≪≫
      FreeOpenUnit.freeTopIso X.ringCatSheaf
  exact (tripleHomExtEquiv (X := X) M U V W hU hV hW).trans
    (extSourceIso (X := X) topIso M 1)

def tripleTopHomCohomologyOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    (complex.X₁ ⟶ M) →ₗ[Γ(X,⊤)] cohomology M 1 := by
  let complex : ShortComplex X.Modules :=
    tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
  exact (tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc).toLinearMap.comp
    (Linear.leftComp Γ(X,⊤) M complex.f).range.mkQ

lemma tripleTopHomCohomologyOne_zero [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    let complex : ShortComplex X.Modules :=
      tripleKernelComplex (X := X.carrier) X.ringCatSheaf U V W
    ∀ (x : complex.X₁ ⟶ M),
      x ∈ (Linear.leftComp Γ(X,⊤) M complex.f).range →
      tripleTopHomCohomologyOne M U V W hU hV hW hc x = 0 := by
  intro complex relation inRange
  let quotientEquiv := tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc
  have class_zero : (Linear.leftComp Γ(X,⊤) M complex.f).range.mkQ relation = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr inRange
  exact (congrArg quotientEquiv class_zero).trans quotientEquiv.map_zero
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.BlowupGluing
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

local instance localAffine (U : X.AffineZariskiSite) : IsAffine U.toOpens.toScheme := U.2

abbrev localCentre (U : X.AffineZariskiSite) : U.toOpens.toScheme.IdealSheafData := I.comap U.toOpens.ι

abbrev localScheme (U : X.AffineZariskiSite) : Scheme :=
  AffineBlowup.scheme (localCentre I U)

abbrev localProjection (U : X.AffineZariskiSite) : localScheme I U ⟶ U.toOpens.toScheme :=
  AffineBlowup.projection (localCentre I U)

end

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

end
end MaximalSeshadri.BlowupGluing

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry MaximalSeshadri.Geometry

variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.ReesGrading
noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

end
end MaximalSeshadri.ReesGrading

end

end OAI
end

section
namespace OAI

section
noncomputable section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

structure EtaleProjectiveChart (g : X ⟶ Spec (CommRingCat.of K))
    (h : X ⟶ Proj (PolyGrade K σ)) where
  U : X.affineOpens
  coord : σ
  nonempty : Nonempty U.1
  φ : PolyChart (R := K) coord →+* Γ(X, U.1)
  factor : Spec.map (CommRingCat.ofHom φ) ≫
    Proj.awayι (PolyGrade K σ) (MvPolynomial.X coord) (poly_X_mem coord) (by decide) =
      U.2.fromSpec ≫ h
  κ : Type
  finite : Finite κ
  a : κ → ChartVariables coord
  card : Nat.card κ = 2
  etale : (MvPolynomial.eval₂Hom (openScalars g U.1)
    (fun k => -φ (chartCoordinate coord (a k).1))).Etale

end
end MaximalSeshadri.ProjectiveBertini

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K σ : Type u} [CommRing K] [Fintype σ] {X : Scheme.{u}}

def sectionCombination {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (t : σ → K) : O X ⟶ M :=
  ∑ j, scalarEnd (k (t j)) ≫ s j

end
end MaximalSeshadri.Projective

end

end
end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading
variable (K : Type) [Field K]
abbrev PlaneRing := MvPolynomial (Fin 2) K
abbrev originIdeal : Ideal (PlaneRing K) := MvPolynomial.idealOfVars (Fin 2) K

def coordinate (i : Fin 2) : originIdeal K :=
  ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩

def chartSubstitution (i : Fin 2) : PlaneRing K →+* PlaneRing K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if j = i then X i else X i * X j)

@[simp] lemma substitution_C (i : Fin 2) (c : K) : chartSubstitution K i (C c) = C c := by
  simp [chartSubstitution]

@[simp] lemma substitution_self (i : Fin 2) : chartSubstitution K i (X i) = X i := by
  simp [chartSubstitution]

@[simp] lemma substitution_other (i j : Fin 2) (h : j ≠ i) :
    chartSubstitution K i (X j) = X i * X j := by
  simp [chartSubstitution, h]

def fromPolynomial (i : Fin 2) : PlaneRing K →+* chart (originIdeal K) (coordinate K i) :=
  MvPolynomial.eval₂Hom
    ((chartBase (originIdeal K) (coordinate K i)).comp MvPolynomial.C)
    (fun j => if j = i then chartBase (originIdeal K) (coordinate K i) (X i)
      else ratio (originIdeal K) (coordinate K i) (coordinate K j))

@[simp] lemma fromPolynomial_C (i : Fin 2) (c : K) :
    fromPolynomial K i (C c) = chartBase (originIdeal K) (coordinate K i) (C c) := by
  simp [fromPolynomial]

@[simp] lemma fromPolynomial_self (i : Fin 2) :
    fromPolynomial K i (X i) = chartBase (originIdeal K) (coordinate K i) (X i) := by
  simp [fromPolynomial]

@[simp] lemma fromPolynomial_other (i j : Fin 2) (h : j ≠ i) :
    fromPolynomial K i (X j) = ratio (originIdeal K) (coordinate K i) (coordinate K j) := by
  simp [fromPolynomial, h]

end

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial ReesGrading
variable (K : Type) [Field K]

def structureMap : affineBlowup (originIdeal K) ⟶ Spec (.of K) :=
  projection (originIdeal K) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReesGrading MaximalSeshadri.Geometry
variable (K : Type) [Field K]

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry MaximalSeshadri.AlgebraicJets
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

end
end MaximalSeshadri.PointBlowup

end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

def sectionFrameOn {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) : M.restrict U.ι ≅ O U.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hU).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hU) (SectionOpens.isoOpen s).ι).app M ≪≫
      restrictFrame (X.homOfLE hU) (sectionFrame s)

lemma sectionFrameOn_coefficient {M : X.Modules} (s t : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) :
    coefficient (sectionFrameOn s U hU) (restrictSection U.ι t) =
      (X.homOfLE hU).appTop (coefficient (sectionFrame s)
        (restrictSection (SectionOpens.isoOpen s).ι t)) := by
  unfold sectionFrameOn
  rw [coefficient_transport]
  change coefficient
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE hU) (SectionOpens.isoOpen s).ι).app M ≪≫
      restrictFrame (X.homOfLE hU) (sectionFrame s))
    (restrictSection U.ι t ≫ (Scheme.Modules.restrictFunctorCongr
      (X.homOfLE_ι hU).symm).hom.app M) = _
  rw [restrictSection_congr, coefficient_restrict_comp]

lemma sectionFrameOn_normalized {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : U ≤ SectionOpens.isoOpen s) :
    coefficient (sectionFrameOn s U hU) (restrictSection U.ι s) = 1 := by
  rw [sectionFrameOn_coefficient, sectionFrame_normalized, map_one]

end
end MaximalSeshadri.Projective
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
open AlgebraicGeometry CategoryTheory
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme}

def quarticSection {M : X.Modules} (a b c d : O X ⟶ M) :
    O X ⟶ modulePow X M 4 := mixedPowerSection 4 ![a,b,c,d]

lemma quarticSection_pure {M : X.Modules} (a : O X ⟶ M) :
    quarticSection a a a a = powerSection a 4 := by
  apply (congrArg (mixedPowerSection 4) (show ![a,a,a,a] = fun _ => a from by
    funext i; fin_cases i <;> rfl)).trans
  exact mixedPowerSection_const 4 a

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

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {σ : Type} {X : Scheme.{0}} {M : X.Modules}

def ratioOn (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : Γ(U.toScheme,⊤) :=
  coefficient (sectionFrameOn (s i) U hi) (restrictSection U.ι (s j))

@[simp] lemma ratioOn_self (s : σ → (O X ⟶ M)) (i : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) : ratioOn s i i U hi = 1 :=
  sectionFrameOn_normalized (s i) U hi

def ratioUnitOn (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    Γ(U.toScheme,⊤)ˣ :=
  frameChange (sectionFrameOn (s j) U hj) (sectionFrameOn (s i) U hi)

end
end MaximalSeshadri.Projective

end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

def sectionIdeal {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) : X.IdealSheafData :=
  (ambientHyperplane v).comap (sectionsMorphism k s hs)

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.LaurentPlane MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planeTriple (s : Fin 3 → (O X ⟶ M)) : X.Opens :=
  tripleOpen (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
    (SectionOpens.isoOpen (s 0))

lemma planeTriple_le (s : Fin 3 → (O X ⟶ M)) (i : Fin 3) :
    planeTriple s ≤ SectionOpens.isoOpen (s i) := by
  fin_cases i
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_right.trans inf_le_left

def planeX (s : Fin 3 → (O X ⟶ M)) : Γ((planeTriple s).toScheme,⊤)ˣ :=
  ratioUnitOn s 0 1 (planeTriple s) (planeTriple_le s 0) (planeTriple_le s 1)

def planeY (s : Fin 3 → (O X ⟶ M)) : Γ((planeTriple s).toScheme,⊤)ˣ :=
  ratioUnitOn s 0 2 (planeTriple s) (planeTriple_le s 0) (planeTriple_le s 2)

end
end MaximalSeshadri.Projective

end

end OAI
end

section
namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}

variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

def pointCentre : X.IdealSheafData := ∏ i, (p i).ker

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)

include hp

variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hd

end
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))
variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hp hd

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))
variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

end
end MaximalSeshadri.FinitePointBlowup
namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme}

end
end MaximalSeshadri.IdealPullback
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))

variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

end
end MaximalSeshadri.FinitePointBlowup

end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] {X : Scheme}

abbrev QuarticIndex (σ : Type) := σ × σ × Option σ × Option σ

def doublePointQuartics {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (j : QuarticIndex σ) : O X ⟶ modulePow X M 4 :=
  quarticSection (s (some j.1)) (s (some j.2.1)) (s j.2.2.1) (s j.2.2.2)

lemma doublePointQuartics_pure {M : X.Modules} (s : Option σ → (O X ⟶ M)) (i : σ) :
    doublePointQuartics s (i,i,some i,some i) = powerSection (s (some i)) 4 :=
  quarticSection_pure _

def centeredOpen {M : X.Modules} (s : Option σ → (O X ⟶ M)) : X.Opens :=
  ⨆ i : σ, SectionOpens.isoOpen (s (some i))

lemma restricted_centered_cover {M : X.Modules} (s : Option σ → (O X ⟶ M)) :
    (⨆ i : σ, SectionOpens.isoOpen (restrictSection (centeredOpen s).ι (s (some i)))) = ⊤ := by
  simp_rw [isoOpen_restrictSection]
  rw [← Scheme.Hom.preimage_iSup]
  exact Scheme.Opens.ι_preimage_self _

lemma doublePointQuartics_cover {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i : σ, SectionOpens.isoOpen (s (some i))) = ⊤) :
    (⨆ j, SectionOpens.isoOpen (doublePointQuartics s j)) = ⊤ := by
  apply top_unique
  rw [← hs]
  apply iSup_le
  intro i
  calc
    SectionOpens.isoOpen (s (some i)) ≤ SectionOpens.isoOpen (powerSection (s (some i)) 4) := sectionOpen_le_powerSection _ _
    _ = SectionOpens.isoOpen (doublePointQuartics s (i,i,some i,some i)) := by
      exact congrArg SectionOpens.isoOpen (doublePointQuartics_pure s i).symm
    _ ≤ (⨆ j : QuarticIndex σ, SectionOpens.isoOpen (doublePointQuartics s j)) :=
      le_iSup (fun j : QuarticIndex σ => SectionOpens.isoOpen (doublePointQuartics s j)) (i,i,some i,some i)

end
end MaximalSeshadri.Projective

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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

lemma BaseSections.res_comp (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V W : X.Opens} (h : U ≤ V) (g : V ≤ W) (m : Sections k M W) :
    res k M h (res k M g m) = res k M (h.trans g) m := by
  exact congrArg (fun morphism : M.presheaf.obj (op W) ⟶ M.presheaf.obj (op U) =>
    morphism m) (M.presheaf.map_comp (homOfLE g).op (homOfLE h).op).symm

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

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.Projective

variable {K A σ : Type} [Field K] [CommRing A] [Algebra K A] [Fintype σ]

def exponent20 : Fin 2 →₀ ℕ := Finsupp.single 0 2
def exponent11 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
def exponent02 : Fin 2 →₀ ℕ := Finsupp.single 1 2

lemma degree20 : exponent20.degree < 3 := by simp [exponent20]
lemma degree11 : exponent11.degree < 3 := by simp [exponent11]
lemma degree02 : exponent02.degree < 3 := by simp [exponent02]

def jet20 : JetAlgebra (Fin 2) K 3 →ₗ[K] K :=
  (LinearMap.proj ⟨exponent20, degree20⟩).comp (polynomialJetEquiv 3).toLinearMap
def jet11 : JetAlgebra (Fin 2) K 3 →ₗ[K] K :=
  (LinearMap.proj ⟨exponent11, degree11⟩).comp (polynomialJetEquiv 3).toLinearMap
def jet02 : JetAlgebra (Fin 2) K 3 →ₗ[K] K :=
  (LinearMap.proj ⟨exponent02, degree02⟩).comp (polynomialJetEquiv 3).toLinearMap

def discriminant (f : JetAlgebra (Fin 2) K 3) : K :=
  jet11 f ^ 2 - 4 * jet20 f * jet02 f

end
end MaximalSeshadri.QuadraticJets

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

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ τ : Type} [CommRing K] {X : Scheme}

lemma sections_cover_reindex {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (e : τ ≃ σ) :
    (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤ := by
  apply le_antisymm le_top
  rw [← hs]
  refine iSup_le (fun i => ?_)
  obtain ⟨j, rfl⟩ := e.surjective i
  exact le_iSup (fun j : τ => SectionOpens.isoOpen (s (e j))) j

end
end MaximalSeshadri.Projective

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

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.IdealPullback
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

def augmentedQuartics {M : X.Modules} (s : Option σ → (O X ⟶ M)) :
    Option (QuarticIndex σ) → (O X ⟶ modulePow X M 4)
  | none => powerSection (s none) 4
  | some j => doublePointQuartics s j

omit [Fintype σ] in
lemma augmentedQuartics_cover {M : X.Modules} (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    (⨆ j, SectionOpens.isoOpen (augmentedQuartics s j)) = ⊤ := by
  apply top_unique
  rw [← hs]
  apply iSup_le
  intro i
  cases i with
  | none =>
    exact (sectionOpen_le_powerSection (s none) 4).trans
      (le_iSup (fun j => SectionOpens.isoOpen (augmentedQuartics s j)) none)
  | some i =>
    calc
      SectionOpens.isoOpen (s (some i)) ≤ SectionOpens.isoOpen (powerSection (s (some i)) 4) :=
        sectionOpen_le_powerSection _ _
      _ = SectionOpens.isoOpen (augmentedQuartics s (some (i,i,some i,some i))) := by
        exact congrArg SectionOpens.isoOpen (doublePointQuartics_pure s i).symm
      _ ≤ _ := le_iSup (fun j => SectionOpens.isoOpen (augmentedQuartics s j)) _

def doublePointQuarticIdeal {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : QuarticIndex σ → K) : X.IdealSheafData :=
  sectionIdeal k (augmentedQuartics s) (augmentedQuartics_cover s hs) (fun j => j.elim 0 v)

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X : Scheme.{0}}

abbrev chartRes (k : K →+* Γ(X,⊤)) (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :=
  chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
    (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planeVertex (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i : Fin 3) :=
  (chartRes k L.sheaf (planeTriple_le s i)).range

end
end MaximalSeshadri.Projective

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X

def BaseHom (_k : K →+* Γ(X,⊤)) (A B : X.Modules) := A ⟶ B
instance baseHomGroup (baseMap : K →+* Γ(X,⊤)) (source target : X.Modules) :
    AddCommGroup (BaseHom baseMap source target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance baseHomModule (k : K →+* Γ(X,⊤)) (A B : X.Modules) :
    Module K (BaseHom k A B) := Module.compHom (A ⟶ B) k

local instance (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _

local instance (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _

instance freeBaseHomGroup (baseMap : K →+* Γ(X,⊤)) (target : X.Modules)
    (chart : X.Opens) : AddCommGroup (BaseHom baseMap (freeOpen X.ringCatSheaf chart) target) :=
  baseHomGroup baseMap _ _

instance freeBaseHomModule (baseMap : K →+* Γ(X,⊤)) (target : X.Modules)
    (chart : X.Opens) : Module K (BaseHom baseMap (freeOpen X.ringCatSheaf chart) target) :=
  baseHomModule baseMap _ _

def freeBaseEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    BaseHom k (freeOpen X.ringCatSheaf U) M ≃ₗ[K] Sections k M U where
  toEquiv := (freeOpenLinearEquiv M U).toEquiv
  map_add' := (freeOpenLinearEquiv M U).map_add
  map_smul' r m := (freeOpenLinearEquiv M U).map_smul (k r) m

def homChart (k : K →+* Γ(X,⊤)) (M : X.Modules) {U T : X.Opens} (h : T ≤ U) :
    BaseHom k (freeOpen X.ringCatSheaf U) M →ₗ[K]
      Sections (T.ι.appTop.hom.comp k) (M.restrict T.ι) ⊤ :=
  (chartTop k M T).symm.toLinearMap.comp ((res k M h).comp (freeBaseEquiv k M U).toLinearMap)

lemma homChart_natural (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V T : X.Opens}
    (h : T ≤ V) (g : V ≤ U) (f : freeOpen X.ringCatSheaf U ⟶ M) :
    homChart k M h (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f) =
      homChart k M (h.trans g) f := by
  change (chartTop k M T).symm
      (res k M h (freeBaseEquiv k M V (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f))) =
    (chartTop k M T).symm (res k M (h.trans g) (freeBaseEquiv k M U f))
  apply congrArg (chartTop k M T).symm
  change res k M h (freeOpenLinearEquiv M V (freeOpenMap X.ringCatSheaf (homOfLE g) ≫ f)) = _
  rw [freeOpenLinearEquiv_naturality]
  exact res_comp k M h g _

lemma homChart_range (k : K →+* Γ(X,⊤)) (M : X.Modules) {U T : X.Opens} (h : T ≤ U) :
    (homChart k M h).range = (chartRes k M h).range := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    refine ⟨(chartTop k M U).symm (freeBaseEquiv k M U f),?_⟩
    apply (chartTop k M T).injective
    rw [chartTop_nested,LinearEquiv.apply_symm_apply]
    exact ((chartTop k M T).apply_symm_apply _).symm
  · rintro _ ⟨m,rfl⟩
    refine ⟨(freeBaseEquiv k M U).symm (chartTop k M U m),?_⟩
    apply (chartTop k M T).injective
    simp only [homChart,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    rw [chartTop_nested]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections MaximalSeshadri.Frames
open MaximalSeshadri.LaurentPlane MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

abbrev planePair (k : K →+* Γ(X,⊤)) (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) (i j : Fin 3) :=
  (chartRes k L.sheaf (le_inf (planeTriple_le s i) (planeTriple_le s j))).range

end
end MaximalSeshadri.Projective

end

end OAI
end


