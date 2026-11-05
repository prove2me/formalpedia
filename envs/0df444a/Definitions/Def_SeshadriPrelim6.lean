-- Prove2me | Definitions.Def_SeshadriPrelim6
-- name    : SeshadriPrelim6
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T15:02:49.88904+00:00
-- url     : https://prove2.me/theorems/28e58c56-a1f2-45aa-ae94-bc2e7a26905c
-- title:
--   Maximal Seshadri constants: supporting development, part 6
-- statement:
--   Part 6 of 6 of the supporting Lean development for the maximal Seshadri constants theorem. It holds the definitions that the statements of the published child theorems refer to, in source order, together with the proved lemmas that their bodies and type class instances rely on. No result is assumed: every lemma here has a proof. Source modules: `Cohomology.PlaneRelationCycles`, `Cohomology.SurfaceH1Finite`, `Divisors.SectionCoefficientOrder`, `Geometry.PlaneBoundaries`, `Intersection.SurfaceTwistEuler`, `Jets.CenteredJetChart`, `LocalAlgebra.PowerIdeal`, `LocalAlgebra.TwistedIdealPower`, `Nodal.NodalIdealDegree`, `Sheaves.TensorDivision`, `Sheaves.TensorInclusion`, `Sheaves.TensorPowerDistribution`.
--
--   **Formalization Note** Definitions of this development carry proof fields, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/AlgebraicGeometry/Seshadri` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim5

set_option linter.all false

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance planeRelationCyclesLinear : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) :=
  sheafLinear X
attribute [local instance] baseHomModule

def basePrecomp (k : K →+* Γ(X,⊤)) {A B : X.Modules} (M : X.Modules) (f : A ⟶ B) :
    BaseHom k B M →ₗ[K] BaseHom k A M where
  toFun g := f ≫ g
  map_add' := Preadditive.comp_add (C := X.Modules) _ _ _ f
  map_smul' r g := Linear.comp_smul _ _ _ f (k r) g

abbrev planeRelations {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) : X.Modules :=
  tripleRelations X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
abbrev planeVertices {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) : X.Modules :=
  tripleVertices X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
abbrev planeRelIota {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) :
    planeRelations s ⟶ planeVertices s :=
  kernel.ι (tripleG X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2)))
abbrev planeRelPi {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) :
    (show X.Modules from triplePairs X.ringCatSheaf (SectionOpens.isoOpen (s 0))
      (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))) ⟶ planeRelations s :=
  tripleToRelations X.ringCatSheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))

def relationA (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 0 1 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 0) (planeTriple_le s 1))).comp
    (basePrecomp k L.sheaf (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)
def relationB (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 0 2 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 0) (planeTriple_le s 2))).comp
    (basePrecomp k L.sheaf (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
      biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)
def relationC (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K] planePair k s L 1 2 :=
  ((homChart k L.sheaf (le_inf (planeTriple_le s 1) (planeTriple_le s 2))).comp
    (basePrecomp k L.sheaf (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
      biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s))).codRestrict _ (by
      intro f; change _ ∈ (chartRes k L.sheaf _).range; rw [← homChart_range]; exact ⟨_,rfl⟩)

def relationCycles (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X) :
    BaseHom k (planeRelations s) L.sheaf →ₗ[K]
      cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2) :=
  ((relationA k s L).prod ((relationB k s L).prod (relationC k s L))).codRestrict _ (by
    intro f
    let morphism : planeRelations s ⟶ L.sheaf := f
    have h := tripleToRelations_cycle X.ringCatSheaf (planeTriple_le s 0) (planeTriple_le s 1) (planeTriple_le s 2)
    let post : (freeOpen X.ringCatSheaf (planeTriple s) ⟶ planeRelations s) →+
        BaseHom k (freeOpen X.ringCatSheaf (planeTriple s)) L.sheaf :=
      { toFun := fun arrow => arrow ≫ morphism
        map_zero' := Limits.zero_comp
        map_add' := fun first second => Preadditive.add_comp _ _ _ first second morphism }
    let evaluate := (homChart k L.sheaf (le_rfl : planeTriple s ≤ planeTriple s)).toAddMonoidHom.comp post
    have evaluate_map {chart : X.Opens} (restriction : planeTriple s ≤ chart)
        (arrow : freeOpen X.ringCatSheaf chart ⟶ planeRelations s) :
        evaluate (freeOpenMap X.ringCatSheaf (homOfLE restriction) ≫ arrow) =
          homChart k L.sheaf restriction (arrow ≫ morphism) :=
      (congrArg (homChart k L.sheaf (le_rfl : planeTriple s ≤ planeTriple s))
        (Category.assoc _ _ _)).trans (homChart_natural k L.sheaf le_rfl restriction _)
    have he := congrArg evaluate h
    simp only [map_add, map_zero, evaluate_map] at he
    exact he)

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

section
variable {space : TopCat.{0}}
  (ringSheaf : Sheaf (Opens.grothendieckTopology space) RingCat.{0})
  (first second third : Opens space) {target : SheafOfModules ringSheaf}
  (morphism : tripleVertices ringSheaf first second third ⟶ target)

end

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance planeBoundariesLinear : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X
local instance planeBoundariesFreeHomGroup (target : X.Modules) (chart : X.Opens) :
    AddCommGroup (freeOpen X.ringCatSheaf chart ⟶ target) :=
  Preadditive.homGroup (C := SheafOfModules X.ringCatSheaf) _ _
attribute [local instance] baseHomModule
variable (k : K →+* Γ(X,⊤)) {M : X.Modules} (s : Fin 3 → (O X ⟶ M)) (L : LineBundle X)

abbrev relationBoundaries := (basePrecomp k L.sheaf (planeRelIota s)).range

end
end MaximalSeshadri.Geometry.BaseSections

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
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] {X : Scheme} {M : X.Modules}

def affineSectionRatios (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (j : Option σ) : Γ(X, U.1) :=
  U.1.topIso.hom (coefficient (sectionFrameOn (s none) U.1 hU)
    (restrictSection U.1.ι (s j)))

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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

def IntegralCurve.ofIdeal (S : Surface) (I : S.scheme.IdealSheafData)
    [IsIntegral I.subscheme] (hd : topologicalKrullDim I.subscheme = 1) : IntegralCurve S :=
  ⟨I.subscheme,I.subschemeι,inferInstance,inferInstance,hd⟩

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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

def frameOnSmaller {M : X.Modules} {U : X.Opens} (e : M.restrict U.ι ≅ O U.toScheme)
    (V : X.Opens) (h : V ≤ U) : M.restrict V.ι ≅ O V.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
  obtain ⟨A,hA,⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨B,hB,⟨f⟩⟩ := M.locallyRankOne x
  obtain ⟨_,⟨U,hUa,rfl⟩,hx,hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ A ⊓ B from ⟨hA,hB⟩)
      (A ⊓ B).isOpen
  exact ⟨⟨U,hUa⟩,hx,⟨frameOnSmaller e U (fun _ hy => (hU hy).1)⟩,
    ⟨frameOnSmaller f U (fun _ hy => (hU hy).2)⟩⟩

def LineBundle.tensor (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    exact ⟨U.1,hx,⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e f ≪≫ moduleTensorUnit (O U.1.toScheme)⟩⟩

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

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

def affineCoefficient {M : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) : Γ(X,U.1) :=
  U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))

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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X) :
    (J.tensor M).sheaf ⟶ M.sheaf :=
  moduleTensorMap ι (𝟙 M.sheaf) ≫ (moduleTensorUnit M.sheaf).hom

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
open AlgebraicGeometry CategoryTheory MonoidalCategory
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def moduleTensorComm (M N : X.Modules) : moduleTensor X M N ≅ moduleTensor X N M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

def lineTensorInterchange (A B C D : LineBundle X) :
    ((A.tensor B).tensor (C.tensor D)).sheaf ≅ ((A.tensor C).tensor (B.tensor D)).sheaf :=
  lineTensorAssoc A B (C.tensor D) ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (lineTensorAssoc B C D).symm ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (moduleTensorIso (moduleTensorComm B.sheaf C.sheaf) (Iso.refl D.sheaf)) ≪≫
  moduleTensorIso (Iso.refl A.sheaf) (lineTensorAssoc C B D) ≪≫
  (lineTensorAssoc A C (B.tensor D)).symm

def lineTensorPower (L M : LineBundle X) : ∀ n : ℕ,
    ((L.tensor M).pow n).sheaf ≅ ((L.pow n).tensor (M.pow n)).sheaf
  | 0 => (moduleTensorUnit (O X)).symm
  | n+1 => moduleTensorIso (Iso.refl _) (lineTensorPower L M n) ≪≫
    lineTensorInterchange L M (L.pow n) (M.pow n)

def lineTwistPower (L M : LineBundle X) (d n : ℕ) :
    (((L.pow d).tensor M).pow n).sheaf ≅ ((L.pow (d*n)).tensor (M.pow n)).sheaf :=
  lineTensorPower (L.pow d) M n ≪≫ moduleTensorIso (linePowerMul L d n) (Iso.refl _)

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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def idealPowerInclusion (J : LineBundle X) (ι : J.sheaf ⟶ O X) :
    ∀ n : ℕ, (J.pow n).sheaf ⟶ O X
  | 0 => 𝟙 _
  | n+1 => tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n

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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def twistIdealPowerIso (L J : LineBundle X) (a b n : ℕ) :
    (((L.pow a).tensor (J.pow b)).pow n).sheaf ≅
      ((J.pow (b*n)).tensor (L.pow (a*n))).sheaf :=
  lineTwistPower L (J.pow b) a n ≪≫
    moduleTensorIso (Iso.refl _) (linePowerMul J b n) ≪≫
      moduleTensorComm _ _

def twistedIdealPowerInclusion (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (a b n : ℕ) : (((L.pow a).tensor (J.pow b)).pow n).sheaf ⟶ (L.pow (a*n)).sheaf :=
  (twistIdealPowerIso L J a b n).hom ≫
    tensorInclusion (J.pow (b*n)) (L.pow (a*n)) (idealPowerInclusion J ι (b*n))

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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections ModuleFlasque ModuleMayerVietoris
open MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X
local instance : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt
attribute [local instance] baseHomModule

def planeBaseCohomologyOneMap [IsNoetherian X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i))) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    (BaseHom k (planeRelations s) L.sheaf ⧸ relationBoundaries k s L) →ₗ[K]
      cohomology L.sheaf 1 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology L.sheaf 1) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology L.sheaf 1) := .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (planeRelations s ⟶ L.sheaf) := Module.compHom (planeRelations s ⟶ L.sheaf) k
  letI : IsScalarTower K Γ(X,⊤) (planeRelations s ⟶ L.sheaf) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have hc : (SectionOpens.isoOpen (s 0) ⊔ SectionOpens.isoOpen (s 1)) ⊔
      SectionOpens.isoOpen (s 2) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs ▸ hx)
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  let F := (tripleTopHomCohomologyOne L.sheaf (SectionOpens.isoOpen (s 0))
    (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2)) (h 0) (h 1) (h 2) hc).restrictScalars K
  refine (relationBoundaries k s L).liftQ F ?_
  intro x hx
  exact tripleTopHomCohomologyOne_zero L.sheaf _ _ _ (h 0) (h 1) (h 2) hc x hx

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
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

def mixedEuler (S : Surface) (L M : LineBundle S.scheme) : ℤ :=
  eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf -
    eulerCharacteristic S.structureMap 2 L.sheaf -
    eulerCharacteristic S.structureMap 2 M.sheaf +
    eulerCharacteristic S.structureMap 2 (O S.scheme)

end
end MaximalSeshadri.Geometry

end

end OAI
end


