-- Prove2me | Definitions.Def_MaximalSeshadriConstants
-- name    : MaximalSeshadriConstants
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.94353+00:00
-- url     : https://prove2.me/theorems/7e11249a-ff9d-4018-b164-c5e170a64f0f
-- statement:
--   This block formalizes, over the complex numbers, the setup for the maximal Seshadri constant property of a line bundle on a smooth projective surface. Complex projective space P^N is Proj of the homogeneous polynomial ring in N+1 variables, with its structure map to Spec ℂ. A Surface is an integral scheme over ℂ, smooth of relative dimension 2, together with a closed immersion into some P^N compatible with the maps to Spec ℂ. A LineBundle on a scheme is a sheaf of modules that is locally isomorphic to the structure sheaf; the file builds tensor powers via sheafified tensor products, global sections, the open set where a section is invertible, and a definition of ampleness (every point and neighbourhood admit a power with a section whose nonvanishing locus is an affine open inside that neighbourhood containing the point). It equips Hom-sets of sheaf modules with a Γ(X,⊤)-linear structure. Sheaf cohomology is Ext from the structure sheaf, its ℂ-dimension is taken by finrank, and the Euler characteristic is the alternating sum up to a chosen dimension. The self-intersection L² of a line bundle on a surface is χ(L⊗²) − 2χ(L) + χ(O), and an IntegralCurve is a closed integral one-dimensional subscheme, whose degree against L is χ(L restricted to C) − χ(O_C). Complex points, r-tuples of points with the Zariski topology induced from the r-fold fibre product, and Configurations (tuples with pairwise distinct images) are defined. Multiplicity of a curve at a point is the order of the curve's ideal in the local ring, with total multiplicity summing over the r points. The Seshadri constant of L at a configuration p is the infimum of deg_L(C)/mult_p(C) over integral curves C with positive total multiplicity. The block also defines degrees of general modules on curves, the ideal image of a map from a line bundle into the structure sheaf, and when such a map presents the pullback of an ideal sheaf, invertibility of pullback ideals, the centre ideal as the product of the point ideals, IsBlowup as the universal scheme making the pullback ideal invertible, and a PointBlowup structure recording a blowup surface with exceptional line bundles pulling back the individual point ideals. BoundaryNef L says that for every integral curve C on the blowup, deg(π*L, C) + √(L²/r)·Σ deg(E_i, C) is nonnegative. Finally EventualMaximalSeshadri(S,L) is a defined proposition, not a proved theorem: there is r₀>0 such that for every r≥r₀ there is a countable family of proper Zariski-closed subsets Z_n of the configuration space, not covering it, such that every configuration outside all Z_n admits a point blowup with BoundaryNef and has Seshadri constant exactly √(L²/r). The definition does not itself require L to be ample.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MaximalSeshadriConstants.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MaximalSeshadriConstants.lean; bytes 16..18384
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Mathlib 4.33.1 uses the original namespace for this same tensor product.
noncomputable abbrev PresheafOfModulesOfCommRing.Monoidal.tensorObj :=
  @PresheafOfModules.Monoidal.tensorObj

namespace OAI



                                                                            
                                                                               
                                                                   
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

                                                                                    
def complexProjectiveSpace (N : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)

                                                                              
def constantsInDegreeZero (N : ℕ) :
    ℂ →+* (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0) :=
  { toFun := fun c => ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c⟩
    map_one' := Subtype.ext MvPolynomial.C_1
    map_mul' := fun a b => Subtype.ext (MvPolynomial.C_mul (a := a) (a' := b))
    map_zero' := Subtype.ext MvPolynomial.C_0
    map_add' := fun a b => Subtype.ext (MvPolynomial.C_add (a := a) (a' := b)) }

                                                           
def projectiveSpaceToSpec (N : ℕ) :
    complexProjectiveSpace N ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (constantsInDegreeZero N))

                                                                             
                                                                            
                                          
structure Surface where
  scheme : Scheme
  structureMap : scheme ⟶ Spec (CommRingCat.of ℂ)
  integral : IsIntegral scheme
  smooth : SmoothOfRelativeDimension 2 structureMap
  embeddingDimension : ℕ
  embedding : scheme ⟶ complexProjectiveSpace embeddingDimension
  closedImmersion : IsClosedImmersion embedding
  overComplex : embedding ≫ projectiveSpaceToSpec embeddingDimension = structureMap

attribute [instance] Surface.integral Surface.smooth Surface.closedImmersion

variable (X : Scheme)

                                                          
structure LineBundle where
  sheaf : X.Modules
  locallyRankOne : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (sheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

                                                                           
                                                                              
def moduleTensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

                                                        
def modulePow (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => moduleTensor X M (modulePow M n)

                                                                      
def structureSheaf : X.Modules := SheafOfModules.unit X.ringCatSheaf

                                                                        
abbrev GlobalSections (M : X.Modules) := structureSheaf X ⟶ M

                                                                                
                                                                         
def sectionOpen {M : X.Modules} (s : GlobalSections X M) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)), U

                                                                         
def LineBundle.IsAmple (L : LineBundle X) : Prop :=
  ∀ (x : X) (V : X.Opens), x ∈ V → ∃ n : ℕ, 0 < n ∧
    ∃ s : GlobalSections X (modulePow X L.sheaf n),
      x ∈ sectionOpen X s ∧ sectionOpen X s ≤ V ∧ IsAffineOpen (sectionOpen X s)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable (X : Scheme)

                                                       
def restrictScalar (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

                                                        
def sheafHomSMul {M N : X.Modules} (r : Γ(X, ⊤)) (f : M ⟶ N) : M ⟶ N where
  val := {
    app U := by
      letI : Module Γ(X, U.unop) (M.val.obj U) := (M.val.obj U).isModule
      letI : Module Γ(X, U.unop) (N.val.obj U) := (N.val.obj U).isModule
      let g : M.val.obj U →ₗ[Γ(X, U.unop)] N.val.obj U := (f.val.app U).hom
      exact ModuleCat.ofHom ((restrictScalar X U.unop r) • g)
    naturality {U V} g := by
      let : Module (X.presheaf.obj V) (N.presheaf.obj V) := (N.val.obj V).isModule
      ext m
      change restrictScalar X V.unop r • f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (restrictScalar X U.unop r • f.app U.unop m)
      have hn := CategoryTheory.congr_fun (f.mapPresheaf.naturality g) m
      change f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (f.app U.unop m) at hn
      rw [hn]
      calc
        _ = X.presheaf.map g (restrictScalar X U.unop r) •
            N.presheaf.map g (f.app U.unop m) := by
              exact congrArg (fun a : X.presheaf.obj V =>
                a • N.presheaf.map g (f.app U.unop m))
                (restrictScalar_naturality X g.unop r).symm
        _ = _ := (N.map_smul g.unop (restrictScalar X U.unop r) (f.app U.unop m)).symm }


instance sheafHomModule (M N : X.Modules) : Module Γ(X, ⊤) (M ⟶ N) where
  smul := sheafHomSMul X
  one_smul f := by
    ext U m
    change restrictScalar X U 1 • f.app U m = f.app U m
    simp
  mul_smul r s f := by
    ext U m
    change restrictScalar X U (r * s) • f.app U m =
      restrictScalar X U r • (restrictScalar X U s • f.app U m)
    simp [mul_smul]
  smul_zero r := by
    ext U m
    change restrictScalar X U r • (0 : Γ(N, U)) = 0
    exact smul_zero _
  smul_add r f g := by
    ext U m
    change restrictScalar X U r • (f.app U m + g.app U m) =
      restrictScalar X U r • f.app U m + restrictScalar X U r • g.app U m
    exact smul_add _ _ _
  zero_smul f := by
    ext U m
    change restrictScalar X U 0 • f.app U m = 0
    simp
  add_smul r s f := by
    ext U m
    change restrictScalar X U (r + s) • f.app U m =
      restrictScalar X U r • f.app U m + restrictScalar X U s • f.app U m
    simp [add_smul]

instance sheafLinear : Linear Γ(X, ⊤) X.Modules where
  smul_comp M N P r f g := by
    ext U m
    change g.app U (restrictScalar X U r • f.app U m) =
      restrictScalar X U r • g.app U (f.app U m)
    exact g.app_smul _ _
  comp_smul M N P f r g := by
    ext U m
    rfl

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme.{0}}

instance schemeHasExt : HasExt.{1} X.Modules := HasExt.standard X.Modules

                                                                           
                       
def baseScalars (f : X ⟶ Spec (CommRingCat.of ℂ)) : ℂ →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

                                                                      
                                                           

                                                                            
                                                                          
                                                                      
abbrev cohomology (M : X.Modules) (n : ℕ) : Type 1 :=
  Abelian.Ext.{1} (C := X.Modules) (structureSheaf X) M n

                                                                           
                                                                               
                                           
def cohomologyDimension (f : X ⟶ Spec (CommRingCat.of ℂ))
    (M : X.Modules) (n : ℕ) : ℕ :=
  letI : Module ℂ (cohomology M n) :=
    Module.compHom (cohomology M n) (baseScalars f)
  Module.finrank ℂ (cohomology M n)

                                                                              
                                                                           
def eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (M : X.Modules) : ℤ :=
  ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * (cohomologyDimension f M n : ℤ)

                                                                           
                                             
def selfIntersection (S : Surface) (L : LineBundle S.scheme) : ℤ :=
  eulerCharacteristic S.structureMap 2 (modulePow S.scheme L.sheaf 2) -
    2 * eulerCharacteristic S.structureMap 2 L.sheaf +
    eulerCharacteristic S.structureMap 2 (SheafOfModules.unit S.scheme.ringCatSheaf)

                                                                          
                                                                      
structure IntegralCurve (S : Surface) where
  scheme : Scheme
  embedding : scheme ⟶ S.scheme
  closedImmersion : IsClosedImmersion embedding
  integral : IsIntegral scheme
  dimension : topologicalKrullDim scheme = 1

attribute [instance] IntegralCurve.closedImmersion IntegralCurve.integral

                                                                    
                             
def curveDegree (S : Surface) (L : LineBundle S.scheme) (C : IntegralCurve S) : ℤ :=
  eulerCharacteristic (C.embedding ≫ S.structureMap) 1
    ((Scheme.Modules.pullback C.embedding).obj L.sheaf) -
  eulerCharacteristic (C.embedding ≫ S.structureMap) 1
    (SheafOfModules.unit C.scheme.ringCatSheaf)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

                               
abbrev complexBase : Scheme := Spec (CommRingCat.of ℂ)

                                                                           
abbrev ComplexPoint (S : Surface) :=
  Over.mk (𝟙 complexBase) ⟶ Over.mk S.structureMap

                                                             
def ComplexPoint.image {S : Surface} (p : ComplexPoint S) : S.scheme :=
  p.left (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)

                                                                                   
def surfacePower (S : Surface) (r : ℕ) : Over complexBase :=
  ∏ᶜ (fun _ : Fin r => Over.mk S.structureMap)

                                                                 
def tupleImage (S : Surface) (r : ℕ) (p : Fin r → ComplexPoint S) :
    (surfacePower S r).left :=
  (Limits.Pi.lift p).left (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)

                                                                               
                                        
@[instance_reducible] def tupleZariskiTopology (S : Surface) (r : ℕ) :
    TopologicalSpace (Fin r → ComplexPoint S) :=
  TopologicalSpace.induced (tupleImage S r) inferInstance

                                                                
def Configuration (S : Surface) (r : ℕ) :=
  {p : Fin r → ComplexPoint S // Function.Injective (fun i => (p i).image)}

instance configurationTopology (S : Surface) (r : ℕ) :
    TopologicalSpace (Configuration S r) :=
  letI := tupleZariskiTopology S r
  inferInstanceAs (TopologicalSpace {p : Fin r → ComplexPoint S //
    Function.Injective (fun i => (p i).image)})

                                                                     
                                                                     
                                                                        
                                                                       
def idealOrder {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) : ℕ :=
  sInf {n : ℕ | ¬ I ≤ IsLocalRing.maximalIdeal R ^ (n + 1)}

                                                                             
                                                                             
                                                      
def curveMultiplicity (S : Surface) (C : IntegralCurve S) (p : ComplexPoint S) : ℕ := by
  classical
  exact if h : ∃ q : C.scheme, C.embedding q = p.image then
    idealOrder (RingHom.ker (C.embedding.stalkMap h.choose).hom)
  else 0

                                                              
def totalMultiplicity (S : Surface) (r : ℕ) (C : IntegralCurve S)
    (p : Configuration S r) : ℕ :=
  ∑ i : Fin r, curveMultiplicity S C (p.val i)

                                                                 
def seshadriConstant (S : Surface) (L : LineBundle S.scheme) (r : ℕ)
    (p : Configuration S r) : ℝ :=
  sInf {a : ℝ | ∃ C : IntegralCurve S, 0 < totalMultiplicity S r C p ∧
    a = (curveDegree S L C : ℝ) / (totalMultiplicity S r C p : ℝ)}

                                                                               
                                                                               
                                                                               
                             

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

                                                                      
                                                                            
                              
def moduleCurveDegree (S : Surface) (M : S.scheme.Modules) (C : IntegralCurve S) : ℤ :=
  eulerCharacteristic (C.embedding ≫ S.structureMap) 1
    ((Scheme.Modules.pullback C.embedding).obj M) -
  eulerCharacteristic (C.embedding ≫ S.structureMap) 1
    (structureSheaf C.scheme)

                                                                             
                            
def sectionImageIdeal {X : Scheme} (J : LineBundle X)
    (ι : J.sheaf ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X, U) := by
  letI : Module Γ(X, U) (J.sheaf.val.obj (Opposite.op U)) :=
    (J.sheaf.val.obj (Opposite.op U)).isModule
  let φ : J.sheaf.val.obj (Opposite.op U) →ₗ[Γ(X, U)] Γ(X, U) :=
    (ι.val.app (Opposite.op U)).hom
  exact φ.range

                                                                            
                                                                            
                                                                                 
def PresentsPullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) : Prop :=
  Mono ι ∧ ∀ (U : Y.affineOpens) (V : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1),
    sectionImageIdeal J ι U.1 = (I.ideal V).map (f.appLE V.1 U.1 e).hom

                                                            
def InvertiblePullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X) : Prop :=
  ∃ (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y), PresentsPullbackIdeal I f J ι

                                                                             
                                                                            
                                                           
def centreIdeal (S : Surface) (r : ℕ) (p : Configuration S r) : S.scheme.IdealSheafData :=
  ∏ i : Fin r, (p.val i).left.ker

                                                                            
                                                                         
                                                       
def IsBlowup {X B : Scheme} (I : X.IdealSheafData) (π : B ⟶ X) : Prop :=
  InvertiblePullbackIdeal I π ∧ ∀ (Y : Scheme) (f : Y ⟶ X),
    InvertiblePullbackIdeal I f → ∃! h : Y ⟶ B, h ≫ π = f

                                                                         
                                                                            
                                                        
structure PointBlowup (S : Surface) (r : ℕ) (p : Configuration S r) where
  surface : Surface
  projection : surface.scheme ⟶ S.scheme
  overComplex : projection ≫ S.structureMap = surface.structureMap
  isBlowup : IsBlowup (centreIdeal S r p) projection
  exceptionalIdeal : Fin r → LineBundle surface.scheme
  exceptionalInclusion : ∀ i, (exceptionalIdeal i).sheaf ⟶ structureSheaf surface.scheme
  exceptionalPullback : ∀ i, PresentsPullbackIdeal (p.val i).left.ker projection
    (exceptionalIdeal i) (exceptionalInclusion i)

                                                           
                                                                              
                                                                        
def PointBlowup.BoundaryNef {S : Surface} {r : ℕ} {p : Configuration S r}
    (B : PointBlowup S r p) (L : LineBundle S.scheme) : Prop :=
  ∀ C : IntegralCurve B.surface,
    0 ≤ (moduleCurveDegree B.surface
      ((Scheme.Modules.pullback B.projection).obj L.sheaf) C : ℝ) +
      Real.sqrt ((selfIntersection S L : ℝ) / r) *
        ∑ i : Fin r, (curveDegree B.surface (B.exceptionalIdeal i) C : ℝ)

                                                                           
                                                                        
def EventualMaximalSeshadri (S : Surface) (L : LineBundle S.scheme) : Prop :=
  ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
    ∃ Z : ℕ → Set (Configuration S r),
      (∀ n, IsClosed (Z n) ∧ Z n ≠ Set.univ) ∧
      (∃ p : Configuration S r, ∀ n, p ∉ Z n) ∧
      ∀ p : Configuration S r, (∀ n, p ∉ Z n) →
        (∃ B : PointBlowup S r p, B.BoundaryNef L) ∧
        seshadriConstant S L r p = Real.sqrt ((selfIntersection S L : ℝ) / r)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry



end MaximalSeshadri.Geometry
end OAI


