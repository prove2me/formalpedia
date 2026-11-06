-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:57:45.056198+00:00
-- url     : https://prove2.me/theorems/c896e29c-4e1e-4dca-a99c-d00726b245fe
-- title:
--   Affine Differentials
-- statement:
--   Definitions and structural lemmas for Affine Differentials, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineDifferentials.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeDifferentials
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.LocallyBijective
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k A B M : Type*} [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
lemma derivation_ext_of_isLocalization (S : Submonoid A) [IsLocalization S B]
    (D E : Derivation k B M)
    (h : ∀ a : A, D (algebraMap A B a) = E (algebraMap A B a)) : D = E := by
  have hlift : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply LinearMap.ext_on_range
      (KaehlerDifferential.span_range_map_derivation_of_isLocalization k A B S)
    intro a
    simpa only [Function.comp_apply, KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D] using h a
  ext b
  simpa only [Derivation.liftKaehlerDifferential_comp_D] using
    LinearMap.congr_fun hlift (KaehlerDifferential.D k B b)
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A : CommRingCat.{u}) [CommRing k] [Algebra k A]
local notation "M" => ModuleCat.of A (KaehlerDifferential k A)
abbrev affineDifferentialBasicOpenRing (f : A) :=
  (Spec (A)).presheaf.obj (.op (PrimeSpectrum.basicOpen f))
abbrev affineDifferentialBasicOpenTildeModule (f : A) :=
  (tilde (R := A) M).presheaf.obj (.op (PrimeSpectrum.basicOpen f))
local notation "G" => affineDifferentialBasicOpenRing A
local notation "H" => affineDifferentialBasicOpenTildeModule k A
local instance basicOpenAlgebra (f : A) : Algebra A (G f) :=
  StructureSheaf.openAlgebra A (.op (PrimeSpectrum.basicOpen f))
local instance basicOpenLocalization (f : A) : IsLocalization.Away f (G f) :=
  StructureSheaf.IsLocalization.to_basicOpen A f
local instance basicOpenModule (f : A) : Module (G f) (H f) :=
  ((tilde (R := A) M).val.obj (.op (PrimeSpectrum.basicOpen f))).isModule
local instance basicOpenAModule (f : A) : Module A (H f) :=
  ((modulesSpecToSheaf.obj (tilde (R := A) M)).presheaf.obj
    (.op (PrimeSpectrum.basicOpen f))).isModule
local instance basicOpenModuleTower (f : A) : IsScalarTower A (G f) (H f) :=
  IsScalarTower.of_compHom A (G f) (H f)
local instance basicOpenBaseAlgebra (f : A) : Algebra k (G f) :=
  ((algebraMap A (G f)).comp (algebraMap k A)).toAlgebra
local instance basicOpenBaseTower (f : A) : IsScalarTower k A (G f) :=
  .of_algebraMap_eq' rfl
def affineDifferentialToBasicOpen (f : A) : KaehlerDifferential k A →ₗ[A] H f :=
  (tilde.toOpen (R := A) M (PrimeSpectrum.basicOpen f)).hom
local instance basicOpenTildeLocalization (f : A) :
    IsLocalizedModule.Away f (affineDifferentialToBasicOpen k A f) :=
  IsLocalizedModule.of_linearEquiv (.powers f)
    (StructureSheaf.toOpenₗ A M (PrimeSpectrum.basicOpen f))
    ((tilde.modulesSpecToSheafIso (R := A) M).app (.op (PrimeSpectrum.basicOpen f))).toLinearEquiv.symm
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Both actual modules are localizations of the same Ω(k,A). -/
def affineDifferentialBasicOpenEquiv (f : A) :
    KaehlerDifferential k (G f) ≃ₗ[A] H f :=
  IsLocalizedModule.linearEquiv (.powers f)
    (KaehlerDifferential.map k k A (G f))
    (affineDifferentialToBasicOpen k A f)
def affineDifferentialBasicOpenScalarEquiv (f : A) :
    KaehlerDifferential k (G f) ≃ₗ[G f] H f :=
  (affineDifferentialBasicOpenEquiv k A f).extendScalarsOfIsLocalization (.powers f) (G f)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma affineDifferentialBasicOpenEquiv_D (f a : A) :
    affineDifferentialBasicOpenEquiv k A f
      (KaehlerDifferential.D k (G f) (algebraMap A (G f) a)) =
    (affineDifferentialToBasicOpen k A f) (KaehlerDifferential.D k A a) := by
  rw [← KaehlerDifferential.map_D k k A (G f)]
  exact IsLocalizedModule.linearEquiv_apply (.powers f)
    (KaehlerDifferential.map k k A (G f))
    (affineDifferentialToBasicOpen k A f) _
local instance basicOpenKModule (f : A) : Module k (H f) :=
  Module.compHom (H f) (algebraMap k (G f))
local instance basicOpenKModuleTower (f : A) : IsScalarTower k (G f) (H f) :=
  IsScalarTower.of_compHom k (G f) (H f)
def affineDifferentialBasicOpenDerivation (f : A) : Derivation k (G f) (H f) :=
  (affineDifferentialBasicOpenScalarEquiv k A f).compDer (KaehlerDifferential.D k (G f))
lemma affineDifferentialBasicOpenDerivation_algebraMap (f a : A) :
    affineDifferentialBasicOpenDerivation k A f (algebraMap A (G f) a) =
      affineDifferentialToBasicOpen k A f (KaehlerDifferential.D k A a) :=
  affineDifferentialBasicOpenEquiv_D k A f a
lemma affineDifferentialBasicOpenDerivation_naturality (f g : A)
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (a : G f) :
    affineDifferentialBasicOpenDerivation k A g
      ((Spec A).presheaf.map (homOfLE h).op a) =
    (tilde (R := A) M).presheaf.map (homOfLE h).op
      (affineDifferentialBasicOpenDerivation k A f a) := by
  let r : G f ⟶ G g := (Spec A).presheaf.map (homOfLE h).op
  let : Algebra (G f) (G g) := r.hom.toAlgebra
  have hr (b : A) : r (algebraMap A (G f) b) = algebraMap A (G g) b := rfl
  let : IsScalarTower k (G f) (G g) := .of_algebraMap_eq' (by ext c; exact hr _)
  let : Module (G f) (H g) := Module.compHom (H g) r.hom
  let : IsScalarTower (G f) (G g) (H g) := .of_compHom (G f) (G g) (H g)
  let : IsScalarTower k (G f) (H g) := .of_algebraMap_smul (by
    intro c m
    change r (algebraMap k (G f) c) • m = algebraMap k (G g) c • m
    rw [IsScalarTower.algebraMap_apply k (G f) (G g)]
    rfl)
  let q : H f →ₗ[G f] H g :=
    ((tilde (R := A) M).val.map (homOfLE h).op).hom
  let d₁ : Derivation k (G f) (H g) :=
    (affineDifferentialBasicOpenDerivation k A g).compAlgebraMap (G f)
  let d₂ : Derivation k (G f) (H g) :=
    q.compDer (affineDifferentialBasicOpenDerivation k A f)
  have hd : d₁ = d₂ := derivation_ext_of_isLocalization (.powers f) d₁ d₂ (by
    intro b
    change affineDifferentialBasicOpenDerivation k A g
        (r (algebraMap A (G f) b)) =
      (tilde (R := A) M).presheaf.map (homOfLE h).op
        (affineDifferentialBasicOpenDerivation k A f (algebraMap A (G f) b))
    rw [hr, affineDifferentialBasicOpenDerivation_algebraMap,
      affineDifferentialBasicOpenDerivation_algebraMap]
    exact congrArg (fun t => t (KaehlerDifferential.D k A b))
      (tilde.toOpen_res (R := A) M (PrimeSpectrum.basicOpen f)
        (PrimeSpectrum.basicOpen g) (homOfLE h)).symm)
  exact Derivation.congr_fun hd a
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable (k : Type u) (A : CommRingCat.{u}) [CommRing k] [Algebra k A]
local notation "M" => ModuleCat.of A (KaehlerDifferential k A)
local notation "T" => tilde (R := A) M
local notation "B" => @PrimeSpectrum.basicOpen A _
abbrev affineDifferentialUnderlyingRingPresheaf :=
  (Spec A).presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
local notation "F" => affineDifferentialUnderlyingRingPresheaf A
abbrev affineDifferentialTildeAbelianSheaf :=
  (SheafOfModules.toSheaf (Spec A).ringCatSheaf).obj T
local notation "S" => affineDifferentialTildeAbelianSheaf k A
attribute [local instance] basicOpenAlgebra basicOpenLocalization basicOpenModule
  basicOpenAModule basicOpenModuleTower basicOpenBaseAlgebra basicOpenBaseTower
  basicOpenTildeLocalization basicOpenKModule basicOpenKModuleTower
local instance affineDifferentialTildeOpenModule (U : (Spec A).Opens) :
    Module Γ(Spec A, U) ((S).obj.obj (op U)) :=
  ((T).val.obj (op U)).isModule
local instance affineDifferentialTildeBasicModule (f : A) :
    Module (affineDifferentialBasicOpenRing A f) ((S).obj.obj (op (B f))) :=
  basicOpenModule k A f
def affineDifferentialDerivationOnBasis :
    (inducedFunctor B).op ⋙ F ⟶ (inducedFunctor B).op ⋙ (S).obj where
  app U := AddCommGrpCat.ofHom
    (affineDifferentialBasicOpenDerivation k A U.unop).toLinearMap.toAddMonoidHom
  naturality {U V} i := by
    ext a
    exact affineDifferentialBasicOpenDerivation_naturality k A U.unop V.unop
      (leOfHom i.unop.hom) a
def affineDifferentialAdditivePresheafMap : F ⟶ (S).obj :=
  TopCat.Sheaf.restrictHomEquivHom F S PrimeSpectrum.isBasis_basic_opens
    (affineDifferentialDerivationOnBasis k A)
lemma affineDifferentialAdditivePresheafMap_basicOpen (f : A)
    (a : affineDifferentialBasicOpenRing A f) :
    (affineDifferentialAdditivePresheafMap k A).app (op (B f)) a =
      affineDifferentialBasicOpenDerivation k A f a := by
  exact congrArg (fun t => t a)
    (TopCat.Sheaf.extend_hom_app F S PrimeSpectrum.isBasis_basic_opens
      (affineDifferentialDerivationOnBasis k A) f)
lemma affineDifferentialAdditivePresheafMap_naturality
    {U V : (Spec A).Opens} (i : V ⟶ U) (a : Γ(Spec A, U)) :
    (affineDifferentialAdditivePresheafMap k A).app (op V)
      ((Spec A).presheaf.map i.op a) =
      (T).presheaf.map i.op ((affineDifferentialAdditivePresheafMap k A).app (op U) a) :=
  congrArg (fun t => t a) ((affineDifferentialAdditivePresheafMap k A).naturality i.op)
lemma affineDifferentialAdditivePresheafMap_basicOpen_leibniz (f : A)
    (a b : affineDifferentialBasicOpenRing A f) :
    (affineDifferentialAdditivePresheafMap k A).app (op (B f)) (a * b) =
      a • (affineDifferentialAdditivePresheafMap k A).app (op (B f)) b +
      b • (affineDifferentialAdditivePresheafMap k A).app (op (B f)) a := by
  have h₁ := affineDifferentialAdditivePresheafMap_basicOpen k A f (a * b)
  have h₂ := (affineDifferentialBasicOpenDerivation k A f).leibniz a b
  have h₃ := congrArg₂ (fun x y => a • x + b • y)
    (affineDifferentialAdditivePresheafMap_basicOpen k A f b).symm
    (affineDifferentialAdditivePresheafMap_basicOpen k A f a).symm
  exact h₁.trans (h₂.trans h₃)
lemma affineDifferentialAdditivePresheafMap_leibniz (U : (Spec A).Opens)
    (a b : Γ(Spec A, U)) :
    (affineDifferentialAdditivePresheafMap k A).app (op U) (a * b) =
      a • (affineDifferentialAdditivePresheafMap k A).app (op U) b +
      b • (affineDifferentialAdditivePresheafMap k A).app (op U) a := by
  apply TopCat.Presheaf.IsSheaf.section_ext (S).property
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hle : B f ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
  refine ⟨B f, hle, hxf, ?_⟩
  let i : B f ⟶ U := homOfLE hle
  let r : Γ(Spec A, U) →+* affineDifferentialBasicOpenRing A f :=
    ((Spec A).presheaf.map i.op).hom
  let q : Γ(T, U) →+ affineDifferentialBasicOpenTildeModule k A f :=
    ((T).presheaf.map i.op).hom
  let dU := (affineDifferentialAdditivePresheafMap k A).app (op U)
  let dV := (affineDifferentialAdditivePresheafMap k A).app (op (B f))
  change q (dU (a * b)) = q (a • dU b + b • dU a)
  have hn (c : Γ(Spec A, U)) : dV (r c) = q (dU c) :=
    affineDifferentialAdditivePresheafMap_naturality k A i c
  have h₁ := (hn (a * b)).symm
  have h₂ := congrArg (fun t => dV t) (map_mul r a b)
  have h₃ := affineDifferentialAdditivePresheafMap_basicOpen_leibniz k A f (r a) (r b)
  have h₄ := congrArg₂ (fun t s => r a • t + r b • s) (hn b) (hn a)
  have h₅ := ((map_add q _ _).trans (congrArg₂ (fun t s => t + s)
    (Scheme.Modules.map_smul («M» := T) i a (dU b))
    (Scheme.Modules.map_smul («M» := T) i b (dU a)))).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
def affineDifferentialGlobalConstantMap : CommRingCat.of k ⟶ Γ(Spec A, ⊤) :=
  CommRingCat.ofHom (algebraMap k A) ≫ (Scheme.ΓSpecIso A).inv
lemma affineDifferentialConstantPresheafMap_basicOpen (f : A) :
    (schemeConstantPresheafMap (Spec A) (CommRingCat.of k)
      (affineDifferentialGlobalConstantMap k A)).app (op (B f)) =
      CommRingCat.ofHom (algebraMap k (affineDifferentialBasicOpenRing A f)) := by
  change CommRingCat.ofHom (algebraMap k A) ≫
      ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.map (homOfLE le_top).op) =
    CommRingCat.ofHom (algebraMap k A) ≫
      CommRingCat.ofHom (algebraMap A (affineDifferentialBasicOpenRing A f))
  exact congrArg (fun t => CommRingCat.ofHom (algebraMap k A) ≫ t)
    (Scheme.toOpen_eq A (B f)).symm
lemma affineDifferentialAdditivePresheafMap_constant (U : (Spec A).Opens) (c : k) :
    (affineDifferentialAdditivePresheafMap k A).app (op U)
      ((schemeConstantPresheafMap (Spec A) (CommRingCat.of k)
        (affineDifferentialGlobalConstantMap k A)).app (op U) c) = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext (S).property
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hle : B f ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
  refine ⟨B f, hle, hxf, ?_⟩
  rw [map_zero]
  change (T).presheaf.map (homOfLE hle).op
    ((affineDifferentialAdditivePresheafMap k A).app (op U) _) = 0
  erw [← affineDifferentialAdditivePresheafMap_naturality]
  have hc := congrArg (fun t => t c)
    ((schemeConstantPresheafMap (Spec A) (CommRingCat.of k)
      (affineDifferentialGlobalConstantMap k A)).naturality (homOfLE hle).op)
  change ((schemeConstantPresheafMap (Spec A) (CommRingCat.of k)
    (affineDifferentialGlobalConstantMap k A)).app (op (B f))) c =
      (Spec A).presheaf.map (homOfLE hle).op
        (((schemeConstantPresheafMap (Spec A) (CommRingCat.of k)
          (affineDifferentialGlobalConstantMap k A)).app (op U)) c) at hc
  erw [← hc, affineDifferentialConstantPresheafMap_basicOpen,
    affineDifferentialAdditivePresheafMap_basicOpen]
  exact (affineDifferentialBasicOpenDerivation k A f).map_algebraMap c
local notation "cA" => affineDifferentialGlobalConstantMap k A
local notation "Omegap" => schemeDifferentialPresheaf (Spec A) (CommRingCat.of k) cA
local notation "Omega" => schemeDifferentialSheaf (Spec A) (CommRingCat.of k) cA
local notation "phiA" => schemeConstantPresheafMap (Spec A) (CommRingCat.of k) cA
def affineDifferentialTildeDerivation :
    ((Scheme.Modules.toPresheafOfModules (Spec A)).obj T).Derivation' phiA where
  d {U} := ((affineDifferentialAdditivePresheafMap k A).app U).hom
  d_mul {U} a b := affineDifferentialAdditivePresheafMap_leibniz k A U.unop a b
  d_map {_U _V} i a := affineDifferentialAdditivePresheafMap_naturality k A i.unop a
  d_app {U} a := affineDifferentialAdditivePresheafMap_constant k A U.unop a
def affineDifferentialPresheafComparison : Omegap ⟶ (T).val :=
  (PresheafOfModules.DifferentialsConstruction.isUniversal' phiA).desc
    (affineDifferentialTildeDerivation k A)
lemma affineDifferentialPresheafComparison_D (U : (Spec A).Opens)
    (a : Γ(Spec A, U)) :
    (affineDifferentialPresheafComparison k A).app (op U)
      (CommRingCat.KaehlerDifferential.d a) =
      (affineDifferentialAdditivePresheafMap k A).app (op U) a :=
  PresheafOfModules.Derivation.congr_d
    ((PresheafOfModules.DifferentialsConstruction.isUniversal' phiA).fac
      (affineDifferentialTildeDerivation k A)) a
def affineDifferentialSheafComparison : Omega ⟶ T :=
  (schemeDifferentialSheafHomEquiv (Spec A) (CommRingCat.of k) cA T).symm
    (affineDifferentialTildeDerivation k A)
lemma affineDifferentialPresheafComparison_basicOpen (f : A) :
    (affineDifferentialPresheafComparison k A).app (op (B f)) =
      ModuleCat.ofHom (affineDifferentialBasicOpenScalarEquiv k A f).toLinearMap := by
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  exact (affineDifferentialPresheafComparison_D k A (B f) a).trans
    (affineDifferentialAdditivePresheafMap_basicOpen k A f a)
def affineDifferentialAbelianPresheafComparison :=
  (PresheafOfModules.toPresheaf (Spec A).ringCatSheaf.obj).map
    (affineDifferentialPresheafComparison k A)
lemma affineDifferentialAbelianPresheafComparison_basicOpen_bijective (f : A) :
    Function.Bijective ((affineDifferentialAbelianPresheafComparison k A).app (op (B f))) := by
  change Function.Bijective (fun x =>
    (affineDifferentialPresheafComparison k A).app (op (B f)) x)
  rw [affineDifferentialPresheafComparison_basicOpen k A f]
  exact (affineDifferentialBasicOpenScalarEquiv k A f).bijective
lemma affineDifferentialAbelianPresheafComparison_locallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective
      (_root_.Opens.grothendieckTopology (Spec A))
      (affineDifferentialAbelianPresheafComparison k A) where
  equalizerSieve_mem {U} s t heq x hx := by
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hle : B f ≤ U.unop⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.unop.2
    refine ⟨B f, homOfLE hle, ?_, hxf⟩
    apply (affineDifferentialAbelianPresheafComparison_basicOpen_bijective k A f).injective
    have hr := congrArg (fun z =>
      (T).presheaf.map (homOfLE hle).op z) heq
    exact ((affineDifferentialAbelianPresheafComparison k A).naturality_apply
      (homOfLE hle).op s).trans
        (hr.trans ((affineDifferentialAbelianPresheafComparison k A).naturality_apply
          (homOfLE hle).op t).symm)
lemma affineDifferentialAbelianPresheafComparison_locallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective
      (_root_.Opens.grothendieckTopology (Spec A))
      (affineDifferentialAbelianPresheafComparison k A) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hle : B f ≤ U⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.2
    obtain ⟨t, ht⟩ :=
      (affineDifferentialAbelianPresheafComparison_basicOpen_bijective k A f).surjective
        ((T).presheaf.map (homOfLE hle).op s)
    exact ⟨B f, homOfLE hle, ⟨t, ht⟩, hxf⟩
lemma affineDifferentialSheafComparison_homEquiv :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (Spec A).ringCatSheaf.obj)
      (affineDifferentialSheafComparison k A) =
      affineDifferentialPresheafComparison k A := by
  apply (PresheafOfModules.DifferentialsConstruction.isUniversal' phiA).postcomp_injective
  exact ((schemeDifferentialSheafHomEquiv (Spec A) (CommRingCat.of k) cA T).apply_symm_apply
    (affineDifferentialTildeDerivation k A)).trans
      ((PresheafOfModules.DifferentialsConstruction.isUniversal' phiA).fac
        (affineDifferentialTildeDerivation k A)).symm
lemma affineDifferentialSheafComparison_isIso : IsIso (affineDifferentialSheafComparison k A) := by
  let J := _root_.Opens.grothendieckTopology (Spec A)
  let unit := CategoryTheory.toSheafify J (Omegap).presheaf
  let theta := (SheafOfModules.toSheaf (Spec A).ringCatSheaf).map
    (affineDifferentialSheafComparison k A)
  have hfac : unit ≫ theta.hom = affineDifferentialAbelianPresheafComparison k A := by
    have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
      (𝟙 (Spec A).ringCatSheaf.obj) (affineDifferentialSheafComparison k A)
    rw [affineDifferentialSheafComparison_homEquiv k A] at h
    exact h.symm
  have hinj : CategoryTheory.Presheaf.IsLocallyInjective J theta.hom :=
    (CategoryTheory.Presheaf.comp_isLocallyInjective_iff J unit theta.hom).mp (by
      rw [hfac]
      exact affineDifferentialAbelianPresheafComparison_locallyInjective k A)
  have hsurj : CategoryTheory.Presheaf.IsLocallySurjective J theta.hom :=
    (CategoryTheory.Presheaf.comp_isLocallySurjective_iff J unit theta.hom).mp (by
      rw [hfac]
      exact affineDifferentialAbelianPresheafComparison_locallySurjective k A)
  have hiso : IsIso theta :=
    (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso theta).mp ⟨hinj, hsurj⟩
  have hpresheaf : IsIso theta.hom :=
    (CategoryTheory.sheafToPresheaf J AddCommGrpCat).map_isIso theta
  exact (isIso_iff_of_reflects_iso (affineDifferentialSheafComparison k A)
    (Scheme.Modules.toPresheaf (Spec A))).mp hpresheaf
def affineDifferentialSheafIso : Omega ≅ T :=
  letI := affineDifferentialSheafComparison_isIso k A
  asIso (affineDifferentialSheafComparison k A)
local instance affineDifferentialOmegaOpenAModule (U : (Spec A).Opens) : Module A Γ(Omega, U) :=
  ((modulesSpecToSheaf (R := A)).obj Omega).presheaf.obj (op U) |>.isModule
def affineDifferentialGlobalSectionsEquiv : Γ(Omega, ⊤) ≃ₗ[A] KaehlerDifferential k A :=
  (((modulesSpecToSheaf (R := A) ⋙ TopCat.Sheaf.forget (ModuleCat A) (Spec A)).mapIso
    (affineDifferentialSheafIso k A)).app (op ⊤)).toLinearEquiv.trans
      (tilde.isoTop (R := A) M).toLinearEquiv.symm
end
end QEC.Coding.AlgebraicGeometry


