-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:53.630094+00:00
-- url     : https://prove2.me/theorems/4d271ecb-543a-41bc-8803-d746a5211727
-- title:
--   Is Iso Pullback Obj Unit To Unit
-- statement:
--   Definitions and structural lemmas for Is Iso Pullback Obj Unit To Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/IsIsoPullbackObjUnitToUnit.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_restrict
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isInvertibleSheaf_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
section VectorBundle
variable {X : Scheme.{u}}
def IsFreeBasisOn (P : PMod X) (U : X.Opens) {n : ℕ} (s : Fin n → P.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : Fin n → ringOn X V => ∑ i, r i • resM P h (s i))
def IsVectorBundle (E : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (s : Fin n → ((preMod X).obj E).obj (op U)), IsFreeBasisOn ((preMod X).obj E) U s
theorem isFreeBasisOn_of_isBasisOn {P : PMod X} {U : X.Opens} {s : P.obj (op U)}
    (hs : IsBasisOn P U s) : IsFreeBasisOn P U (fun _ : Fin 1 => s) := by
  intro V h
  have e : (fun r : Fin 1 → ringOn X V => ∑ i, r i • resM P h ((fun _ : Fin 1 => s) i)) =
      (fun c : ringOn X V => c • resM P h s) ∘ (fun r : Fin 1 → ringOn X V => r 0) := by
    funext r
    simp
  rw [e]
  exact (hs V h).comp (Equiv.funUnique (Fin 1) (ringOn X V)).bijective
theorem IsInvertibleSheaf.isVectorBundle {E : X.Modules} (hE : IsInvertibleSheaf E) :
    IsVectorBundle E := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hE x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  exact ⟨V, hV, hxV, 1, fun _ => resM _ (homOfLE hVU).le s,
    isFreeBasisOn_of_isBasisOn (hs.restrict _)⟩
theorem isVectorBundle_unit (X : Scheme.{u}) : IsVectorBundle (𝟙_ X.Modules) :=
  IsInvertibleSheaf.isVectorBundle isInvertibleSheaf_unit
end VectorBundle
section OverZ
def toSpecZ (X : Scheme.{0}) : X ⟶ Spec (.of ℤ) := specZIsTerminal.from X
theorem specZ_hom_ext {X : Scheme.{0}} (f g : X ⟶ Spec (.of ℤ)) : f = g :=
  specZIsTerminal.hom_ext f g
def IsFiniteTypeOverZ (X : Scheme.{0}) : Prop :=
  LocallyOfFiniteType (toSpecZ X) ∧ QuasiCompact (toSpecZ X)
def invOpen (X : Scheme.{0}) (m : ℕ) : X.Opens :=
  toSpecZ X ⁻¹ᵁ (PrimeSpectrum.basicOpen (m : ℤ) : (Spec (.of ℤ)).Opens)
instance (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
abbrev ZLoc (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})
def zLocToRat (p : Nat.Primes) : ZLoc p →+* ℚ :=
  IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (g := algebraMap ℤ ℚ) (by
    rintro ⟨y, hy⟩
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    apply hy
    have : y = 0 := by simpa using h0
    rw [this]
    exact Ideal.zero_mem _)
def atP (X : Scheme.{0}) (p : Nat.Primes) : Scheme.{0} :=
  pullback (toSpecZ X) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZLoc p))))
def atPTo (X : Scheme.{0}) (p : Nat.Primes) : atP X p ⟶ X := pullback.fst _ _
def genFib (X : Scheme.{0}) : Scheme.{0} :=
  pullback (toSpecZ X) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
def genTo (X : Scheme.{0}) : genFib X ⟶ X := pullback.fst _ _
def genToAtP (X : Scheme.{0}) (p : Nat.Primes) : genFib X ⟶ atP X p :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom (zLocToRat p))) (𝟙 _)
    (specZ_hom_ext _ _) (specZ_hom_ext _ _)
theorem genToAtP_atPTo (X : Scheme.{0}) (p : Nat.Primes) :
    genToAtP X p ≫ atPTo X p = genTo X :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)
end OverZ
section Pullbacks
variable {A B C D : Scheme.{u}}
def pbSquare (q : A ⟶ B) (j : B ⟶ D) (k : A ⟶ C) (r : C ⟶ D) (h : q ≫ j = k ≫ r)
    (M : D.Modules) :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback j).obj M) ≅
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback r).obj M) :=
  (Scheme.Modules.pullbackComp q j).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp k r).app M).symm
def pbSection (f : A ⟶ B) (M : B.Modules) (t : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) t
end Pullbacks
section Generic
variable {X : Scheme.{u}} [IrreducibleSpace X]
structure GenericStalkIso (E E' : X.Modules) where

  toAddEquiv : E.presheaf.stalk (genericPoint X) ≃+ E'.presheaf.stalk (genericPoint X)

  map_smul_germ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (r : Γ(X, U)) (s : Γ(E, U))
    (t : Γ(E', U)), toAddEquiv (E.presheaf.germ U _ hU s) = E'.presheaf.germ U _ hU t →
      toAddEquiv (E.presheaf.germ U _ hU (r • s)) = E'.presheaf.germ U _ hU (r • t)
def germImage (E : X.Modules) (x : X) : Set (E.presheaf.stalk (genericPoint X)) :=
  {v | ∃ (U : X.Opens) (_ : x ∈ U) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
    E.presheaf.germ U _ hU s = v}
end Generic
section Opens
def primeProd (S : Finset Nat.Primes) : ℕ := ∏ p ∈ S, (p : ℕ)
def genOpen (X : Scheme.{0}) (m : ℕ) : (genFib X).Opens := genTo X ⁻¹ᵁ invOpen X m
def genRes (X : Scheme.{0}) (m : ℕ) : (genOpen X m).toScheme ⟶ (invOpen X m).toScheme :=
  genTo X ∣_ invOpen X m
def atPOpen (X : Scheme.{0}) (p : Nat.Primes) (m : ℕ) : (atP X p).Opens :=
  atPTo X p ⁻¹ᵁ invOpen X m
def atPRes (X : Scheme.{0}) (p : Nat.Primes) (m : ℕ) :
    (atPOpen X p m).toScheme ⟶ (invOpen X m).toScheme :=
  atPTo X p ∣_ invOpen X m
def subOpen (X : Scheme.{0}) (a m' : ℕ) : (invOpen X a).toScheme.Opens :=
  (invOpen X a).ι ⁻¹ᵁ invOpen X (a * m')
def subRes (X : Scheme.{0}) (a m' : ℕ) :
    (genRes X a ⁻¹ᵁ subOpen X a m').toScheme ⟶ (subOpen X a m').toScheme :=
  genRes X a ∣_ subOpen X a m'
theorem subRes_square (X : Scheme.{0}) (a m' : ℕ) :
    subRes X a m' ≫ (subOpen X a m').ι = (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ genRes X a :=
  morphismRestrict_ι _ _
theorem glue_square (X : Scheme.{0}) (m : ℕ) (p : Nat.Primes) :
    genRes X m ≫ (invOpen X m).ι = ((genOpen X m).ι ≫ genToAtP X p) ≫ atPTo X p := by
  have h := morphismRestrict_ι (genTo X) (invOpen X m)
  rw [Category.assoc, genToAtP_atPTo]
  exact h
end Opens
section Generic
variable {X : Scheme.{u}} [IrreducibleSpace X]
theorem germ_smul_eq {E : X.Modules} {U : X.Opens} (hU : genericPoint X ∈ U) (r : Γ(X, U))
    {s t : Γ(E, U)} (h : E.presheaf.germ U _ hU s = E.presheaf.germ U _ hU t) :
    E.presheaf.germ U _ hU (r • s) = E.presheaf.germ U _ hU (r • t) := by
  obtain ⟨W, hW, i, j, hst⟩ := TopCat.Presheaf.germ_eq E.presheaf _ hU hU s t h
  rw [show j = i from Subsingleton.elim _ _] at hst
  rw [← E.presheaf.germ_res_apply i _ hW, ← E.presheaf.germ_res_apply i _ hW,
    Scheme.Modules.map_smul, Scheme.Modules.map_smul, hst]
def GenericStalkIso.refl (E : X.Modules) : GenericStalkIso E E where
  toAddEquiv := AddEquiv.refl _
  map_smul_germ _ hU r _ _ h := germ_smul_eq hU r h
end Generic
section Unit
variable {X Y : Scheme.{u}}
instance final_opensMap (f : X ⟶ Y) : (Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
set_option backward.isDefEq.respectTransparency.types false in

theorem isIso_pullbackObjUnitToUnit (f : X ⟶ Y)
    [(SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _
      _).bijective.of_comp_iff', ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert! (SheafOfModules.bijective_pushforwardSections f.toRingCatSheafHom M).comp
    (SheafOfModules.unitHomEquiv _).bijective
  ext g : 1
  dsimp
  rw [SheafOfModules.pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (isIso_pullbackObjUnitToUnit f)
end Unit
section SchemeStatements
def BundlesAgree.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X] (E E' : X.Modules),
    IsVectorBundle E → IsVectorBundle E' → ∀ φ : GenericStalkIso E E',
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      φ.toAddEquiv '' germImage E x = germImage E' x) →
    ∃! e : E ≅ E', ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      φ.toAddEquiv (E.presheaf.germ U _ hU s) =
        E'.presheaf.germ U _ hU (Scheme.Modules.Hom.app e.hom U s)
def SpreadBundle.Statement : Prop :=
  ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (p : Nat.Primes) (E : (atP X p).Modules),
    IsVectorBundle E → ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ m' : ℕ, m ∣ m' → ¬ (p : ℕ) ∣ m' →
      ∃ E' : (invOpen X m').toScheme.Modules, IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (atPRes X p m')).obj E' ≅
          (Scheme.Modules.pullback (atPOpen X p m').ι).obj E)
def SpreadIso.Statement : Prop :=
  ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (a : ℕ), 0 < a →
    ∀ (F G : (invOpen X a).toScheme.Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ ψ : (Scheme.Modules.pullback (genRes X a)).obj F ≅
      (Scheme.Modules.pullback (genRes X a)).obj G,
    ∃ m' : ℕ, 0 < m' ∧ ∃ f : (Scheme.Modules.pullback (subOpen X a m').ι).obj F ≅
        (Scheme.Modules.pullback (subOpen X a m').ι).obj G,
      (Scheme.Modules.pullback (subRes X a m')).map f.hom =
        (pbSquare _ _ _ _ (subRes_square X a m') F).hom ≫
          (Scheme.Modules.pullback (genRes X a ⁻¹ᵁ subOpen X a m').ι).map ψ.hom ≫
            (pbSquare _ _ _ _ (subRes_square X a m') G).inv
def PrimeOpensCover.Statement : Prop :=
  ∀ (X : Scheme.{0}) (S : Finset Nat.Primes) (mp : Nat.Primes → ℕ),
    (∀ p ∈ S, ¬ (p : ℕ) ∣ mp p) → (∀ p ∈ S, ∀ q ∈ S, q ≠ p → (q : ℕ) ∣ mp p) →
    ((invOpen X (primeProd S) ⊔ ⨆ p ∈ S, invOpen X (mp p)) = ⊤) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      invOpen X (mp p) ⊓ invOpen X (mp q) ≤ invOpen X (primeProd S) ∧
      invOpen X (mp p) ⊓ invOpen X (mp q) ≤ invOpen X (primeProd S * mp p)
structure GlueBundles.Data (X : Scheme.{0}) (S : Finset Nat.Primes) where

  E₀ : (invOpen X (primeProd S)).toScheme.Modules
  isVB₀ : IsVectorBundle E₀

  E : ∀ p : S, (atP X p).Modules
  isVB : ∀ p : S, IsVectorBundle (E p)

  γ : ∀ p : S, (Scheme.Modules.pullback ((genOpen X (primeProd S)).ι ≫ genToAtP X p)).obj (E p) ≅
    (Scheme.Modules.pullback (genRes X (primeProd S))).obj E₀
def GlueBundles.Statement : Prop :=
  ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (S : Finset Nat.Primes) (D : GlueBundles.Data X S),
    ∃ E : X.Modules, IsVectorBundle E ∧
      ∃ (α : (Scheme.Modules.pullback (invOpen X (primeProd S)).ι).obj E ≅ D.E₀)
        (β : ∀ p : S, (Scheme.Modules.pullback (atPTo X p)).obj E ≅ D.E p),
        ∀ p : S, (pbSquare _ _ _ _ (glue_square X (primeProd S) p) E).hom ≫
            (Scheme.Modules.pullback ((genOpen X (primeProd S)).ι ≫ genToAtP X p)).map (β p).hom ≫
              (D.γ p).hom =
          (Scheme.Modules.pullback (genRes X (primeProd S))).map α.hom
def ClearDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X], Flat (toSpecZ X) →
    ∀ (L : X.Modules), IsVectorBundle L →
    ∀ s : Γ((Scheme.Modules.pullback (genTo X)).obj L, genTo X ⁻¹ᵁ ⊤),
    ∃ N : ℕ, 0 < N ∧ ∃ t : Γ(L, ⊤), pbSection (genTo X) L t = N • s
end SchemeStatements
section AlgebraStatements
def Dominates (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    (V : Subring K) : Prop :=
  ∃ h : ∀ a : A, algebraMap A K a ∈ V,
    ∀ a : A, (⟨_, h a⟩ : V) ∈ nonunits V ↔ a ∈ IsLocalRing.maximalIdeal A
def DominatingDVR.Statement : Prop :=
  (∀ (A K : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra A K] [IsFractionRing A K], ¬ IsField A →
      ∃ V : Subring K, IsDiscreteValuationRing V ∧ Dominates A V) ∧
  (∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (z : Z), z ≠ genericPoint Z →
      ∃ V : Subring Z.functionField, IsDiscreteValuationRing V ∧ Dominates (Z.presheaf.stalk z) V)
def blowUpChart (A K : Type*) [CommRing A] [Field K] [Algebra A K] {n : ℕ} (x : Fin n → A)
    (i : Fin n) : Subalgebra A K :=
  Algebra.adjoin A (Set.range fun j => algebraMap A K (x j) / algebraMap A K (x i))
def BlowUpChart.Statement : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] (n : ℕ) (x : Fin n → A),
    Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A → (∃ i, x i ≠ 0) →
    ∃ i, x i ≠ 0 ∧ ¬ IsUnit (algebraMap A (blowUpChart A K x i) (x i)) ∧
      ∀ P : Ideal (blowUpChart A K x i), P.IsPrime → algebraMap A _ (x i) ∈ P →
        P.comap (algebraMap A (blowUpChart A K x i)) = IsLocalRing.maximalIdeal A
def KrullAkizuki.Statement : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L], ringKrullDim R = 1 →
    (∀ S : Subalgebra R L, IsNoetherianRing S ∧ ringKrullDim S ≤ 1) ∧
      IsDedekindDomain (integralClosure R K)
def locIn (A K : Type*) [CommRing A] [Field K] [Algebra A K] (p : Ideal A) : Set K :=
  {y | ∃ a s : A, s ∉ p ∧ algebraMap A K s * y = algebraMap A K a}
def HeightOneIntersection.Statement : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K],
    Set.range (algebraMap A K) = ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p
def locSub {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V] (M : Submodule A V)
    (p : Ideal A) : Set V :=
  {v | ∃ s : A, s ∉ p ∧ s • v ∈ M}
def LatticesAgree.Statement : Prop :=
  ∀ (A K V : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module A V] [IsScalarTower A K V] (M N : Submodule A V),
    Module.Finite A M → Module.Projective A M → Module.Finite A N → Module.Projective A N →
    Submodule.span K (M : Set V) = ⊤ → Submodule.span K (N : Set V) = ⊤ →
    (∀ p : Ideal A, p.IsPrime → p.height = 1 → locSub M p = locSub N p) → M = N
def FiniteIntegralClosure.Statement : Prop :=
  (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L], Module.Finite A (integralClosure A L)) ∧
  (∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
    ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
      (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
      letI : Algebra Γ(X, U) L :=
        ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
          haveI := hU; infer_instance))).toAlgebra
      Module.Finite Γ(X, U) (integralClosure Γ(X, U) L))
end AlgebraStatements
section NumberStatements
open GroundTheory.Heights₂.Heights.NumbersDVR in

def SectionNef.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ι : κ → Type) [∀ k, Fintype (ι k)] (F : Type)
    [Field F] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ringKrullDim (MRing ι F ⧸ P) = ((1 + Fintype.card κ : ℕ) : WithBot ℕ∞) →
    ∀ a : κ → ℕ,
      ((∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ P) ∨
        (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W →
          ∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ W)) →
      0 ≤ intNum F P ![fun k => (a k : ℤ)]
def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊B⌋₊ + 1)), Real.log p / p ≤ Real.log B + C
def cp (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)
def SumCp.Statement : Prop :=
  ∀ d : ℤ, d ≠ 0 → ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ B) →
    ∑ p ∈ S, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ C * Real.log B
end NumberStatements
section Inhabitants
abbrev specInt : Scheme.{0} := Spec (.of ℤ)
def prime2 : Nat.Primes := ⟨2, Nat.prime_two⟩
def prime3 : Nat.Primes := ⟨3, Nat.prime_three⟩
def primePt (p : Nat.Primes) : PrimeSpectrum ℤ := ⟨Ideal.span {((p : ℕ) : ℤ)}, inferInstance⟩
def closedPt (p : Nat.Primes) : specInt := primePt p
abbrev intLattice : Submodule ℤ ℚ := Submodule.span ℤ {1}
def GlueBundles.dataSpecInt : GlueBundles.Data specInt {prime2} where
  E₀ := SheafOfModules.unit _
  isVB₀ := isVectorBundle_unit _
  E _ := SheafOfModules.unit _
  isVB _ := isVectorBundle_unit _
  γ _ := pullbackUnitIso _ ≪≫ (pullbackUnitIso _).symm
end Inhabitants
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model


