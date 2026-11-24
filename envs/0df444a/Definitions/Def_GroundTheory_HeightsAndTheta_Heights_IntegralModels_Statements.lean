-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:39.920827+00:00
-- url     : https://prove2.me/theorems/91ed785a-aaca-4e2a-bad1-2856460c27c7
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
section VectorBundle
universe u
variable {X : Scheme.{u}}
def IsBasisOn (M : X.Modules) (U : X.Opens) {n : ℕ} (s : Fin n → Γ(M, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : Fin n → Γ(X, V) => ∑ i, r i • (M.presheaf.map (homOfLE h).op).hom (s i))
def IsVectorBundle (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (s : Fin n → Γ(M, U)), IsBasisOn M U s
variable (X) in

def structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf
end VectorBundle
section OverZ
abbrev SpecZ : Scheme.{0} := Spec (CommRingCat.of ℤ)
variable {X : Scheme.{0}}
def invOpen (f : X ⟶ SpecZ) (m : ℤ) : X.Opens :=
  f ⁻¹ᵁ PrimeSpectrum.basicOpen (m : CommRingCat.of ℤ)
lemma mem_invOpen (f : X ⟶ SpecZ) (m : ℤ) (x : X) :
    x ∈ invOpen f m ↔ (m : ℤ) ∉ (f.base x).asIdeal := Iff.rfl
lemma invOpen_mul_le_left (f : X ⟶ SpecZ) (a b : ℤ) : invOpen f (a * b) ≤ invOpen f a := by
  intro x hx
  rw [mem_invOpen] at hx ⊢
  exact fun h => hx (Ideal.mul_mem_right _ _ h)
instance isPrime_span_prime (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).2 (Nat.prime_iff_prime_int.mp p.2)
abbrev ZLoc (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})
abbrev baseChange (f : X ⟶ SpecZ) (R : Type) [CommRing R] : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (Int.castRingHom R)))
abbrev baseChangeMap (f : X ⟶ SpecZ) (R : Type) [CommRing R] : baseChange f R ⟶ X :=
  pullback.fst _ _
lemma range_baseChangeMap_subset (f : X ⟶ SpecZ) (R : Type) [CommRing R] (m : ℤ)
    (hm : IsUnit (m : R)) :
    Set.range (baseChangeMap f R) ⊆ Set.range (invOpen f m).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (m : ℤ) ∉ (f.base ((pullback.fst _ _ : baseChange f R ⟶ X).base y)).asIdeal
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  intro hz
  have hz' : (m : R) ∈
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (Int.castRingHom R)))).base y).asIdeal := hz
  exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ hz' hm)
def toInvOpen (f : X ⟶ SpecZ) (R : Type) [CommRing R] (m : ℤ) (hm : IsUnit (m : R)) :
    baseChange f R ⟶ (invOpen f m : Scheme.{0}) :=
  IsOpenImmersion.lift (invOpen f m).ι (baseChangeMap f R) (range_baseChangeMap_subset f R m hm)
@[reassoc (attr := simp)]
lemma toInvOpen_ι (f : X ⟶ SpecZ) (R : Type) [CommRing R] (m : ℤ)
    (hm : IsUnit (m : R)) : toInvOpen f R m hm ≫ (invOpen f m).ι = baseChangeMap f R :=
  IsOpenImmersion.lift_fac _ _ _
end OverZ
section Maps
variable {X : Scheme.{0}}
lemma isUnit_intCast_zLoc (p : Nat.Primes) (m : ℤ) (hm : ¬ ((p : ℕ) : ℤ) ∣ m) :
    IsUnit (m : ZLoc p) := by
  have := IsLocalization.map_units (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (ZLoc p)
    ⟨m, fun h => hm (Ideal.mem_span_singleton.mp h)⟩
  rwa [eq_intCast] at this
lemma isUnit_intCast_rat (m : ℤ) (hm : m ≠ 0) : IsUnit (m : ℚ) := by
  rw [isUnit_iff_ne_zero]
  exact_mod_cast hm
def zLocToRat (p : Nat.Primes) : ZLoc p →+* ℚ :=
  IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (g := Int.castRingHom ℚ)
    (fun s => by
      have hs : (s : ℤ) ≠ 0 := fun h => s.2 (h ▸ Ideal.zero_mem _)
      simpa using hs)
def ratToLoc (f : X ⟶ SpecZ) (p : Nat.Primes) : baseChange f ℚ ⟶ baseChange f (ZLoc p) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (zLocToRat p))) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ : ℤ →+* ℚ => pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ))
      (RingHom.ext_int _ _))
@[reassoc (attr := simp)]
lemma ratToLoc_baseChangeMap (f : X ⟶ SpecZ) (p : Nat.Primes) :
    ratToLoc f p ≫ baseChangeMap f (ZLoc p) = baseChangeMap f ℚ :=
  pullback.lift_fst _ _ _
end Maps
section Pullback
universe u
variable {T Y Z : Scheme.{u}}
def pullbackCompIso {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k) {E : Z.Modules}
    {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    (Scheme.Modules.pullback k).obj E ≅ (Scheme.Modules.pullback g).obj F :=
  ((Scheme.Modules.pullbackCongr e).app E).symm ≪≫ ((Scheme.Modules.pullbackComp g h).app E).symm ≪≫
    (Scheme.Modules.pullback g).mapIso γ
def pullSection (c : T ⟶ Z) (L : Z.Modules) :
    Γ(L, ⊤) →+ Γ((Scheme.Modules.pullback c).obj L, c ⁻¹ᵁ ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤).hom
end Pullback
section Normal
universe u
def IsNormalScheme (X : Scheme.{u}) : Prop := ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)
instance stalkModule {X : Scheme.{u}} (E : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) E.val x
def genericImage {X : Scheme.{u}} [IrreducibleSpace X] (E : X.Modules) (x : X) :
    AddSubgroup (E.presheaf.stalk (genericPoint X)) :=
  (E.presheaf.stalkSpecializes (genericPoint_specializes x)).hom.range
end Normal
section Localised
variable {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]
def localizedIn (p : Ideal A) [p.IsPrime] (M : Submodule A V) : Submodule A V where
  carrier := {v | ∃ s : A, s ∉ p ∧ s • v ∈ M}
  add_mem' := by
    rintro v w ⟨s, hs, hsv⟩ ⟨t, ht, htw⟩
    refine ⟨s * t, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hs ht, ?_⟩
    rw [smul_add]
    exact M.add_mem (by rw [mul_comm, mul_smul]; exact M.smul_mem t hsv)
      (by rw [mul_smul]; exact M.smul_mem s htw)
  zero_mem' := ⟨1, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩
  smul_mem' := by
    rintro a v ⟨s, hs, hsv⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem a hsv⟩
end Localised
section More
variable {X : Scheme.{0}}
@[reassoc (attr := simp)]
lemma toInvOpen_homOfLE (f : X ⟶ SpecZ) (R : Type) [CommRing R] {m m' : ℤ} (hm : IsUnit (m : R))
    (hm' : IsUnit (m' : R)) (h : invOpen f m ≤ invOpen f m') :
    toInvOpen f R m hm ≫ X.homOfLE h = toInvOpen f R m' hm' := by
  rw [← cancel_mono (invOpen f m').ι]
  simp [Scheme.homOfLE_ι]
def pullbackIsoAlong {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {F G : Z.Modules} (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (Scheme.Modules.pullback k).obj F ≅ (Scheme.Modules.pullback k).obj G :=
  pullbackCompIso e (Iso.refl _) ≪≫ (Scheme.Modules.pullback g).mapIso ψ ≪≫
    (pullbackCompIso e (Iso.refl _)).symm
def primeProd (S : Finset Nat.Primes) : ℤ := ∏ p ∈ S, ((p : ℕ) : ℤ)
lemma primeProd_ne_zero (S : Finset Nat.Primes) : primeProd S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ => by exact_mod_cast p.2.ne_zero
def Dominates (A : Type*) [CommRing A] [IsLocalRing A] {K : Type*} [Field K] [Algebra A K]
    (V : Subring K) : Prop :=
  ∃ hA : ∀ a : A, algebraMap A K a ∈ V,
    ∀ a : A, ¬ IsUnit (⟨algebraMap A K a, hA a⟩ : V) ↔ a ∈ IsLocalRing.maximalIdeal A
def blowUpChart {A : Type*} [CommRing A] (K : Type*) [Field K] [Algebra A K] {n : ℕ}
    (x : Fin n → A) (i : Fin n) : Subalgebra A K :=
  Algebra.adjoin A (Set.range fun j => algebraMap A K (x j) / algebraMap A K (x i))
def primeWeight (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)
def genericSpecMap (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] : Spec (CommRingCat.of L) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)) ≫ Z.fromSpecStalk (genericPoint Z)
end More
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
structure IsRegularSection {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) (b : K → ℤ) (f g : MRing ι F) : Prop where
  degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
  regular : ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W →
    ∃ u v : MRing ι F, u ∉ W ∧ u * f - v * g ∈ P
def SameRationalSpan {E : Type*} [AddCommGroup E] (L L' : AddSubgroup E) : Prop :=
  (∀ v ∈ L, ∃ N : ℕ, 0 < N ∧ N • v ∈ L') ∧ ∀ v ∈ L', ∃ N : ℕ, 0 < N ∧ N • v ∈ L
def DominatingDVR.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ¬ IsField A →
    ∀ (K : Type) [Field K] [Algebra A K] [IsFractionRing A K],
      ∃ V : Subring K, IsDiscreteValuationRing V ∧ Dominates A V
def DominatingDVRScheme.Statement : Prop :=
  ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (z : Z), z ≠ genericPoint Z →
    ∃ V : Subring Z.functionField, IsDiscreteValuationRing V ∧ Dominates (Z.presheaf.stalk z) V
def BlowUpChart.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (n : ℕ) (x : Fin n → A),
    Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A → (∃ j, x j ≠ 0) →
      ∃ i, x i ≠ 0 ∧ ¬ IsUnit (algebraMap A (blowUpChart K x i) (x i)) ∧
        ∃ Q : Ideal (blowUpChart K x i), Q.IsPrime ∧ algebraMap A _ (x i) ∈ Q ∧
          Q.comap (algebraMap A (blowUpChart K x i)) = IsLocalRing.maximalIdeal A
def KrullAkizuki.Statement : Prop :=
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
      [IsScalarTower R K L] (S : Subalgebra R L), IsNoetherianRing S ∧ ringKrullDim S ≤ 1) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K],
      IsDedekindDomain (integralClosure R K))
def HeightOneIntersection.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K],
    Subalgebra.toSubmodule (⊥ : Subalgebra A K) =
      ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        localizedIn p.asIdeal (Subalgebra.toSubmodule (⊥ : Subalgebra A K))
def LatticesAgree.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module A V]
    [IsScalarTower A K V] (M N : Submodule A V),
    Module.Finite A M → Module.Projective A M → Module.Finite A N → Module.Projective A N →
    Submodule.span K (M : Set V) = ⊤ → Submodule.span K (N : Set V) = ⊤ →
    (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → localizedIn p.asIdeal M = localizedIn p.asIdeal N) →
    M = N
def BundlesAgree.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], IsNormalScheme X →
    ∀ (E E' : X.Modules), IsVectorBundle E → IsVectorBundle E' →
    ∀ φ : E.presheaf.stalk (genericPoint X) ≃ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X),
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      (genericImage E x).map φ.toAddMonoidHom = genericImage E' x) →
    ∃! ψ : E ≅ E', ∀ v, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
      (Scheme.Modules.Hom.mapPresheaf ψ.hom)).hom v = φ v
def SpreadBundle.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules), IsVectorBundle E →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, m ∣ n → ∀ hn : ¬ ((p : ℕ) : ℤ) ∣ (n : ℤ),
      ∃ E' : (invOpen f n : Scheme.{0}).Modules, IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toInvOpen f (ZLoc p) n
          (isUnit_intCast_zLoc p n hn))).obj E' ≅ E)
def SpreadIso.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ α : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ≅
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ (m' : ℕ) (hm' : 0 < m') (ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a m'))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a m'))).obj G),
      pullbackIsoAlong (toInvOpen_homOfLE f ℚ
        (isUnit_intCast_rat ((a : ℤ) * m') (by positivity))
        (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a m')) ψ = α
def PrimeOpensCover.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (S : Finset Nat.Primes) (mp : Nat.Primes → ℤ),
    (∀ p ∈ S, ¬ ((p : ℕ) : ℤ) ∣ mp p) → (∀ p ∈ S, ∀ q ∈ S, q ≠ p → ((q : ℕ) : ℤ) ∣ mp p) →
    (invOpen f (primeProd S) ⊔ ⨆ p ∈ S, invOpen f (mp p) = ⊤) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
        invOpen f (mp p) ⊓ invOpen f (mp q) ≤ invOpen f (primeProd S) ∧
        invOpen f (mp p) ⊓ invOpen f (mp q) ≤ invOpen f (primeProd S * mp p)
def GlueBundles.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f]
    (S : Finset Nat.Primes) (E₀ : (invOpen f (primeProd S) : Scheme.{0}).Modules)
    (Ep : ∀ p : S, (baseChange f (ZLoc p)).Modules),
    IsVectorBundle E₀ → (∀ p, IsVectorBundle (Ep p)) →
    ∀ β : ∀ p : S, (Scheme.Modules.pullback (ratToLoc f p)).obj (Ep p) ≅
      (Scheme.Modules.pullback (toInvOpen f ℚ (primeProd S)
        (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj E₀,
    ∃ E : X.Modules, IsVectorBundle E ∧
      ∃ (γ₀ : (Scheme.Modules.pullback (invOpen f (primeProd S)).ι).obj E ≅ E₀)
        (γ : ∀ p : S, (Scheme.Modules.pullback (baseChangeMap f (ZLoc p))).obj E ≅ Ep p),
        ∀ p : S, pullbackCompIso (toInvOpen_ι f ℚ (primeProd S)
            (isUnit_intCast_rat _ (primeProd_ne_zero S))) γ₀ =
          pullbackCompIso (ratToLoc_baseChangeMap f p) (γ p) ≪≫ β p
def ChartGlue.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (τ : Type) [Finite τ] (x : τ → Ω) (r : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (S : Finset Nat.Primes)
    (o₀ : Type) [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
    (o : S → Type) [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
    [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
    [∀ p, Algebra (o p) Ω] (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E),
    (∀ p i, x i ≠ 0 → SameRationalSpan (B₀.lat i) ((Bp p).lat i)) →
    ∃ B : ChartBundle ℤ x r E, ∀ i, x i ≠ 0 →
      (∀ v, v ∈ B₀.lat i ↔ ∃ n : ℕ, primeProd S ^ n • v ∈ B.lat i) ∧
      ∀ (p : S) (v : E), v ∈ (Bp p).lat i ↔
        ∃ s : ℤ, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s ∧ s • v ∈ B.lat i
def ChartBundlesAgree.Statement : Prop :=
  ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (τ : Type) (x : τ → Ω) (r : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle o x r E) (i : τ), x i ≠ 0 →
    IsNoetherianRing (chartRing o x i) → IsIntegrallyClosed (chartRing o x i) →
    (∀ v ∈ B.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B'.lat i) →
    (∀ v ∈ B'.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B.lat i) →
    (∀ q : Ideal (chartRing o x i), q.IsPrime → q.height = 1 → ∀ v : E,
      (∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B.lat i) ↔
        ∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B'.lat i) →
    B.lat i = B'.lat i
def ClearDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [Flat f] [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules), IsVectorBundle L →
    ∀ s : Γ((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L, baseChangeMap f ℚ ⁻¹ᵁ ⊤),
      ∃ N : ℕ, 0 < N ∧ ∃ t : Γ(L, ⊤), pullSection (baseChangeMap f ℚ) L t = N • s
def SectionNef.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (F : Type) [Field F] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ringKrullDim (MRing ι F ⧸ P) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b : K → ℤ) (f g : MRing ι F), IsRegularSection P b f g → 0 ≤ intNum F P ![b]
def SectionNefGenerated.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (F : Type) [Field F] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ringKrullDim (MRing ι F ⧸ P) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ b : K → ℤ, (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W →
      ∃ f g : MRing ι F, IsRegularSection P b f g ∧
        ∃ u v : MRing ι F, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) →
      0 ≤ intNum F P ![b]
def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
    ∑ p ∈ (Finset.Iic ⌊B⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log B + C
def SumCp.Statement : Prop :=
  ∀ d : ℤ, d ≠ 0 → ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ S : Finset ℕ,
    (∀ p ∈ S, p.Prime ∧ ((p : ℝ) ≤ B ∨ (p : ℤ) ∣ d)) →
    ∑ p ∈ S, (primeWeight p + 2 * padicValInt p d) * Real.log p ≤ C * Real.log B
def FiniteIntegralClosure.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
    Module.Finite A (integralClosure A L)
def FiniteNormalization.Statement : Prop :=
  ∀ (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Type) [Field L] [Algebra Z.functionField L] [FiniteDimensional Z.functionField L],
    IsFinite (genericSpecMap Z L).fromNormalization
section Transport
universe u
variable {X Y : Scheme.{u}}
instance final_opensMap (f : X ⟶ Y) : (Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
set_option backward.isDefEq.respectTransparency.types false in

def pullbackStructureIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X :=
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)
end Transport
section Inhabitants
abbrev onePoint : Unit → ℚ := fun _ => 1
def awayToRat (m : ℤ) (hm : m ≠ 0) : Localization.Away m →+* ℚ :=
  IsLocalization.Away.lift m (g := Int.castRingHom ℚ) (isUnit_intCast_rat m hm)
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Model


