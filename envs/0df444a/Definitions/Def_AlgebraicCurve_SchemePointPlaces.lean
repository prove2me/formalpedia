-- Prove2me | Definitions.Def_AlgebraicCurve_SchemePointPlaces
-- name    : AlgebraicCurve_SchemePointPlaces
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:36.9326+00:00
-- url     : https://prove2.me/theorems/aed408b9-e4f7-4e75-b03e-535d16770a46
-- title:
--   Sections, closed points, stalks, and places on a smooth curve
-- statement:
--   For an integral curve $C$ smooth of relative dimension one over a field $K$, the file defines the structural maps $K→O_{C,x}→κ(x)$, the carriers of sections and rational closed points, and the place of $K(C)$ centered at a closed point. It identifies the stalk with that place's valuation ring and their residue fields as $K$-algebras, and packages inverse constructions between $K$-sections and closed points with residue field $K$. This supplies the scheme-point to degree-one-place bridge used for the canonical curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
/-! Centered places and their structurally linear stalk and residue identifications. -/
set_option backward.isDefEq.respectTransparency.types false

/-! ### Stalks at closed points

`closedPointPlace` chooses, for a closed point of a smooth integral curve, a place whose
valuation ring is the image of the stalk. That such a place exists rests on the stalk being a
discrete valuation ring, which comes from the local structure of standard smooth algebras of
relative dimension one; these facts are proved here because the definition depends on them. -/

section

universe u v

open IsLocalRing

attribute [local instance] Ideal.Quotient.field

namespace Algebra
namespace IsStandardSmoothOfRelativeDimension

private theorem isDomain_of_maximalIdeal_eq_span {L : Type*} [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] {ϖ : L} (hreg : IsSMulRegular L ϖ)
    (hmax : maximalIdeal L = Ideal.span {ϖ}) : IsDomain L := by
  classical
  have hpow : ∀ n : ℕ, maximalIdeal L ^ n = Ideal.span {ϖ ^ n} := fun n => by
    rw [hmax, Ideal.span_singleton_pow]
  have key : ∀ x : L, x ≠ 0 → ∃ (n : ℕ) (w : L), IsUnit w ∧ x = w * ϖ ^ n := by
    intro x hx
    have hex : ∃ n : ℕ, x ∉ maximalIdeal L ^ n := by
      by_contra! h
      apply hx
      have hmem : x ∈ ⨅ n : ℕ, maximalIdeal L ^ n := Ideal.mem_iInf.mpr h
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal L).ne_top,
        Ideal.mem_bot] at hmem
    have hn0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Ideal.one_eq_top] at this
      exact this trivial
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hxj : x ∈ maximalIdeal L ^ j := by
      have := Nat.find_min hex (m := j) (by omega)
      exact not_not.mp this
    have hxj1 : x ∉ maximalIdeal L ^ (j + 1) := hj ▸ Nat.find_spec hex
    rw [hpow] at hxj hxj1
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hxj
    refine ⟨j, w, ?_, rfl⟩
    by_contra hw
    apply hxj1
    have hw' : w ∈ maximalIdeal L := hw
    rw [hmax] at hw'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw'
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
  have : NoZeroDivisors L := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    obtain ⟨n, w, hw, rfl⟩ := key a h.1
    obtain ⟨m, w', hw', rfl⟩ := key b h.2
    have hreg' : IsSMulRegular L (ϖ ^ (n + m)) := hreg.pow (n + m)
    have h0 : ϖ ^ (n + m) • (w * w') = ϖ ^ (n + m) • (0 : L) := by
      rw [smul_eq_mul, smul_zero, ← hab]; ring
    exact (hw.mul hw').ne_zero (hreg' h0)⟩
  exact NoZeroDivisors.to_isDomain L

/-- A maximal localization of a standard smooth curve algebra over a field is a DVR. -/
private theorem isDiscreteValuationRing_localization_atPrime
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (p : Ideal A) [p.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime p), IsDiscreteValuationRing (Localization.AtPrime p) := by
  classical

  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k A
  let P := MvPolynomial (Fin 1) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : Algebra.Etale P A := hg
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm

  let e : P ≃ₐ[k] Polynomial k := MvPolynomial.uniqueAlgEquiv (R := k) (Fin 1)
  have : IsPrincipalIdealRing P := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  have hPnf : ¬ IsField P := fun h => Polynomial.not_isField (R := k) (e.symm.toMulEquiv.isField h)

  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing P A

  let q : Ideal P := p.under P
  have : Algebra.FiniteType k A :=
    (inferInstance : Algebra.FiniteType k P).trans (inferInstance : Algebra.FiniteType P A)
  have : Module.Finite k (A ⧸ p) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ p)
  have : Module.Finite k (P ⧸ q) :=
    FiniteDimensional.of_injective (IsScalarTower.toAlgHom k (P ⧸ q) (A ⧸ p)).toLinearMap
      (FaithfulSMul.algebraMap_injective (P ⧸ q) (A ⧸ p))
  have hqmax : q.IsMaximal := by
    refine Ideal.Quotient.maximal_of_isField _ ?_
    have : Algebra.IsIntegral k (P ⧸ q) := Algebra.IsIntegral.of_finite k _
    exact isField_of_isIntegral_of_isField' (R := k) (S := P ⧸ q) (Field.toIsField k)
  have hq0 : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hqmax hPnf
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal q).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hq0 (by rw [hπ]; simp)

  set L := Localization.AtPrime p
  let := Localization.AtPrime.algebraOfLiesOver q p
  have hmap : q.map (algebraMap P L) = maximalIdeal L :=
    ((Algebra.isUnramifiedAt_iff_map_eq (R := P) (p := q) (q := p)).mp inferInstance).2
  have hmaxL : maximalIdeal L = Ideal.span {algebraMap P L π} := by
    rw [← hmap, hπ]
    change Ideal.map (algebraMap P L) (Ideal.span {π}) = _
    rw [Ideal.map_span, Set.image_singleton]

  have : Module.Flat P L := Module.Flat.trans P A L
  have hreg : IsSMulRegular L (algebraMap P L π) := by
    have h : IsSMulRegular L π :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
    intro a b hab
    apply h
    simpa [Algebra.smul_def] using hab
  have hne : maximalIdeal L ≠ ⊥ := by
    rw [hmaxL, Ne, Ideal.span_singleton_eq_bot]
    intro h0
    have : (algebraMap P L π) • (1 : L) = (algebraMap P L π) • (0 : L) := by simp [h0]
    exact one_ne_zero (hreg this)
  have hnf : ¬ IsField L := fun hF => hne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)

  have hdom : IsDomain L := isDomain_of_maximalIdeal_eq_span hreg hmaxL
  have hprinc : (maximalIdeal L).IsPrincipal := ⟨⟨algebraMap P L π, hmaxL⟩⟩
  exact ⟨hdom, ((IsDiscreteValuationRing.TFAE L hnf).out 4 0).mp hprinc⟩

end Algebra.IsStandardSmoothOfRelativeDimension

end

section

universe u
open CategoryTheory AlgebraicGeometry IsLocalRing Topology

private theorem AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  classical

  obtain ⟨U, hU, V, hV, hxV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x

  have hfxU : f.base x ∈ U := hle hxV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (f.base x)]; exact hfxU

  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(X, V) := (f.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  let : Algebra k Γ(X, V) := ψ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(X, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ

  have hmax : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx

  obtain ⟨hdom, hdvr⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := k) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal

  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxV).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

end

section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing Topology

private theorem AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]
    (x : C) (a : K) :
    baseToFunctionField c a =
      algebraMap (C.presheaf.stalk x) C.functionField
        ((C.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))) := by
  have key : ∀ s : Γ(C, ⊤), (C.presheaf.germ ⊤ (genericPoint C) trivial).hom s =
      algebraMap (C.presheaf.stalk x) C.functionField ((C.presheaf.germ ⊤ x trivial).hom s) := by
    intro s
    simp_rw [RingHom.algebraMap_toAlgebra]
    change _ = (C.presheaf.germ ⊤ x trivial ≫ C.presheaf.stalkSpecializes _).hom s
    rw [C.presheaf.germ_stalkSpecializes]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  exact key _

private theorem AlgebraicCurve.exists_place_range_stalk_eq
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : IsClosed ({x} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ v : AlgebraicCurve.Place K C.functionField,
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by
  let := (baseToFunctionField c).toAlgebra
  have hdvr : IsDiscreteValuationRing (C.presheaf.stalk x) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c x hx
  set O := C.presheaf.stalk x with hO
  set F := C.functionField with hF

  let A : ValuationSubring F := (ValuationRing.valuation O F).valuationSubring
  have hA : (algebraMap O F).range = A.toSubring := by
    ext f
    change f ∈ (algebraMap O F).range ↔ f ∈ (ValuationRing.valuation O F).integer
    rw [ValuationRing.range_algebraMap_eq]
  have hmemA : ∀ f : F, f ∈ A ↔ ∃ a : O, algebraMap O F a = f := fun f =>
    ValuationRing.mem_integer_iff O F f

  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  let e : O ≃+* A :=
    RingEquiv.ofBijective
      ((algebraMap O F).codRestrict A.toSubring fun a => by
        rw [← hA]; exact ⟨a, rfl⟩)
      ⟨fun a b hab => hinj (congrArg Subtype.val hab),
        fun ⟨f, hf⟩ => by
          obtain ⟨a, rfl⟩ := (hmemA f).mp hf
          exact ⟨a, rfl⟩⟩
  refine ⟨⟨A, ?_, ?_, ?_⟩, hA⟩
  ·
    intro a
    rw [hmemA]
    exact ⟨_, (baseToFunctionField_apply_eq_algebraMap_stalk c x a).symm⟩
  ·
    intro htop
    apply IsDiscreteValuationRing.not_isField O
    have hsurj : Function.Surjective (algebraMap O F) := by
      intro f
      have hf : f ∈ A := by rw [htop]; trivial
      exact (hmemA f).mp hf
    exact (RingEquiv.ofBijective (algebraMap O F) ⟨hinj, hsurj⟩).toMulEquiv.isField
      (Field.toIsField F)
  ·
    exact IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective


end

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory
namespace AlgebraicCurve

/-- The coefficient map to a stalk induced by the selected scheme structure map. -/
def stalkBaseMap {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (x : C) : K →+* C.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
    C.presheaf.germ ⊤ x trivial).hom

/-- The coefficient map to a residue field induced by the selected structure map. -/
def residueBaseMap {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (x : C) : K →+* C.residueField x :=
  (C.residue x).hom.comp (stalkBaseMap c x)

/-- Sections of a scheme's selected structure morphism over its coefficient field. -/
abbrev SchemeSection {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) :=
  {s : Spec (CommRingCat.of K) ⟶ C // s ≫ c = 𝟙 _}

/-- Closed points whose structural residue map is onto the entire residue field. -/
abbrev RationalClosedPoint {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) :=
  {x : closedPoints C // Function.Surjective (residueBaseMap c x.val)}

variable {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [SmoothOfRelativeDimension 1 c]

/-- A closed point's place on the actual scheme function field. -/
def closedPointPlace (x : closedPoints C) :
    letI := (baseToFunctionField c).toAlgebra
    Place K C.functionField := by
  letI := (baseToFunctionField c).toAlgebra
  exact Classical.choose (exists_place_range_stalk_eq c x.val x.property)

/-- The chosen place has exactly the image of the point's stalk as its valuation ring. -/
theorem closedPointPlace_range (x : closedPoints C) :
    letI := (baseToFunctionField c).toAlgebra
    (algebraMap (C.presheaf.stalk x.val) C.functionField).range =
      (closedPointPlace c x).toValuationSubring.toSubring := by
  let := (baseToFunctionField c).toAlgebra
  exact Classical.choose_spec (exists_place_range_stalk_eq c x.val x.property)

/-- The stalk identifies with the chosen valuation ring through its actual field inclusion. -/
def closedPointStalkRingEquiv (x : closedPoints C) :
    letI := (baseToFunctionField c).toAlgebra
    C.presheaf.stalk x.val ≃+* (closedPointPlace c x).toValuationSubring := by
  letI := (baseToFunctionField c).toAlgebra
  let O := C.presheaf.stalk x.val
  let v := closedPointPlace c x
  let f : O →+* v.toValuationSubring :=
    (algebraMap O C.functionField).codRestrict v.toValuationSubring.toSubring (fun a => by
      rw [← closedPointPlace_range c x]
      exact ⟨a, rfl⟩)
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    exact IsFractionRing.injective O C.functionField (congrArg Subtype.val hab)
  · intro a
    have hmem : (a : C.functionField) ∈ (algebraMap O C.functionField).range := by
      rw [closedPointPlace_range c x]
      exact a.property
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, Subtype.ext hb⟩

/-- The ring equivalence fixes the actual image of every stalk element in the function field. -/
theorem closedPointStalkRingEquiv_coe (x : closedPoints C) (a : C.presheaf.stalk x.val) :
    letI := (baseToFunctionField c).toAlgebra
    ((closedPointStalkRingEquiv c x a : (closedPointPlace c x).toValuationSubring) : C.functionField) =
      algebraMap (C.presheaf.stalk x.val) C.functionField a := rfl

/-- The stalk identification preserves the structural coefficient action. -/
def closedPointStalkAlgEquiv (x : closedPoints C) :
    letI := (baseToFunctionField c).toAlgebra
    letI := (stalkBaseMap c x.val).toAlgebra
    C.presheaf.stalk x.val ≃ₐ[K] (closedPointPlace c x).toValuationSubring := by
  letI := (baseToFunctionField c).toAlgebra
  letI := (stalkBaseMap c x.val).toAlgebra
  apply AlgEquiv.ofRingEquiv (f := closedPointStalkRingEquiv c x)
  intro a
  apply Subtype.ext
  rw [closedPointStalkRingEquiv_coe]
  exact (baseToFunctionField_apply_eq_algebraMap_stalk c x.val a).symm

/-- The residue-field equivalence is linear for the structural coefficient actions. -/
def closedPointPlaceResidueAlgEquiv (x : closedPoints C) :
    letI := (baseToFunctionField c).toAlgebra
    letI := (stalkBaseMap c x.val).toAlgebra
    letI := (residueBaseMap c x.val).toAlgebra
    C.residueField x.val ≃ₐ[K] (closedPointPlace c x).ResidueField := by
  letI := (baseToFunctionField c).toAlgebra
  letI := (stalkBaseMap c x.val).toAlgebra
  letI := (residueBaseMap c x.val).toAlgebra
  let E := closedPointStalkAlgEquiv c x
  apply AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv E.toRingEquiv)
  intro a
  show IsLocalRing.ResidueField.mapEquiv E.toRingEquiv
      (IsLocalRing.residue (C.presheaf.stalk x.val) (algebraMap K _ a)) =
    IsLocalRing.residue (closedPointPlace c x).toValuationSubring (algebraMap K _ a)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue (closedPointPlace c x).toValuationSubring) (E.commutes a)

end AlgebraicCurve

end

/-! Structural residue maps and rational scheme sections over arbitrary fields. -/
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory
namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))

/-- The local structural coefficient map gives the actual composition from the stalk spectrum. -/
theorem fromSpecStalk_toBase (x : C) :
    C.fromSpecStalk x ≫ c = Spec.map (CommRingCat.ofHom (stalkBaseMap c x)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  have htop : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [htop, CategoryTheory.Functor.map_id, Category.comp_id]
  have hmap : (Spec.map (CommRingCat.ofHom (stalkBaseMap c x))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
        CommRingCat.ofHom (stalkBaseMap c x) ≫
          (Scheme.ΓSpecIso (C.presheaf.stalk x)).inv := by
    rw [← Iso.inv_comp_eq]
    exact (Scheme.ΓSpecIso_inv_naturality _).symm
  rw [hmap]
  simp only [stalkBaseMap, CommRingCat.ofHom_hom, Category.assoc, Iso.hom_inv_id_assoc]

/-- The residue structural map gives the actual composition from the residue-field spectrum. -/
theorem fromSpecResidueField_toBase (x : C) :
    C.fromSpecResidueField x ≫ c = Spec.map (CommRingCat.ofHom (residueBaseMap c x)) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, fromSpecStalk_toBase, ← Spec.map_comp]
  rfl

/-- A scheme section is a closed immersion because its source spectrum is a singleton. -/
theorem schemeSection_isClosedImmersion (s : SchemeSection c) : IsClosedImmersion s.val :=
  isClosedImmersion_of_comp_eq_id c s.val s.property

/-- A rational scheme section has a closed image point over any coefficient field. -/
theorem schemeSection_point_isClosed (s : SchemeSection c) :
    IsClosed ({s.val (IsLocalRing.closedPoint K)} : Set C) := by
  letI := schemeSection_isClosedImmersion c s
  have hrange : Set.range s.val.base = {s.val (IsLocalRing.closedPoint K)} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint K)]
      exact Set.mem_singleton _
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨IsLocalRing.closedPoint K, hx.symm⟩
  rw [← hrange]
  exact s.val.isClosedEmbedding.isClosed_range

/-- The field map supplied by a section is a left inverse to the structural residue map. -/
theorem schemeSection_residue_comp (s : SchemeSection c) :
    CommRingCat.ofHom (residueBaseMap c (s.val (IsLocalRing.closedPoint K))) ≫
      C.descResidueField (Scheme.stalkClosedPointTo s.val) = 𝟙 (CommRingCat.of K) := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_id, ← fromSpecResidueField_toBase]
  rw [← Category.assoc, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
  exact s.property

/-- A section identifies its point residue field with K through the structural K-action. -/
def schemeSectionResidueAlgEquiv (s : SchemeSection c) :
    letI := (stalkBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
    letI := (residueBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
    C.residueField (s.val (IsLocalRing.closedPoint K)) ≃ₐ[K] K := by
  letI := (stalkBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
  letI := (residueBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
  let g := C.descResidueField (Scheme.stalkClosedPointTo s.val)
  have hcomp (a : K) : g.hom (residueBaseMap c (s.val (IsLocalRing.closedPoint K)) a) = a := by
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom a)
      (schemeSection_residue_comp c s)
  let G : C.residueField (s.val (IsLocalRing.closedPoint K)) →ₐ[K] K :=
    { toRingHom := g.hom
      commutes' := fun a => hcomp a }
  exact AlgEquiv.ofBijective G
    ⟨g.hom.injective, fun a => ⟨residueBaseMap c (s.val (IsLocalRing.closedPoint K)) a, hcomp a⟩⟩

/-- The structural residue map at a section's image is surjective. -/
theorem schemeSection_residueBaseMap_surjective (s : SchemeSection c) :
    Function.Surjective (residueBaseMap c (s.val (IsLocalRing.closedPoint K))) := by
  letI := (stalkBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
  letI := (residueBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
  let E := schemeSectionResidueAlgEquiv c s
  intro b
  refine ⟨E b, E.injective ?_⟩
  exact E.commutes (E b)

end AlgebraicCurve

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K))

/-- The structural residue map at a rational closed point is a field isomorphism. -/
def rationalClosedPointResidueAlgEquiv (x : closedPoints C)
    (hx : Function.Surjective (residueBaseMap c x.val)) :
    letI := (stalkBaseMap c x.val).toAlgebra
    letI := (residueBaseMap c x.val).toAlgebra
    C.residueField x.val ≃ₐ[K] K := by
  letI := (stalkBaseMap c x.val).toAlgebra
  letI := (residueBaseMap c x.val).toAlgebra
  let E := RingEquiv.ofBijective (residueBaseMap c x.val)
    ⟨(residueBaseMap c x.val).injective, hx⟩
  exact AlgEquiv.ofRingEquiv (f := E.symm) (fun a => E.symm_apply_apply a)

/-- A rational closed point gives a section through its structural residue inverse. -/
def schemeSectionOfRationalClosedPoint (x : RationalClosedPoint c) : SchemeSection c := by
  letI := (stalkBaseMap c x.val.val).toAlgebra
  letI := (residueBaseMap c x.val.val).toAlgebra
  let E := rationalClosedPointResidueAlgEquiv c x.val x.property
  refine ⟨Spec.map (CommRingCat.ofHom E.toRingHom) ≫ C.fromSpecResidueField x.val.val, ?_⟩
  rw [Category.assoc, fromSpecResidueField_toBase, ← Spec.map_comp]
  have heq : CommRingCat.ofHom (residueBaseMap c x.val.val) ≫
      CommRingCat.ofHom E.toRingHom = 𝟙 (CommRingCat.of K) := by
    ext a
    exact E.commutes a
  rw [heq, Spec.map_id]

/-- A section gives a rational closed point, preserving its actual image point. -/
def schemeSectionRationalClosedPoint (s : SchemeSection c) : RationalClosedPoint c :=
  ⟨⟨s.val (IsLocalRing.closedPoint K), schemeSection_point_isClosed c s⟩,
    schemeSection_residueBaseMap_surjective c s⟩

/-- The section constructed from a rational closed point has that same image. -/
theorem schemeSectionRationalClosedPoint_ofRational (x : RationalClosedPoint c) :
    schemeSectionRationalClosedPoint c (schemeSectionOfRationalClosedPoint c x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  letI := (stalkBaseMap c x.val.val).toAlgebra
  letI := (residueBaseMap c x.val.val).toAlgebra
  let E := rationalClosedPointResidueAlgEquiv c x.val x.property
  change (Spec.map (CommRingCat.ofHom E.toRingHom) ≫ C.fromSpecResidueField x.val.val)
      (IsLocalRing.closedPoint K) = x.val.val
  simp only [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

/-- A section is uniquely recovered from its image and its structural residue inverse. -/
theorem schemeSectionOfRationalClosedPoint_ofSection (s : SchemeSection c) :
    schemeSectionOfRationalClosedPoint c (schemeSectionRationalClosedPoint c s) = s := by
  apply Subtype.ext
  apply (Scheme.SpecToEquivOfField K C).injective
  letI := (stalkBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
  letI := (residueBaseMap c (s.val (IsLocalRing.closedPoint K))).toAlgebra
  let x := schemeSectionRationalClosedPoint c s
  letI := (stalkBaseMap c x.val.val).toAlgebra
  letI := (residueBaseMap c x.val.val).toAlgebra
  let E := rationalClosedPointResidueAlgEquiv c x.val x.property
  change (Scheme.SpecToEquivOfField K C)
      ((Scheme.SpecToEquivOfField K C).symm
        ⟨s.val (IsLocalRing.closedPoint K), CommRingCat.ofHom E.toRingHom⟩) = _
  rw [Equiv.apply_symm_apply]
  change (⟨s.val (IsLocalRing.closedPoint K), CommRingCat.ofHom E.toRingHom⟩ :
      Σ y : C, C.residueField y ⟶ CommRingCat.of K) =
    ⟨s.val (IsLocalRing.closedPoint K), C.descResidueField (Scheme.stalkClosedPointTo s.val)⟩
  apply congrArg (fun g : C.residueField (s.val (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K =>
    (⟨s.val (IsLocalRing.closedPoint K), g⟩ : Σ y : C, C.residueField y ⟶ CommRingCat.of K))
  apply CommRingCat.hom_ext
  ext b
  obtain ⟨a, ha⟩ := schemeSection_residueBaseMap_surjective c s b
  rw [← ha]
  have hcomp := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom a)
    (schemeSection_residue_comp c s)
  exact (E.commutes a).trans hcomp.symm

/-- Rational scheme sections correspond exactly to closed points with residue field K. -/
def schemeSectionRationalClosedPointEquiv : SchemeSection c ≃ RationalClosedPoint c where
  toFun := schemeSectionRationalClosedPoint c
  invFun := schemeSectionOfRationalClosedPoint c
  left_inv := schemeSectionOfRationalClosedPoint_ofSection c
  right_inv := schemeSectionRationalClosedPoint_ofRational c

end AlgebraicCurve

end

/-! ### Closed points versus places

The closed-point/place correspondence below needs four facts about a smooth proper integral curve:
every stalk is a valuation ring, a non-generic point is closed, properness gives a closed center to
every place, and a point is determined by the image of its stalk. They are proved here, privately,
because the definitions `closedPointPlaceEquiv` and `rationalClosedPointPlaceEquiv` depend on them. -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing Topology

namespace SmoothCurveStalk

private theorem valuationRing_of_surjective {A B : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) (hf : Function.Surjective f) : ValuationRing B := by
  have : PreValuationRing B := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    obtain ⟨c, h | h⟩ := ValuationRing.cond a b
    · exact ⟨f c, Or.inl (by rw [← map_mul, h])⟩
    · exact ⟨f c, Or.inr (by rw [← map_mul, h])⟩⟩
  exact ⟨⟩

private theorem valuationRing_localization_atPrime {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [IsDomain B] [IsNoetherianRing B] [Algebra.EssFiniteType R B]
    (q : Ideal B) [q.IsPrime] [Algebra.IsUnramifiedAt R q] (hp : (q.under R).IsPrincipal) :
    ValuationRing (Localization.AtPrime q) := by
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hprinc : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).IsPrincipal := by
    rw [← hmap]
    obtain ⟨π, hπ⟩ := hp
    refine ⟨⟨algebraMap R _ π, ?_⟩⟩
    rw [hπ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
      Ideal.submodule_span_eq]
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (Localization.AtPrime q)).out 4 1).mp hprinc

private theorem isPrincipalIdealRing_mvPolynomial_fin_one (K : Type*) [Field K] :
    IsPrincipalIdealRing (MvPolynomial (Fin 1) K) :=
  let e : MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective

end SmoothCurveStalk

open SmoothCurveStalk in
private theorem AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] (x : C) :
    ValuationRing (C.presheaf.stalk x) := by

  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) x

  have hU' : U = ⊤ := top_unique fun y _ => by
    haveI : Subsingleton ↥(Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim y (c x)]
    exact e hxV
  subst hU'
  let ι : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  have hφ : ((c.appLE ⊤ V e).hom.comp ι.toRingHom).IsStandardSmoothOfRelativeDimension 1 := by
    simpa using hstd.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv ι)

  obtain ⟨g, -, hg⟩ := hφ.exists_etale_mvPolynomial
  algebraize [g]

  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : IsDomain Γ(C, V) := IsIntegral.component_integral V
  haveI : IsNoetherianRing Γ(C, V) :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial (Fin 1) K) Γ(C, V)
  haveI := isPrincipalIdealRing_mvPolynomial_fin_one K
  let q : Ideal Γ(C, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hq : ValuationRing (Localization.AtPrime q) :=
    valuationRing_localization_atPrime (R := MvPolynomial (Fin 1) K) q
      (IsPrincipalIdealRing.principal _)

  show ValuationRing (C.presheaf.stalk ((⟨x, hxV⟩ : V) : C))
  letI := C.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  let eqv := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (C.presheaf.stalk ((⟨x, hxV⟩ : V) : C))
  exact valuationRing_of_surjective eqv.toRingEquiv.toRingHom eqv.surjective

private theorem Algebra.IsStandardSmoothOfRelativeDimension.isMaximal_of_isPrime_of_ne_bot
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (q : Ideal A) [hq : q.IsPrime] (hq0 : q ≠ ⊥) : q.IsMaximal := by
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q hq.ne_top
  obtain ⟨_, hdvr⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
      (k := k) m

  have hdisj : Disjoint (m.primeCompl : Set A) q := by
    rw [Set.disjoint_left]; intro a ha haq; exact ha (hqm haq)
  haveI hq' : (q.map (algebraMap A (Localization.AtPrime m))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ q hq hdisj
  have hinj := IsLocalization.injective (Localization.AtPrime m) m.primeCompl_le_nonZeroDivisors
  have hq'0 : q.map (algebraMap A (Localization.AtPrime m)) ≠ ⊥ := by
    intro h
    apply hq0
    refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
    have hmem : algebraMap A (Localization.AtPrime m) a ∈ q.map (algebraMap A _) :=
      Ideal.mem_map_of_mem _ ha
    rw [h, Ideal.mem_bot] at hmem
    exact (injective_iff_map_eq_zero _).mp hinj a hmem
  have hmax' : (q.map (algebraMap A (Localization.AtPrime m))).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hq'0 hq'
  have heq : q.map (algebraMap A (Localization.AtPrime m)) = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal hmax'

  have : q = m := by
    refine le_antisymm hqm fun a ha => ?_
    have h1 := IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m)
      hq hdisj
    have hmem : a ∈ Ideal.comap (algebraMap A (Localization.AtPrime m))
        (q.map (algebraMap A (Localization.AtPrime m))) := by
      rw [Ideal.mem_comap, heq]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m a).mpr ha
    exact h1.le hmem
  exact this ▸ hm

private theorem AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : x ≠ genericPoint C) : IsClosed ({x} : Set C) := by
  classical
  rw [← closure_subset_iff_isClosed]
  intro y hy

  obtain ⟨U, hU, V, hV, hyV, hle, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) y
  have hxV : x ∈ V := by
    obtain ⟨w, hwV, hwx⟩ := mem_closure_iff.mp hy V V.isOpen hyV
    rw [Set.mem_singleton_iff] at hwx
    exact hwx ▸ hwV

  have hcyU : c.base y ∈ U := hle hyV
  obtain rfl : U = ⊤ := top_le_iff.mp fun w _ => by
    rw [Subsingleton.elim w (c.base y)]; exact hcyU
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(C, V) := (c.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e hstd
  letI : Algebra K Γ(C, V) := ψ.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(C, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hψ
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩

  set qx := hV.primeIdealOf ⟨x, hxV⟩ with hqx
  set qy := hV.primeIdealOf ⟨y, hyV⟩ with hqy

  have hspec : (⟨x, hxV⟩ : V) ⤳ ⟨y, hyV⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp (specializes_iff_mem_closure.mpr hy)
  have hle' : qx.asIdeal ≤ qy.asIdeal :=
    (PrimeSpectrum.le_iff_specializes qx qy).mpr (hspec.map hV.isoSpec.hom.base.hom.continuous)

  have hinj : Function.Injective (hV.isoSpec.hom.base) := (Scheme.homeoOfIso hV.isoSpec).injective
  have hqx0 : qx.asIdeal ≠ ⊥ := by
    intro h0
    apply hx
    have h1 : qx = genericPoint (Spec Γ(C, V)) := by
      rw [genericPoint_eq_bot_of_affine]; exact PrimeSpectrum.ext h0
    rw [← hV.primeIdealOf_genericPoint] at h1
    exact congrArg Subtype.val (hinj h1)

  have hqxmax : qx.asIdeal.IsMaximal :=
    Algebra.IsStandardSmoothOfRelativeDimension.isMaximal_of_isPrime_of_ne_bot (k := K) _ hqx0
  have hqq : qx = qy := PrimeSpectrum.ext (hqxmax.eq_of_le qy.isPrime.ne_top hle')
  have hxy : (⟨x, hxV⟩ : V) = ⟨y, hyV⟩ := hinj hqq
  rw [Set.mem_singleton_iff]
  exact (congrArg Subtype.val hxy).symm

namespace AlgebraicCurve

private theorem exists_lift_of_valuationSubring
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c]
    (R : ValuationSubring C.functionField) (hK : ∀ a : K, baseToFunctionField c a ∈ R) :
    ∃ ℓ : Spec (CommRingCat.of R) ⟶ C,
      Spec.map (CommRingCat.ofHom (algebraMap R C.functionField)) ≫ ℓ =
        C.fromSpecStalk (genericPoint C) ∧
      ℓ ≫ c = Spec.map (CommRingCat.ofHom ((baseToFunctionField c).codRestrict R hK)) := by
  classical
  set η := genericPoint C with hη
  let A : CommRingCat.of R ⟶ C.presheaf.stalk η :=
    CommRingCat.ofHom (algebraMap R C.functionField)
  let B : CommRingCat.of K ⟶ CommRingCat.of R :=
    CommRingCat.ofHom ((baseToFunctionField c).codRestrict R hK)
  have hBA : B ≫ A = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
      C.presheaf.germ ⊤ η trivial := by
    ext a
    rfl

  have w : C.fromSpecStalk η ≫ c = Spec.map A ≫ Spec.map B := by
    apply ext_of_isAffine
    rw [← Spec.map_comp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
    have h1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk η)).Opens) ≤ ⊤)).op = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [h1, CategoryTheory.Functor.map_id, Category.comp_id]

    have h2 : (Spec.map (B ≫ A)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ (B ≫ A) ≫
          (Scheme.ΓSpecIso (C.presheaf.stalk η)).inv := by
      rw [← Iso.inv_comp_eq]
      exact (Scheme.ΓSpecIso_inv_naturality (B ≫ A)).symm
    rw [h2, hBA]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

  have hvc : ValuativeCriterion c := by
    have h : IsProper c := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨ℓ, hl₁, hl₂⟩ := (hvc.existence ⟨R, C.functionField, C.fromSpecStalk η, Spec.map B, ⟨w⟩⟩).exists_lift
  dsimp only at hl₁ hl₂
  exact ⟨ℓ, hl₁, hl₂⟩

end AlgebraicCurve

private theorem _root_.ValuationSubring.eq_of_le_of_isUnit_imp {F : Type*} [Field F]
    {S R : ValuationSubring F} (hle : S ≤ R)
    (hunit : ∀ s : S, IsUnit (⟨(s : F), hle s.2⟩ : R) → IsUnit s) : S = R := by
  refine le_antisymm hle fun r hr => ?_
  by_contra hrS
  have hr0 : r ≠ 0 := by rintro rfl; exact hrS S.zero_mem
  have hinv : r⁻¹ ∈ S := (S.mem_or_inv_mem r).resolve_left hrS
  have hu : IsUnit (⟨r⁻¹, hle hinv⟩ : R) :=
    isUnit_iff_exists_inv.mpr ⟨⟨r, hr⟩, Subtype.ext (inv_mul_cancel₀ hr0)⟩
  obtain ⟨w, hw⟩ := hunit ⟨r⁻¹, hinv⟩ hu

  have : ((w⁻¹ : Sˣ) : S).1 = r := by
    have h1 : ((w⁻¹ : Sˣ) : S).1 * r⁻¹ = 1 := by
      have := congrArg (fun t : S => t.1) (w.inv_mul)
      simpa [hw] using this
    field_simp at h1
    linear_combination h1
  exact hrS (this ▸ ((w⁻¹ : Sˣ) : S).2)


private theorem AlgebraicCurve.exists_closedPoint_range_stalk_eq
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ v : AlgebraicCurve.Place K C.functionField, ∃ x : C, IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by
  letI := (baseToFunctionField c).toAlgebra
  intro v
  classical
  set R := v.toValuationSubring with hRdef
  have hK : ∀ a : K, baseToFunctionField c a ∈ R := v.algebraMap_mem'
  obtain ⟨ℓ, hl₁, -⟩ := exists_lift_of_valuationSubring c R hK
  set x := ℓ.base (closedPoint R) with hxdef
  have hgen : genericPoint C ⤳ x := (genericPoint_spec C).specializes trivial

  set φ := Scheme.stalkClosedPointTo ℓ with hφdef
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap R C.functionField) =
      C.presheaf.stalkSpecializes hgen := by
    apply Spec.map_injective
    rw [← cancel_mono (C.fromSpecStalk x), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hφ' : ∀ s, algebraMap R C.functionField (φ.hom s) =
      algebraMap (C.presheaf.stalk x) C.functionField s := by
    intro s
    have := congrArg (fun g => g.hom s) hφ
    simp at this
    exact this

  haveI : ValuationRing (C.presheaf.stalk x) :=
    AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one c x
  let S : ValuationSubring C.functionField :=
    (ValuationRing.valuation (C.presheaf.stalk x) C.functionField).valuationSubring
  have hS : ∀ f, f ∈ S ↔ ∃ a, algebraMap (C.presheaf.stalk x) C.functionField a = f := fun f =>
    ValuationRing.mem_integer_iff (C.presheaf.stalk x) C.functionField f
  have hSR : S ≤ R := by
    intro f hf
    obtain ⟨a, rfl⟩ := (hS f).mp hf
    rw [← hφ' a]
    exact (φ.hom a).2
  let ψ : C.presheaf.stalk x →+* S :=
    (algebraMap (C.presheaf.stalk x) C.functionField).codRestrict S fun a => (hS _).mpr ⟨a, rfl⟩
  have hunit : ∀ s : S, IsUnit (⟨(s : C.functionField), hSR s.2⟩ : R) → IsUnit s := by
    rintro ⟨f, hf⟩ hu
    obtain ⟨a, rfl⟩ := (hS f).mp hf
    have hu' : IsUnit (φ.hom a) := by
      have heq : φ.hom a = ⟨algebraMap (C.presheaf.stalk x) C.functionField a, hSR hf⟩ :=
        Subtype.ext (hφ' a)
      rwa [heq]
    have ha : IsUnit a := isUnit_of_map_unit φ.hom a hu'
    exact ha.map ψ
  have hSReq : S = R := ValuationSubring.eq_of_le_of_isUnit_imp hSR hunit
  have hrange : (algebraMap (C.presheaf.stalk x) C.functionField).range = R.toSubring := by
    rw [← hSReq]
    ext f
    rw [RingHom.mem_range]
    exact (hS f).symm

  have key : ∀ y : C, y = genericPoint C →
      (algebraMap (C.presheaf.stalk y) C.functionField).range = ⊤ := by
    rintro y rfl
    refine eq_top_iff.mpr fun f _ => ⟨f, ?_⟩
    change (C.presheaf.stalkSpecializes (specializes_refl _)).hom f = f
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hxη : x ≠ genericPoint C := by
    intro hx
    apply v.ne_top'
    apply ValuationSubring.toSubring_injective
    change R.toSubring = _
    rw [← hrange, key x hx]
    rfl
  exact ⟨x, isClosed_singleton_of_ne_genericPoint c x hxη, hrange⟩


private theorem AlgebraicCurve.eq_of_range_stalk_eq
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (x y : C)
    (h : (algebraMap (C.presheaf.stalk x) C.functionField).range =
      (algebraMap (C.presheaf.stalk y) C.functionField).range) :
    x = y := by

  haveI : C.IsSeparated := ⟨by
    rw [show terminal.from C = c ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  set O := C.presheaf.stalk x with hOdef
  set O' := C.presheaf.stalk y with hO'def
  set F := C.functionField with hFdef
  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  have hinj' : Function.Injective (algebraMap O' F) := IsFractionRing.injective O' F

  let eO : O ≃+* (algebraMap O F).range :=
    RingEquiv.ofBijective (algebraMap O F).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  let eO' : O' ≃+* (algebraMap O' F).range :=
    RingEquiv.ofBijective (algebraMap O' F).rangeRestrict
      ⟨fun a b hab => hinj' (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  let eh : (algebraMap O' F).range ≃+* (algebraMap O F).range := RingEquiv.subringCongr h.symm
  let e : O' ≃+* O := eO'.trans (eh.trans eO.symm)
  have he : ∀ a : O', algebraMap O F (e a) = algebraMap O' F a := by
    intro a
    have h1 : ∀ b : (algebraMap O F).range, algebraMap O F (eO.symm b) = (b : F) := by
      intro b
      exact congrArg Subtype.val (eO.apply_symm_apply b)
    change algebraMap O F (eO.symm (eh (eO' a))) = _
    rw [h1]
    rfl

  have hηx : genericPoint C ⤳ x := (genericPoint_spec C).specializes trivial
  have hηy : genericPoint C ⤳ y := (genericPoint_spec C).specializes trivial
  have halgx : algebraMap O F = (C.presheaf.stalkSpecializes hηx).hom :=
    RingHom.algebraMap_toAlgebra _
  have halgy : algebraMap O' F = (C.presheaf.stalkSpecializes hηy).hom :=
    RingHom.algebraMap_toAlgebra _

  let α : Spec O ⟶ C := C.fromSpecStalk x
  let β : Spec O ⟶ C := Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk y
  let ι : Spec F ⟶ Spec O := Spec.map (C.presheaf.stalkSpecializes hηx)
  haveI : IsDominant ι := ⟨by
    have hpt : ∀ p : Spec F, ι.base p = genericPoint (Spec O) := by
      intro p
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      change Ideal.comap (C.presheaf.stalkSpecializes hηx).hom p.asIdeal = ⊥
      have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime p.asIdeal
      rw [hp, ← RingHom.ker_eq_comap_bot, ← halgx]
      exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
    have hmem : genericPoint (Spec O) ∈ Set.range ι.base :=
      ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), hpt _⟩
    have hd : Dense ({genericPoint (Spec O)} : Set (Spec O)) :=
      dense_iff_closure_eq.mpr (genericPoint_closure (Spec O))
    exact hd.mono (Set.singleton_subset_iff.mpr hmem)⟩

  have hιe : ι ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
      = Spec.map (C.presheaf.stalkSpecializes hηy) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    change (C.presheaf.stalkSpecializes hηx).hom (e a) = (C.presheaf.stalkSpecializes hηy).hom a
    rw [← halgx, ← halgy]
    exact he a
  have hagree : ι ≫ α = ι ≫ β := by
    change ι ≫ C.fromSpecStalk x
      = ι ≫ (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk y)
    rw [← Category.assoc, hιe, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hαβ : α = β := ext_of_isDominant ι hagree

  haveI : IsLocalHom e.toRingHom :=
    ⟨fun a ha => (isLocalHom_equiv e).map_nonunit a ha⟩
  have hcl : (Spec.map (CommRingCat.ofHom e.toRingHom)).base (IsLocalRing.closedPoint O)
      = IsLocalRing.closedPoint O' := by
    change PrimeSpectrum.comap e.toRingHom (IsLocalRing.closedPoint O) = _
    exact IsLocalRing.comap_closedPoint e.toRingHom
  have h1 : α.base (IsLocalRing.closedPoint O) = x := Scheme.fromSpecStalk_closedPoint
  have h2 : β.base (IsLocalRing.closedPoint O) = y := by
    change (C.fromSpecStalk y).base
      ((Spec.map (CommRingCat.ofHom e.toRingHom)).base (IsLocalRing.closedPoint O)) = y
    rw [hcl]
    exact Scheme.fromSpecStalk_closedPoint
  rw [← h1, ← h2, hαβ]

private theorem AlgebraicCurve.Place.isRational_iff_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := by
  constructor
  · intro hv
    have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
      ⟨v.algebraMap_residueField_injective, hv⟩
    show Module.finrank K v.ResidueField = 1
    rw [← Module.finrank_self K]
    exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm
  · intro h x
    have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
    have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
      rw [hbot]
      exact Algebra.mem_top
    exact Algebra.mem_bot.mp hx

end

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c]

/-- Distinct closed points have distinct centered valuation rings. -/
theorem closedPointPlace_injective :
    letI := (baseToFunctionField c).toAlgebra
    Function.Injective (closedPointPlace c) := by
  letI := (baseToFunctionField c).toAlgebra
  intro x y h
  apply Subtype.ext
  apply eq_of_range_stalk_eq c
  rw [closedPointPlace_range c x, closedPointPlace_range c y, h]

/-- Properness supplies a closed center for every place, including boundary places. -/
theorem closedPointPlace_surjective :
    letI := (baseToFunctionField c).toAlgebra
    Function.Surjective (closedPointPlace c) := by
  letI := (baseToFunctionField c).toAlgebra
  intro v
  obtain ⟨x, hx, hrange⟩ := exists_closedPoint_range_stalk_eq c v
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  exact (closedPointPlace_range c ⟨x, hx⟩).symm.trans hrange

/-- All closed points correspond to all places of the actual scheme function field. -/
def closedPointPlaceEquiv :
    letI := (baseToFunctionField c).toAlgebra
    closedPoints C ≃ Place K C.functionField := by
  letI := (baseToFunctionField c).toAlgebra
  exact Equiv.ofBijective (closedPointPlace c)
    ⟨closedPointPlace_injective c, closedPointPlace_surjective c⟩

end AlgebraicCurve

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c]

/-- A centered place is rational exactly when the point's structural residue map is onto. -/
theorem closedPointPlace_isRational_iff (x : closedPoints C) :
    letI := (baseToFunctionField c).toAlgebra
    (closedPointPlace c x).IsRational ↔ Function.Surjective (residueBaseMap c x.val) := by
  letI := (baseToFunctionField c).toAlgebra
  letI := (stalkBaseMap c x.val).toAlgebra
  letI := (residueBaseMap c x.val).toAlgebra
  let E := closedPointPlaceResidueAlgEquiv c x
  constructor
  · intro h b
    obtain ⟨a, ha⟩ := h (E b)
    refine ⟨a, E.injective ?_⟩
    change E (algebraMap K (C.residueField x.val) a) = E b
    rw [E.commutes]
    exact ha
  · intro h b
    obtain ⟨a, ha⟩ := h (E.symm b)
    refine ⟨a, ?_⟩
    rw [← E.commutes a]
    change E (residueBaseMap c x.val a) = b
    rw [ha, E.apply_symm_apply]

/-- Degree one is exactly structural rationality of the corresponding closed point. -/
theorem closedPointPlace_degree_eq_one_iff (x : closedPoints C) :
    letI := (baseToFunctionField c).toAlgebra
    (closedPointPlace c x).deg = 1 ↔ Function.Surjective (residueBaseMap c x.val) := by
  letI := (baseToFunctionField c).toAlgebra
  rw [← Place.isRational_iff_deg_eq_one, closedPointPlace_isRational_iff]

/-- Restrict the full closed-point/place correspondence to residue degree one. -/
def rationalClosedPointPlaceEquiv :
    letI := (baseToFunctionField c).toAlgebra
    RationalClosedPoint c ≃ {v : Place K C.functionField // v.deg = 1} := by
  letI := (baseToFunctionField c).toAlgebra
  let E := closedPointPlaceEquiv c
  refine
    { toFun := fun x => ⟨E x.val, (closedPointPlace_degree_eq_one_iff c x.val).mpr x.property⟩
      invFun := fun v => ⟨E.symm v.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (closedPointPlace_degree_eq_one_iff c (E.symm v.val)).mp
    change (E (E.symm v.val)).deg = 1
    rw [E.apply_symm_apply]
    exact v.property
  · intro x
    apply Subtype.ext
    exact E.symm_apply_apply x.val
  · intro v
    apply Subtype.ext
    exact E.apply_symm_apply v.val

/-- Sections over K correspond to degree-one places of the actual scheme function field. -/
def schemeSectionPlaceEquiv :
    letI := (baseToFunctionField c).toAlgebra
    SchemeSection c ≃ {v : Place K C.functionField // v.deg = 1} := by
  letI := (baseToFunctionField c).toAlgebra
  exact (schemeSectionRationalClosedPointEquiv c).trans (rationalClosedPointPlaceEquiv c)

end AlgebraicCurve

end


