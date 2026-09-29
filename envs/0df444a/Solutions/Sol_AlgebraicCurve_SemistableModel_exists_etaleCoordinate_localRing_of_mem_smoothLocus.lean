-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.exists_etaleCoordinate_localRing_of_mem_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f8dfb29e-5379-5660-b21a-3946518aa50c

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_Algebra_FormallySmooth_exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 320000

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry TopCat

universe u v

namespace SmoothStalkPlumbing

variable {F : Type v} [Field F] {X : Scheme.{u}} [IsIntegral X] (φ : F ≃+* X.functionField)

theorem algebraMap_stalk_functionField_eq (x : X) :
    algebraMap (X.presheaf.stalk x) X.functionField =
      (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x))).hom :=
  rfl

theorem mem_localRing_iff (x : X) (g : F) :
    g ∈ SemistableModel.localRing X φ x ↔
      ∃ s : X.presheaf.stalk x, φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s) = g := by
  simp only [SemistableModel.localRing, RingHom.mem_range, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, Function.comp_apply]

theorem algebraMap_stalkSpecializes {x y : X} (h : x ⤳ y) (s : X.presheaf.stalk y) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.stalkSpecializes h).hom s) =
      algebraMap (X.presheaf.stalk y) X.functionField s := by
  rw [algebraMap_stalk_functionField_eq, algebraMap_stalk_functionField_eq,
    ← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem localRing_le_of_specializes {x y : X} (h : x ⤳ y) :
    SemistableModel.localRing X φ y ≤ SemistableModel.localRing X φ x := by
  intro g hg
  obtain ⟨s, rfl⟩ := (mem_localRing_iff φ y g).mp hg
  exact (mem_localRing_iff φ x _).mpr ⟨(X.presheaf.stalkSpecializes h).hom s, by
    rw [algebraMap_stalkSpecializes]⟩

theorem injective_symm_comp_algebraMap (x : X) :
    Function.Injective (fun s : X.presheaf.stalk x =>
      φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s)) :=
  φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)

noncomputable def localRingEquiv (x : X) : X.presheaf.stalk x ≃+* SemistableModel.localRing X φ x :=
  RingEquiv.ofBijective
    (((φ.symm : X.functionField ≃+* F).toRingHom.comp
      (algebraMap (X.presheaf.stalk x) X.functionField)).rangeRestrict)
    ⟨fun _ _ hab => injective_symm_comp_algebraMap φ x (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩

@[scoped simp] theorem coe_localRingEquiv (x : X) (s : X.presheaf.stalk x) :
    ((localRingEquiv φ x s : SemistableModel.localRing X φ x) : F) =
      φ.symm (algebraMap (X.presheaf.stalk x) X.functionField s) :=
  rfl

scoped instance isLocalRing_localRing (x : X) : IsLocalRing (SemistableModel.localRing X φ x) :=
  (localRingEquiv φ x).isLocalRing

theorem algebraMap_germ (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ U x hx).hom s) =
      (X.presheaf.germ U (genericPoint X)
        ((genericPoint_spec X).specializes (Set.mem_univ x) |>.mem_open U.2 hx)).hom s := by
  rw [algebraMap_stalk_functionField_eq, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

end SmoothStalkPlumbing
p2m_reactivate "P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus.SmoothStalkPlumbing"

namespace SmoothStalkResidue

theorem isAlgClosed_residueField {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (ResidueField ↥A) := by
  refine IsAlgClosed.of_exists_root _ (fun p hp hirr => ?_)

  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue ↥A) := by
    obtain ⟨q₀, hq₀⟩ := Polynomial.map_surjective (IsLocalRing.residue ↥A) IsLocalRing.residue_surjective p
    exact ⟨q₀, hq₀⟩
  obtain ⟨q, hqmap, hqdeg, hqmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hp

  have hdeg : (q.map (algebraMap ↥A L)).degree ≠ 0 := by
    rw [hqmonic.degree_map, hqdeg]
    exact fun h0 => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h0) |>.elim
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (q.map (algebraMap ↥A L)) hdeg
  have hint : IsIntegral ↥A r := ⟨q, hqmonic, by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hr⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨IsLocalRing.residue ↥A y, ?_⟩
  have hinj : Function.Injective (algebraMap ↥A L) := Subtype.val_injective
  have hy : q.eval y = 0 := by
    apply hinj
    rw [map_zero]
    have := hr
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map, Polynomial.eval₂_hom] at this
  rw [← hqmap, Polynomial.eval_map, Polynomial.eval₂_hom, hy, map_zero]

end SmoothStalkResidue
p2m_reactivate "P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus.SmoothStalkPlumbing"

namespace SmoothStalkChart

theorem isUnit_germ_top_iff (A : Type u) [CommRing A] [IsLocalRing A]
    (p : Spec (CommRingCat.of A)) (hp : p = closedPoint A) (a : A) :
    IsUnit (((Spec (CommRingCat.of A)).presheaf.germ ⊤ p trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) ↔ IsUnit a := by
  subst hp
  let e : (Spec (CommRingCat.of A)).presheaf.stalk (closedPoint A) ≃+* A :=
    (stalkClosedPointIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  have he : e (((Spec (CommRingCat.of A)).presheaf.germ ⊤ (closedPoint A) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = a := by
    change ((Spec (CommRingCat.of A)).presheaf.germ ⊤ (closedPoint A) trivial ≫
      (stalkClosedPointIso (CommRingCat.of A)).hom).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a
    rw [germ_stalkClosedPointIso_hom, ← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  constructor
  · intro hu
    have := hu.map e
    rwa [he] at this
  · intro hu
    have h2 := hu.map e.symm
    rw [← he, RingEquiv.symm_apply_apply] at h2
    exact h2

theorem isUnit_of_isUnit_mk {S : Type*} [CommRing S] [IsLocalRing S] (I : Ideal S)
    (hI : I ≤ maximalIdeal S) (s : S) (hu : IsUnit (Ideal.Quotient.mk I s)) : IsUnit s := by
  obtain ⟨y, hy⟩ := hu.exists_right_inv
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk I)] at hy
  have h1 : s * s' - 1 ∈ I := Ideal.Quotient.eq.mp hy
  by_contra hns
  have h2 : s * s' ∈ maximalIdeal S := Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hns)
  have h3 : (1 : S) ∈ maximalIdeal S := by
    have : (1 : S) = s * s' - (s * s' - 1) := by ring
    rw [this]; exact Ideal.sub_mem _ h2 (hI h1)
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 isUnit_one

end SmoothStalkChart
p2m_reactivate "P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus.SmoothStalkPlumbing"

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A) :
    let S : Subring F := SemistableModel.localRing X φ x
    ∃ (ι : ↥A →+* ↥S) (_ : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
      (t : ↥S) (χ₀ : ↥S →+* ResidueField ↥A),
      IsLocalRing ↥S ∧
      (∀ f : ↥S, IsUnit f ↔ χ₀ f ≠ 0) ∧
      (∀ a : ↥A, χ₀ (ι a) = IsLocalRing.residue ↥A a) ∧
      χ₀ t = 0 ∧
      (Polynomial.eval₂RingHom ι t).FormallySmooth ∧ (Polynomial.eval₂RingHom ι t).FormallyUnramified ∧
      (∀ f : ↥S, χ₀ f = 0 → ∃ g : ↥S, ∃ s ∈ (maximalIdeal ↥A).map ι, f = g * t + s) ∧
      ((maximalIdeal ↥A).map ι).IsPrime ∧ t ∉ (maximalIdeal ↥A).map ι ∧
      IsNoetherianRing (↥S ⧸ (maximalIdeal ↥A).map ι) ∧
      (∀ f : F, f ∈ SemistableModel.localRing X φ η ↔
        ∃ g h : ↥S, h ∉ (maximalIdeal ↥A).map ι ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∃ (P : Type) (_ : CommRing P) (_ : Algebra ↥A P) (_ : Algebra.FinitePresentation ↥A P)
          (M : Submonoid P) (_ : Algebra P ↥S) (_ : IsLocalization M ↥S),
        ∀ a : ↥A, algebraMap P ↥S (algebraMap ↥A P a) = ι a) := by
  intro S
  classical

  have hsm : (toBase.stalkMap x).hom.FormallySmooth := hxs
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU : V ≤ toBase ⁻¹ᵁ ⊤ := le_top
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of ↥A)).Opens) := isAffineOpen_top _

  set q : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨x, hxV⟩ with hqdef
  letI algRB : Algebra Γ(Spec (CommRingCat.of ↥A), ⊤) Γ(X, V) := (toBase.appLE ⊤ V hVU).hom.toAlgebra
  have hIsSm : Algebra.IsSmoothAt Γ(Spec (CommRingCat.of ↥A), ⊤) q.asIdeal :=
    (formallySmooth_stalkMap_iff ⊤ htop V hV hVU hxV).mp hsm
  have hfp : (toBase.appLE ⊤ V hVU).hom.FinitePresentation := toBase.finitePresentation_appLE htop hV hVU

  let eΓ := Scheme.ΓSpecIso (CommRingCat.of ↥A)
  let ψ : ↥A →+* Γ(X, V) := (toBase.appLE ⊤ V hVU).hom.comp eΓ.inv.hom

  have hgermψ : ∀ (y : X) (hyV : y ∈ V) (a : ↥A),
      (X.presheaf.germ V y hyV).hom (ψ a) =
        (toBase.stalkMap y).hom (((Spec (CommRingCat.of ↥A)).presheaf.germ ⊤ (toBase.base y) trivial).hom
          (eΓ.inv.hom a)) := by
    intro y hyV a
    change (toBase.appLE ⊤ V hVU ≫ X.presheaf.germ V y hyV).hom (eΓ.inv.hom a) =
      ((Spec (CommRingCat.of ↥A)).presheaf.germ ⊤ (toBase.base y) trivial ≫ toBase.stalkMap y).hom (eΓ.inv.hom a)
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

  have hover : ∀ (y : X) (hyV : y ∈ V), toBase.base y = closedPoint ↥A →
      ∀ a : ↥A, ψ a ∈ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal ↔ a ∈ maximalIdeal ↥A := by
    intro y hyV hy a
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hyV⟩ : V)
    haveI := hV.isLocalization_stalk ⟨y, hyV⟩
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal (ψ a),
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    change ¬ IsUnit ((X.presheaf.germ V y hyV).hom (ψ a)) ↔ _
    rw [hgermψ, isUnit_map_iff, SmoothStalkChart.isUnit_germ_top_iff ↥A (toBase.base y) hy a]

  let e : X.presheaf.stalk x ≃+* ↥S := SmoothStalkPlumbing.localRingEquiv φ x
  letI algBst : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  haveI hlocst : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  letI algBS : Algebra Γ(X, V) ↥S := (e.toRingHom.comp (algebraMap Γ(X, V) (X.presheaf.stalk x))).toAlgebra
  have halgBS : ∀ b, algebraMap Γ(X, V) ↥S b = e ((X.presheaf.germ V x hxV).hom b) := fun _ => rfl
  let eB : X.presheaf.stalk x ≃ₐ[Γ(X, V)] ↥S := AlgEquiv.ofRingEquiv (f := e) (fun b => rfl)
  haveI hlocS : IsLocalization.AtPrime (↥S) q.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv q.asIdeal.primeCompl eB

  let ι : ↥A →+* ↥S := (algebraMap Γ(X, V) ↥S).comp ψ
  letI algAS : Algebra ↥A ↥S := ι.toAlgebra
  letI algAB : Algebra ↥A Γ(X, V) := ψ.toAlgebra
  haveI : IsScalarTower ↥A Γ(X, V) ↥S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hιdef : ∀ a : ↥A, ι a = algebraMap Γ(X, V) ↥S (ψ a) := fun _ => rfl
  have hιF : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L) := by
    intro a
    rw [hιdef, halgBS, SmoothStalkPlumbing.coe_localRingEquiv, SmoothStalkPlumbing.algebraMap_germ]
    rw [RingEquiv.symm_apply_eq, hφ]
    change ((toBase.appLE ⊤ V hVU) ≫ X.presheaf.germ V (genericPoint X) _).hom (eΓ.inv.hom a) =
      (toBase.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom (eΓ.inv.hom a)
    rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    rfl

  haveI hfpAB : Algebra.FinitePresentation ↥A Γ(X, V) :=
    RingHom.finitePresentation_respectsIso.2 (toBase.appLE ⊤ V hVU).hom eΓ.commRingCatIsoToRingEquiv.symm hfp
  haveI : Algebra.EssFiniteType Γ(X, V) ↥S := Algebra.EssFiniteType.of_isLocalization (↥S) q.asIdeal.primeCompl
  haveI : Algebra.EssFiniteType ↥A ↥S := Algebra.EssFiniteType.comp ↥A Γ(X, V) ↥S

  have hunitS : ∀ b : Γ(X, V), IsUnit (algebraMap Γ(X, V) ↥S b) ↔ b ∉ q.asIdeal := fun b =>
    IsLocalization.AtPrime.isUnit_to_map_iff (↥S) q.asIdeal b
  have hoverx : ∀ a : ↥A, ψ a ∈ q.asIdeal ↔ a ∈ maximalIdeal ↥A := hover x hxV hx
  haveI hlocal : IsLocalHom (algebraMap ↥A ↥S) := ⟨fun a ha => by
    change IsUnit (ι a) at ha
    rw [hιdef, hunitS, hoverx, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at ha
    exact ha⟩
  have hιmax : ∀ a : ↥A, ι a ∈ maximalIdeal ↥S ↔ a ∈ maximalIdeal ↥A := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hιdef, hunitS, not_not, hoverx]

  letI algRS : Algebra Γ(Spec (CommRingCat.of ↥A), ⊤) ↥S :=
    ((algebraMap Γ(X, V) ↥S).comp (toBase.appLE ⊤ V hVU).hom).toAlgebra
  haveI : IsScalarTower Γ(Spec (CommRingCat.of ↥A), ⊤) Γ(X, V) ↥S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hfsS : Algebra.FormallySmooth ↥A ↥S := by
    let eL : Localization.AtPrime q.asIdeal ≃ₐ[Γ(X, V)] ↥S := IsLocalization.algEquiv q.asIdeal.primeCompl _ _
    haveI : Algebra.FormallySmooth Γ(Spec (CommRingCat.of ↥A), ⊤) ↥S :=
      Algebra.FormallySmooth.of_equiv (eL.restrictScalars Γ(Spec (CommRingCat.of ↥A), ⊤))
    letI algAR : Algebra ↥A Γ(Spec (CommRingCat.of ↥A), ⊤) := eΓ.inv.hom.toAlgebra
    haveI : IsScalarTower ↥A Γ(Spec (CommRingCat.of ↥A), ⊤) ↥S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let eA : ↥A ≃ₐ[↥A] Γ(Spec (CommRingCat.of ↥A), ⊤) :=
      AlgEquiv.ofRingEquiv (f := eΓ.commRingCatIsoToRingEquiv.symm) (fun a => rfl)
    haveI : Algebra.FormallySmooth ↥A Γ(Spec (CommRingCat.of ↥A), ⊤) := Algebra.FormallySmooth.of_equiv eA
    exact Algebra.FormallySmooth.comp ↥A Γ(Spec (CommRingCat.of ↥A), ⊤) ↥S

  have hxclosed : IsClosed ({x} : Set X) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    exact hxc y (specializes_iff_mem_closure.mpr hy)
  haveI hqmax : q.asIdeal.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hxclosed
  haveI hkclosed : IsAlgClosed (ResidueField ↥A) := SmoothStalkResidue.isAlgClosed_residueField A
  have hBq : ∀ b : Γ(X, V), ∃ a : ↥A, b - ψ a ∈ q.asIdeal := by
    let K := Γ(X, V) ⧸ q.asIdeal
    letI : Field K := Ideal.Quotient.field q.asIdeal
    have hle : maximalIdeal ↥A ≤ q.asIdeal.comap ψ := fun a ha => (hoverx a).mpr ha
    letI algkK : Algebra (ResidueField ↥A) K := (Ideal.quotientMap q.asIdeal ψ hle).toAlgebra
    haveI : IsScalarTower ↥A (ResidueField ↥A) K := IsScalarTower.of_algebraMap_eq (fun a => rfl)
    haveI : Algebra.FiniteType (ResidueField ↥A) K :=
      Algebra.FiniteType.of_restrictScalars_finiteType ↥A (ResidueField ↥A) K
    haveI : Module.Finite (ResidueField ↥A) K := finite_of_finite_type_of_isJacobsonRing (ResidueField ↥A) K
    haveI : Algebra.IsIntegral (ResidueField ↥A) K := inferInstance
    intro b
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField ↥A) (K := K)).2
      (Ideal.Quotient.mk q.asIdeal b)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨a, ?_⟩
    rw [← Ideal.Quotient.eq, ← hc]
    rfl
  have hres' : ∀ z : ↥S, ∃ a : ↥A, z - ι a ∈ maximalIdeal ↥S := by
    intro z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl z
    obtain ⟨ab, hab⟩ := hBq b
    obtain ⟨as, has⟩ := hBq s
    have hasu : IsUnit as := by
      by_contra hnu
      have h1 : ψ as ∈ q.asIdeal := (hoverx as).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      have h2 : (s : Γ(X, V)) ∈ q.asIdeal := by
        have : (s : Γ(X, V)) = ((s : Γ(X, V)) - ψ as) + ψ as := by ring
        rw [this]; exact Ideal.add_mem _ has h1
      exact s.2 h2
    refine ⟨ab * ↑hasu.unit⁻¹, ?_⟩
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal ↥S]

    have key : (IsLocalization.mk' (↥S) b s - ι (ab * ↑hasu.unit⁻¹)) * algebraMap Γ(X, V) ↥S s =
        algebraMap Γ(X, V) ↥S (b - ψ ab) - ι (ab * ↑hasu.unit⁻¹) * algebraMap Γ(X, V) ↥S (s - ψ as) := by
      have e1 := IsLocalization.mk'_spec (↥S) b s
      have hu : ψ ↑hasu.unit⁻¹ * ψ as = 1 := by rw [← map_mul, IsUnit.val_inv_mul, map_one]
      have hu' : algebraMap Γ(X, V) ↥S (ψ ↑hasu.unit⁻¹) * algebraMap Γ(X, V) ↥S (ψ as) = 1 := by
        rw [← map_mul, hu, map_one]
      simp only [hιdef, map_mul, map_sub]
      linear_combination e1 - (algebraMap Γ(X, V) ↥S (ψ ab)) * hu'
    have hmem : (IsLocalization.mk' (↥S) b s - ι (ab * ↑hasu.unit⁻¹)) * algebraMap Γ(X, V) ↥S s ∈
        q.asIdeal.map (algebraMap Γ(X, V) ↥S) := by
      rw [key]
      exact Ideal.sub_mem _ (Ideal.mem_map_of_mem _ hab) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ has))
    have hsu : IsUnit (algebraMap Γ(X, V) ↥S s) := (hunitS s).mpr s.2
    have := Ideal.mul_mem_right (↑hsu.unit⁻¹ : ↥S) _ hmem
    rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
  have hres : Function.Surjective (algebraMap ↥A (ResidueField ↥S)) := by
    intro z
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, ha⟩ := hres' w
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply ↥A ↥S (ResidueField ↥S), IsLocalRing.ResidueField.algebraMap_eq, eq_comm,
      ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha

  have hfracS : ∀ z : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ z * (h : F) = (g : F) := by
    intro z
    obtain ⟨a', b', hb', hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x) (φ z)
    have hb0 : (b' : X.presheaf.stalk x) ≠ 0 := nonZeroDivisors.ne_zero hb'
    have hbF : ((e b' : ↥S) : F) ≠ 0 := by
      intro h0
      apply hb0
      have : e b' = 0 := Subtype.ext h0
      exact e.injective (this.trans (map_zero e).symm)
    refine ⟨e a', e b', hbF, ?_⟩
    rw [SmoothStalkPlumbing.coe_localRingEquiv, SmoothStalkPlumbing.coe_localRingEquiv,
      ← (div_eq_iff (by rwa [SmoothStalkPlumbing.coe_localRingEquiv] at hbF)).mp]
    rw [← map_div₀, hab, RingEquiv.symm_apply_apply]
  haveI hfrS : IsFractionRing (↥S) F := by
    refine IsFractionRing.of_field (↥S) F (fun z => ?_)
    obtain ⟨g, h, hh, e1⟩ := hfracS z
    exact ⟨g, h, ((eq_div_iff hh).mpr e1)⟩
  letI algAF : Algebra ↥A F := ((algebraMap L F).comp (algebraMap ↥A L)).toAlgebra
  haveI : IsScalarTower ↥A L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥A ↥S F := IsScalarTower.of_algebraMap_eq (fun a => (hιF a).symm)
  have h1 : Module.finrank ↥S Ω[↥S⁄↥A] = 1 := by
    haveI : Module.Free ↥S Ω[↥S⁄↥A] := Module.free_of_flat_of_isLocalRing

    haveI : Algebra.FormallyEtale ↥S F := Algebra.FormallyEtale.of_isLocalization (M := nonZeroDivisors ↥S)
    have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale ↥A ↥S F
    have e1 : Module.finrank F Ω[F⁄↥A] = Module.finrank ↥S Ω[↥S⁄↥A] := by
      rw [← hbc.equiv.finrank_eq, Module.finrank_baseChange]

    haveI : Algebra.FormallyEtale ↥A L := Algebra.FormallyEtale.of_isLocalization (M := nonZeroDivisors ↥A)
    have hinj : Function.Injective (KaehlerDifferential.map ↥A L F F) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp (KaehlerDifferential.exact_mapBaseChange_map ↥A L F),
        LinearMap.range_eq_bot]
      refine LinearMap.ext (fun z => ?_)
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, LinearMap.zero_apply]
      | tmul f ω => rw [Subsingleton.elim ω 0, TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]
      | add a b ha hb => rw [map_add, ha, hb, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, add_zero]
    have e2 : Module.finrank F Ω[F⁄↥A] = Module.finrank F Ω[F⁄L] :=
      (LinearEquiv.ofBijective (KaehlerDifferential.map ↥A L F F)
        ⟨hinj, KaehlerDifferential.map_surjective ↥A L F⟩).finrank_eq
    rw [← e1, e2, IsCurveOver.finrank_kaehler]

  obtain ⟨t, htmax, hφs, hφu, hmaxeq⟩ :=
    Algebra.FormallySmooth.exists_formallyUnramified_aeval_and_maximalIdeal_eq_of_finrank_kaehlerDifferential_eq_one
      hres h1
  have hev : (Polynomial.aeval t : Polynomial ↥A →ₐ[↥A] ↥S).toRingHom = Polynomial.eval₂RingHom ι t :=
    RingHom.ext (fun p => Polynomial.aeval_def t p)
  rw [hev] at hφs hφu

  have hbij : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap ↥A ↥S)) := by
    refine ⟨RingHom.injective _, fun z => ?_⟩
    obtain ⟨a, rfl⟩ := hres z
    exact ⟨IsLocalRing.residue ↥A a, by
      rw [IsLocalRing.ResidueField.map_residue, IsScalarTower.algebraMap_apply ↥A ↥S (ResidueField ↥S),
        IsLocalRing.ResidueField.algebraMap_eq]⟩
  let eκ : ResidueField ↥A ≃+* ResidueField ↥S := RingEquiv.ofBijective _ hbij
  have heκ : ∀ a : ↥A, eκ (IsLocalRing.residue ↥A a) = IsLocalRing.residue ↥S (ι a) := fun a =>
    IsLocalRing.ResidueField.map_residue (algebraMap ↥A ↥S) a
  let χ₀ : ↥S →+* ResidueField ↥A := eκ.symm.toRingHom.comp (IsLocalRing.residue ↥S)
  have hχ₀ : ∀ f : ↥S, χ₀ f = eκ.symm (IsLocalRing.residue ↥S f) := fun _ => rfl
  have hχ₀zero : ∀ f : ↥S, χ₀ f = 0 ↔ f ∈ maximalIdeal ↥S := by
    intro f
    rw [hχ₀, map_eq_zero_iff _ eκ.symm.injective, IsLocalRing.residue_eq_zero_iff]

  set I : Ideal ↥S := (maximalIdeal ↥A).map (algebraMap ↥A ↥S) with hIdef
  have hIι : (maximalIdeal ↥A).map ι = I := rfl
  have hImax : I ≤ maximalIdeal ↥S := by
    rw [hIdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    exact (hιmax a).mpr ha
  have hnoeth : IsNoetherianRing (↥S ⧸ I) := by
    haveI : IsNoetherianRing (↥A ⧸ maximalIdeal ↥A) := inferInstanceAs (IsNoetherianRing (ResidueField ↥A))
    exact Algebra.EssFiniteType.isNoetherianRing (↥A ⧸ maximalIdeal ↥A) (↥S ⧸ I)

  have hηV : η ∈ V := hηx.mem_open V.2 hxV
  set qη : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨η, hηV⟩ with hqηdef
  have hqηle : qη ≤ q := by
    rw [PrimeSpectrum.le_iff_specializes]
    have h1 : (⟨η, hηV⟩ : V) ⤳ (⟨x, hxV⟩ : V) := Topology.IsInducing.subtypeVal.specializes_iff.mp hηx
    exact h1.map (hV.isoSpec.hom).continuous
  have hqηne : qη ≠ q := by
    intro h
    apply hne
    have h1 : hV.fromSpec qη = η := hV.fromSpec_primeIdealOf ⟨η, hηV⟩
    have h2 : hV.fromSpec q = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
    rw [h] at h1
    exact h1.symm.trans h2
  have hoverη : ∀ a : ↥A, ψ a ∈ qη.asIdeal ↔ a ∈ maximalIdeal ↥A := hover η hηV hη
  set P : Ideal ↥S := qη.asIdeal.map (algebraMap Γ(X, V) ↥S) with hPdef
  have hdisj : Disjoint (q.asIdeal.primeCompl : Set Γ(X, V)) qη.asIdeal := by
    rw [Set.disjoint_left]
    intro b hb hbη
    exact hb (hqηle hbη)
  haveI hPprime : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl (↥S) qη.asIdeal qη.2 hdisj
  have hPcomap : P.comap (algebraMap Γ(X, V) ↥S) = qη.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl (↥S) qη.2 hdisj
  have hmemP : ∀ b : Γ(X, V), algebraMap Γ(X, V) ↥S b ∈ P ↔ b ∈ qη.asIdeal := fun b => by
    rw [← Ideal.mem_comap, hPcomap]
  have hIP : I ≤ P := by
    rw [hIdef, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    change ι a ∈ P
    rw [hιdef, hmemP, hoverη]
    exact ha
  have hPne : P ≠ maximalIdeal ↥S := by
    intro h
    apply hqηne
    apply PrimeSpectrum.ext
    rw [← hPcomap, h]
    exact IsLocalization.AtPrime.comap_maximalIdeal (↥S) q.asIdeal
  have hPle : P ≤ maximalIdeal ↥S := IsLocalRing.le_maximalIdeal hPprime.ne_top
  have htP : t ∉ P := by
    intro ht
    apply hPne
    refine le_antisymm hPle ?_
    rw [hmaxeq]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ht) hIP

  have hPI : P = I := by
    refine le_antisymm ?_ hIP
    let π := Ideal.Quotient.mk I
    have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
    haveI : Nontrivial (↥S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (fun htop => (IsLocalRing.maximalIdeal.isMaximal ↥S).ne_top (top_le_iff.mp (htop ▸ hImax)))
    haveI : IsLocalRing (↥S ⧸ I) := IsLocalRing.of_surjective' π hπsurj
    haveI : IsNoetherianRing (↥S ⧸ I) := hnoeth
    have hπmax : ∀ s : ↥S, π s ∈ maximalIdeal (↥S ⧸ I) ↔ s ∈ maximalIdeal ↥S := by
      intro s
      rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
      exact not_congr ⟨SmoothStalkChart.isUnit_of_isUnit_mk I hImax s, fun hu => hu.map π⟩
    have hmaxb : maximalIdeal (↥S ⧸ I) = Ideal.span {π t} := by
      apply le_antisymm
      · intro z hz
        obtain ⟨s, rfl⟩ := hπsurj z
        have hs : s ∈ maximalIdeal ↥S := (hπmax s).mp hz
        rw [hmaxeq] at hs
        obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.mp hs
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hi, add_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · rw [Ideal.span_singleton_le_iff_mem, hπmax]; exact htmax
    have hPb : (P.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hπsurj (by rw [Ideal.mk_ker]; exact hIP)
    have htPb : π t ∉ P.map π := by
      intro h
      apply htP
      have h4 : t ∈ (P.map π).comap π := h
      rwa [Ideal.comap_map_of_surjective _ hπsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_eq_left.mpr hIP] at h4
    have hPbot : P.map π = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr (fun p hp => ?_)
      have hall : ∀ n : ℕ, p ∈ Ideal.span {π t ^ n} := by
        intro n
        induction n with
        | zero => rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
        | succ n ih =>
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ih
          have hc : c ∈ P.map π := by
            rcases hPb.mem_or_mem hp with h | h
            · exact h
            · exact (htPb (hPb.mem_of_pow_mem n h)).elim
          have hcm : c ∈ maximalIdeal (↥S ⧸ I) := IsLocalRing.le_maximalIdeal hPb.ne_top hc
          rw [hmaxb] at hcm
          obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hcm
          exact Ideal.mem_span_singleton'.mpr ⟨c', by ring⟩
      have hmem : p ∈ ⨅ n : ℕ, (maximalIdeal (↥S ⧸ I)) ^ n := by
        rw [Ideal.mem_iInf]
        intro n
        rw [hmaxb, Ideal.span_singleton_pow]
        exact hall n
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
        Ideal.mem_bot] at hmem
    intro s hs
    have h1 : π s ∈ P.map π := Ideal.mem_map_of_mem _ hs
    rw [hPbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1
  have hIprime : I.IsPrime := hPI ▸ hPprime
  have htI : t ∉ I := hPI ▸ htP

  letI algBη : Algebra Γ(X, V) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηV⟩ : V)
  haveI hlocη : IsLocalization.AtPrime (X.presheaf.stalk η) qη.asIdeal := hV.isLocalization_stalk ⟨η, hηV⟩
  have hread : ∀ b : Γ(X, V), φ.symm (algebraMap (X.presheaf.stalk η) X.functionField
      (algebraMap Γ(X, V) (X.presheaf.stalk η) b)) = ((algebraMap Γ(X, V) ↥S b : ↥S) : F) := by
    intro b
    rw [halgBS, SmoothStalkPlumbing.coe_localRingEquiv]
    change φ.symm (algebraMap _ _ ((X.presheaf.germ V η hηV).hom b)) =
      φ.symm (algebraMap _ _ ((X.presheaf.germ V x hxV).hom b))
    rw [SmoothStalkPlumbing.algebraMap_germ, SmoothStalkPlumbing.algebraMap_germ]
  have hloc11 : ∀ f : F, f ∈ SemistableModel.localRing X φ η ↔
      ∃ g h : ↥S, h ∉ (maximalIdeal ↥A).map ι ∧ f * (h : F) = (g : F) := by
    intro f
    rw [hIι]
    constructor
    · intro hf
      obtain ⟨s, rfl⟩ := (SmoothStalkPlumbing.mem_localRing_iff φ η f).mp hf
      obtain ⟨⟨b, w⟩, rfl⟩ := IsLocalization.mk'_surjective qη.asIdeal.primeCompl s
      refine ⟨algebraMap Γ(X, V) ↥S b, algebraMap Γ(X, V) ↥S w, ?_, ?_⟩
      · rw [← hPI, hmemP]; exact w.2
      · rw [← hread, ← hread, ← map_mul, ← map_mul, IsLocalization.mk'_spec]
    · rintro ⟨g, h, hh, e1⟩
      obtain ⟨⟨b₂, w₂⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl g
      obtain ⟨⟨b₁, w₁⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl h
      have hb₁ : b₁ ∉ qη.asIdeal := by
        intro hb
        apply hh
        rw [← hPI]
        exact IsLocalization.mk'_mem_iff.mpr ((hmemP b₁).mpr hb)
      have hw₂ : (w₂ : Γ(X, V)) ∉ qη.asIdeal := fun hw => w₂.2 (hqηle hw)
      have hbw : b₁ * w₂ ∉ qη.asIdeal := fun hmem => by
        rcases qη.2.mem_or_mem hmem with h' | h'
        · exact hb₁ h'
        · exact hw₂ h'
      let z := IsLocalization.mk' (X.presheaf.stalk η) (b₂ * w₁) (⟨b₁ * w₂, hbw⟩ : qη.asIdeal.primeCompl)
      refine (SmoothStalkPlumbing.mem_localRing_iff φ η f).mpr ⟨z, ?_⟩
      have hd : ((algebraMap Γ(X, V) ↥S (b₁ * w₂) : ↥S) : F) ≠ 0 := by
        intro h0
        have h0' : algebraMap Γ(X, V) ↥S (b₁ * w₂) = 0 := Subtype.ext h0
        have hmem : algebraMap Γ(X, V) ↥S (b₁ * w₂) ∈ P := by rw [h0']; exact P.zero_mem
        exact hbw ((hmemP _).mp hmem)
      have hz : φ.symm (algebraMap _ _ z) * ((algebraMap Γ(X, V) ↥S (b₁ * w₂) : ↥S) : F) =
          ((algebraMap Γ(X, V) ↥S (b₂ * w₁) : ↥S) : F) := by
        rw [← hread, ← hread, ← map_mul, ← map_mul]
        congr 2
        exact IsLocalization.mk'_spec _ _ _
      have hf : f * ((algebraMap Γ(X, V) ↥S (b₁ * w₂) : ↥S) : F) =
          ((algebraMap Γ(X, V) ↥S (b₂ * w₁) : ↥S) : F) := by
        have k1 : (IsLocalization.mk' (↥S) b₁ w₁) * algebraMap Γ(X, V) ↥S (w₁ * w₂) =
            algebraMap Γ(X, V) ↥S (b₁ * w₂) := by
          rw [map_mul, ← mul_assoc, IsLocalization.mk'_spec, ← map_mul]
        have k2 : (IsLocalization.mk' (↥S) b₂ w₂) * algebraMap Γ(X, V) ↥S (w₁ * w₂) =
            algebraMap Γ(X, V) ↥S (b₂ * w₁) := by
          rw [map_mul, mul_comm (algebraMap Γ(X, V) ↥S (w₁ : Γ(X, V))), ← mul_assoc, IsLocalization.mk'_spec,
            ← map_mul]
        have k1' := congrArg (fun s : ↥S => (s : F)) k1
        have k2' := congrArg (fun s : ↥S => (s : F)) k2
        simp only [Subring.coe_mul] at k1' k2'
        calc f * ((algebraMap Γ(X, V) ↥S (b₁ * w₂) : ↥S) : F)
            = (f * ((IsLocalization.mk' (↥S) b₁ w₁ : ↥S) : F)) *
                ((algebraMap Γ(X, V) ↥S (w₁ * w₂) : ↥S) : F) := by rw [← k1']; ring
          _ = ((IsLocalization.mk' (↥S) b₂ w₂ : ↥S) : F) * ((algebraMap Γ(X, V) ↥S (w₁ * w₂) : ↥S) : F) := by
                rw [e1]
          _ = ((algebraMap Γ(X, V) ↥S (b₂ * w₁) : ↥S) : F) := k2'
      exact mul_right_cancel₀ hd (hz.trans hf.symm)

  refine ⟨ι, hιF, t, χ₀, inferInstance, ?_, ?_, ?_, hφs, hφu, ?_, hIprime, htI, hnoeth, hloc11, hfracS,
    ⟨Γ(X, V), inferInstance, algAB, hfpAB, q.asIdeal.primeCompl, algBS, hlocS, fun a => rfl⟩⟩
  · intro f
    rw [ne_eq, hχ₀zero, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  · intro a
    rw [hχ₀, ← heκ, RingEquiv.symm_apply_apply]
  · exact (hχ₀zero t).mpr htmax
  · intro f hf
    rw [hχ₀zero, hmaxeq] at hf
    obtain ⟨y, hy, s', hs', rfl⟩ := Submodule.mem_sup.mp hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    exact ⟨g, s', hs', rfl⟩

end S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_localRing_of_mem_smoothLocus (solution)
