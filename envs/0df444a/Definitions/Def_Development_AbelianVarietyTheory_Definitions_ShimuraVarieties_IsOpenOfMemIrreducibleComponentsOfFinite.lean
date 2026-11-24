-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
-- name    : Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:53:56.644948+00:00
-- url     : https://prove2.me/theorems/33af492b-8499-4d52-9f45-fdeba9449f5a
-- title:
--   Is Open Of Mem Irreducible Components Of Finite
-- statement:
--   Definitions and structural lemmas for Is Open Of Mem Irreducible Components Of Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IsOpenOfMemIrreducibleComponentsOfFinite.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace GlobalTheory
class IsNormalScheme (X : Scheme.{u}) : Prop where

  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)

  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)
attribute [instance] IsNormalScheme.isDomain_stalk IsNormalScheme.isIntegrallyClosed_stalk
theorem isNormalScheme_iff (X : Scheme.{u}) :
    IsNormalScheme X ↔
      ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) :=
  ⟨fun h x ↦ ⟨h.1 x, h.2 x⟩, fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩⟩
theorem isNormalScheme_iff_pred (X : Scheme.{0}) :
    GlobalTheory.IsNormalScheme X ↔ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X :=
  isNormalScheme_iff X
theorem IsNormalScheme.pred (X : Scheme.{0}) [h : GlobalTheory.IsNormalScheme X] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X :=
  (isNormalScheme_iff_pred X).mp h
theorem IsNormalScheme.of_pred {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) :
    GlobalTheory.IsNormalScheme X :=
  (isNormalScheme_iff_pred X).mpr h
namespace IsNormalScheme
theorem isDomain_and_isIntegrallyClosed_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : (IsDomain R ∧ IsIntegrallyClosed R) ↔ (IsDomain S ∧ IsIntegrallyClosed S) :=
  ⟨fun ⟨_, _⟩ ↦ ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩,
    fun ⟨_, _⟩ ↦ ⟨e.toMulEquiv.isDomain _, .of_equiv e.symm⟩⟩
theorem of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [∀ x, IsIso (f.stalkMap x)]
    [IsNormalScheme Y] : IsNormalScheme X :=
  (isNormalScheme_iff X).mpr fun x ↦
    (isDomain_and_isIntegrallyClosed_iff_of_ringEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).mp ⟨inferInstance, inferInstance⟩
theorem of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsNormalScheme Y] : IsNormalScheme X :=
  of_isIso_stalkMap f
instance opens {X : Scheme.{u}} [IsNormalScheme X] (U : X.Opens) : IsNormalScheme U :=
  of_isOpenImmersion U.ι
instance openCover_X {X : Scheme.{u}} [IsNormalScheme X] (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    IsNormalScheme (𝒰.X i) :=
  of_isOpenImmersion (𝒰.f i)
theorem of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] [IsNormalScheme X] :
    IsNormalScheme Y :=
  of_isOpenImmersion (inv f)
theorem iff_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) : IsNormalScheme X ↔ IsNormalScheme Y :=
  ⟨fun _ ↦ of_isIso e.hom, fun _ ↦ of_isIso e.inv⟩
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsNormalScheme ·) :=
  ⟨fun e _ ↦ of_isIso e.hom⟩
theorem of_forall_exists_isOpenImmersion {X : Scheme.{u}}
    (h : ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsOpenImmersion f),
      IsNormalScheme Y ∧ x ∈ Set.range f) : IsNormalScheme X := by
  refine (isNormalScheme_iff X).mpr fun x ↦ ?_
  obtain ⟨Y, f, _, _, y, rfl⟩ := h x
  exact (isDomain_and_isIntegrallyClosed_iff_of_ringEquiv
      (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv).mpr ⟨inferInstance, inferInstance⟩
theorem of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover) [∀ i, IsNormalScheme (𝒰.X i)] :
    IsNormalScheme X :=
  of_forall_exists_isOpenImmersion fun x ↦ by
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact ⟨_, 𝒰.f i, inferInstance, inferInstance, y, rfl⟩
theorem iff_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    IsNormalScheme X ↔ ∀ i, IsNormalScheme (𝒰.X i) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ of_openCover 𝒰⟩
instance (priority := 900) isReduced {X : Scheme.{u}} [IsNormalScheme X] : IsReduced X :=
  isReduced_of_isReduced_stalk X
theorem isIntegral_of_irreducibleSpace (X : Scheme.{u}) [IsNormalScheme X] [IrreducibleSpace X] :
    IsIntegral X :=
  isIntegral_of_irreducibleSpace_of_isReduced X
theorem spec_iff (R : CommRingCat.{u}) :
    IsNormalScheme (Spec R) ↔ ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  rw [isNormalScheme_iff]
  constructor
  · intro h p hp
    exact (isDomain_and_isIntegrallyClosed_iff_of_ringEquiv
      (Spec.stalkIso R ⟨p, hp⟩).commRingCatIsoToRingEquiv).mp (h ⟨p, hp⟩)
  · intro h x
    exact (isDomain_and_isIntegrallyClosed_iff_of_ringEquiv
      (Spec.stalkIso R x).commRingCatIsoToRingEquiv).mpr (@h x.asIdeal x.isPrime)
instance spec (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalScheme (Spec R) :=
  (spec_iff R).mpr fun p _ ↦
    ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ _ p.primeCompl_le_nonZeroDivisors⟩
theorem spec_iff_of_isDomain (R : CommRingCat.{u}) [IsDomain R] :
    IsNormalScheme (Spec R) ↔ IsIntegrallyClosed R :=
  ⟨fun h ↦ .of_localization_maximal fun p _ _ ↦ ((spec_iff R).mp h p).2, fun _ ↦ inferInstance⟩
theorem iff_spec_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    IsNormalScheme U ↔ IsNormalScheme (Spec Γ(X, U)) :=
  iff_of_iso hU.isoSpec
theorem spec_of_isAffineOpen {X : Scheme.{u}} [IsNormalScheme X] {U : X.Opens}
    (hU : IsAffineOpen U) : IsNormalScheme (Spec Γ(X, U)) :=
  (iff_spec_of_isAffineOpen hU).mp inferInstance
theorem isDiscreteValuationRing_stalk {X : Scheme.{u}} [IsNormalScheme X] [IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hf : ¬ IsField (X.presheaf.stalk x) := fun h ↦ by
    have := ringKrullDim_eq_zero_of_isField h
    rw [ringKrullDim_stalk_eq_coheight, hx] at this
    simp at this
  have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
  have h3 : IsIntegrallyClosed (X.presheaf.stalk x) ∧
      ∃! P : Ideal (X.presheaf.stalk x), P ≠ ⊥ ∧ P.IsPrime :=
    ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP ↦ IsLocalRing.eq_maximalIdeal
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hf).out 0 3).mpr h3
theorem eq_of_mem_irreducibleComponents_of_isDomain {X : Scheme.{u}} {x : X}
    [IsDomain (X.presheaf.stalk x)] {Z W : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hW : W ∈ irreducibleComponents X) (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  first
  | (rename_i h_2; revert X x h_2 Z W hZ hW hxZ hxW; exact @_root_.GlobalTheory.IrreducibleGeneralizations.main)
  | exact @_root_.GlobalTheory.IrreducibleGeneralizations.main
  | exact _root_.GlobalTheory.IrreducibleGeneralizations.main
  | (apply _root_.GlobalTheory.IrreducibleGeneralizations.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IrreducibleGeneralizations.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IrreducibleGeneralizations.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IrreducibleGeneralizations.main ..)
theorem eq_of_mem_irreducibleComponents {X : Scheme.{u}} [IsNormalScheme X] {x : X}
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W :=
  eq_of_mem_irreducibleComponents_of_isDomain hZ hW hxZ hxW
theorem pairwiseDisjoint_irreducibleComponents (X : Scheme.{u}) [IsNormalScheme X] :
    (irreducibleComponents X).PairwiseDisjoint id := fun _ hZ _ hW hne ↦
  Set.disjoint_left.mpr fun _ hxZ hxW ↦ hne (eq_of_mem_irreducibleComponents hZ hW hxZ hxW)
theorem isOpen_of_mem_irreducibleComponents_of_finite {X : Scheme.{u}} [IsNormalScheme X]
    (hX : (irreducibleComponents X).Finite) {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    IsOpen Z := by
  have : Zᶜ = ⋃ W ∈ irreducibleComponents X \ {Z}, W := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents x, fun h ↦ hx ?_⟩,
        mem_irreducibleComponent⟩
      exact (show irreducibleComponent x = Z from h) ▸ mem_irreducibleComponent
    · rintro ⟨W, ⟨hW, hne⟩, hxW⟩ hxZ
      exact hne (eq_of_mem_irreducibleComponents hW hZ hxW hxZ)
  rw [← isClosed_compl_iff, this]
  exact hX.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
theorem isOpen_of_mem_irreducibleComponents {X : Scheme.{u}} [IsNormalScheme X]
    [IsLocallyNoetherian X] {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨(U : X.Opens), hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace U.toScheme := noetherianSpace_of_isAffineOpen U hU
  let y : U.toScheme := ⟨x, hxU⟩
  have hy : U.ι y = x := rfl
  have ho : IsOpen (irreducibleComponent y) := isOpen_of_mem_irreducibleComponents_of_finite
    NoetherianSpace.finite_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents y)
  have hi : IsIrreducible (U.ι '' irreducibleComponent y) :=
    isIrreducible_irreducibleComponent.image _ U.ι.continuous.continuousOn
  have hxi : x ∈ U.ι '' irreducibleComponent y := ⟨y, mem_irreducibleComponent, hy⟩
  obtain ⟨W, hW, hle⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hi
  refine ⟨_, ?_, U.ι.isOpenEmbedding.isOpenMap _ ho, hxi⟩
  rwa [eq_of_mem_irreducibleComponents hZ hW hx (hle hxi)]
instance finite_irreducibleComponents (X : Scheme.{u}) [IsNoetherian X] :
    Finite (irreducibleComponents X) :=
  NoetherianSpace.finite_irreducibleComponents.to_subtype
section Components
variable {X : Scheme.{u}} [IsNormalScheme X] [IsLocallyNoetherian X]
def component (Z : irreducibleComponents X) : X.Opens :=
  ⟨Z.1, isOpen_of_mem_irreducibleComponents Z.2⟩
@[simp]
theorem coe_component (Z : irreducibleComponents X) : (component Z : Set X) = Z.1 := rfl
@[simp]
theorem mem_component {Z : irreducibleComponents X} {x : X} : x ∈ component Z ↔ x ∈ Z.1 := Iff.rfl
theorem isClosed_component (Z : irreducibleComponents X) : IsClosed (component Z : Set X) :=
  isClosed_of_mem_irreducibleComponents _ Z.2
instance nonempty_component (Z : irreducibleComponents X) : Nonempty (component Z) :=
  Z.2.1.nonempty.to_subtype
instance isIntegral_component (Z : irreducibleComponents X) : IsIntegral (component Z) :=
  have : IrreducibleSpace (component Z).toScheme := Subtype.irreducibleSpace Z.2.1
  isIntegral_of_irreducibleSpace _
instance isClosedImmersion_component_ι (Z : irreducibleComponents X) :
    IsClosedImmersion (component Z).ι :=
  .of_isPreimmersion _ (by simpa using isClosed_component Z)
variable (X) in

theorem iSup_component : ⨆ Z : irreducibleComponents X, component Z = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩
variable (X) in

theorem pairwise_disjoint_component :
    Pairwise fun Z W : irreducibleComponents X ↦ Disjoint (component Z) (component W) := by
  intro Z W hne
  rw [← Opens.coe_disjoint]
  exact pairwiseDisjoint_irreducibleComponents X Z.2 W.2 (fun h ↦ hne (Subtype.ext h))
variable (X) in

noncomputable def componentCover : X.OpenCover :=
  X.openCoverOfIsOpenCover component (iSup_component X)
@[simp]
theorem componentCover_X (Z : irreducibleComponents X) :
    (componentCover X).X Z = (component Z).toScheme := rfl
@[simp]
theorem componentCover_f (Z : irreducibleComponents X) :
    (componentCover X).f Z = (component Z).ι := rfl
instance isIntegral_componentCover_X (Z : (componentCover X).I₀) :
    IsIntegral ((componentCover X).X Z) :=
  isIntegral_component Z
instance finite_componentCover_index {X : Scheme.{u}} [IsNormalScheme X] [IsNoetherian X] :
    Finite (componentCover X).I₀ :=
  finite_irreducibleComponents X
variable (X) in

theorem nonempty_isColimit_component :
    Nonempty (IsColimit (Cofan.mk X fun Z : irreducibleComponents X ↦ (component Z).ι)) :=
  nonempty_isColimit_cofanMk_of _ (by simpa using iSup_component X)
    (by simpa [Function.onFun] using pairwise_disjoint_component X)
variable (X) in

instance isIso_sigmaDesc_component :
    IsIso (Sigma.desc fun Z : irreducibleComponents X ↦ (component Z).ι) :=
  (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp (nonempty_isColimit_component X)
end Components
theorem isIntegrallyClosed_of_isAffineOpen {X : Scheme.{u}} [IsNormalScheme X] {U : X.Opens}
    (hU : IsAffineOpen U) [IsDomain Γ(X, U)] : IsIntegrallyClosed Γ(X, U) :=
  (spec_iff_of_isDomain _).mp (spec_of_isAffineOpen hU)
theorem exists_germToFunctionField_eq_of_locally {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U] (t : X.functionField)
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (_ : Nonempty V) (s : Γ(X, V)),
      x ∈ V ∧ V ≤ U ∧ X.germToFunctionField V s = t) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = t := by
  choose V hV s hxV hVU hs using h
  have hg : ∀ (W : X.Opens) [Nonempty W], genericPoint X ∈ W := fun W h ↦
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)
  obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U ↦ V x.1 x.2) U
    (fun x ↦ homOfLE (hVU x.1 x.2))
    (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) (fun x ↦ s x.1 x.2) (fun x y ↦ by
      have := hV x.1 x.2
      have := hV y.1 y.2
      apply germ_injective_of_isIntegral X (genericPoint X) (U := V x.1 x.2 ⊓ V y.1 y.2)
        ⟨hg _, hg _⟩
      exact ((X.presheaf.germ_res_apply _ _ _ _).trans (hs x.1 x.2)).trans
        ((X.presheaf.germ_res_apply _ _ _ _).trans (hs y.1 y.2)).symm)
  obtain ⟨x⟩ := ‹Nonempty U›
  have := hV x.1 x.2
  refine ⟨a, ?_⟩
  rw [← hs x.1 x.2, ← ha x]
  exact (X.presheaf.germ_res_apply (homOfLE (hVU x.1 x.2)) _ (hg _) a).symm
instance isIntegrallyClosedIn_functionField {X : Scheme.{u}} [IsNormalScheme X] [IsIntegral X]
    (U : X.Opens) [Nonempty U] : IsIntegrallyClosedIn Γ(X, U) X.functionField := by
  refine isIntegrallyClosedIn_iff.mpr ⟨X.germToFunctionField_injective U, fun {t} ht ↦ ?_⟩
  refine exists_germToFunctionField_eq_of_locally U t fun x hx ↦ ?_
  obtain ⟨_, ⟨(V : X.Opens), hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  have := isIntegrallyClosed_of_isAffineOpen hV
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE (show V ≤ U from hVU)).op).hom.toAlgebra
  have : IsScalarTower Γ(X, U) Γ(X, V) X.functionField := .of_algebraMap_eq fun a ↦
    (X.presheaf.germ_res_apply (homOfLE (show V ≤ U from hVU)) _ _ a).symm
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := Γ(X, V)) ht.tower_top
  exact ⟨V, inferInstance, s, hxV, hVU, hs⟩
instance isIntegrallyClosed_sections {X : Scheme.{u}} [IsNormalScheme X] [IsIntegral X]
    (U : X.Opens) [Nonempty U] : IsIntegrallyClosed Γ(X, U) :=
  have : FaithfulSMul Γ(X, U) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (X.germToFunctionField_injective U)
  .of_isIntegrallyClosedIn _ X.functionField
instance isIntegrallyClosed_globalSections {X : Scheme.{u}} [IsNormalScheme X] [IsIntegral X] :
    IsIntegrallyClosed Γ(X, ⊤) :=
  have : Nonempty (⊤ : X.Opens) := ⟨Nonempty.some inferInstance, trivial⟩
  isIntegrallyClosed_sections ⊤
theorem isDomain_and_isIntegrallyClosed_of_isIrreducible {X : Scheme.{u}} [IsNormalScheme X]
    {U : X.Opens} (hU : IsIrreducible (U : Set X)) :
    IsDomain Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) := by
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hU
  have := isIntegral_of_irreducibleSpace U.toScheme
  exact (isDomain_and_isIntegrallyClosed_iff_of_ringEquiv
    U.topIso.commRingCatIsoToRingEquiv).mp ⟨inferInstance, inferInstance⟩
theorem isIntegrallyClosedIn_localization {A B Aₘ Bₘ : Type*} [CommRing A] [CommRing B]
    [CommRing Aₘ] [CommRing Bₘ] [Algebra A B] [Algebra A Aₘ] [Algebra B Bₘ] [Algebra Aₘ Bₘ]
    [Algebra A Bₘ] [IsScalarTower A B Bₘ] [IsScalarTower A Aₘ Bₘ] (M : Submonoid A)
    [IsLocalization M Aₘ] [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ]
    [IsIntegrallyClosedIn A B] : IsIntegrallyClosedIn Aₘ Bₘ := by
  have hinj : Function.Injective (algebraMap A B) := IsIntegralClosure.algebraMap_injective A A B
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {s} hs ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, e⟩ := IsLocalization.surj M x
    have h1 : algebraMap B Bₘ (algebraMap A B a) = 0 := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A Aₘ Bₘ, ← e, map_mul,
        hx, zero_mul]
    obtain ⟨⟨_, c, hc, rfl⟩, h2⟩ :=
      (IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid B M) Bₘ _).mp h1
    have h3 : c * a = 0 := hinj (by simpa using h2)
    have h4 : algebraMap A Aₘ a = 0 :=
      (IsLocalization.map_eq_zero_iff M Aₘ _).mpr ⟨⟨c, hc⟩, h3⟩
    rw [h4] at e
    exact (IsLocalization.map_units Aₘ m).mul_left_eq_zero.mp e
  · obtain ⟨⟨x, _, m₁, hm₁, rfl⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B M) s
    simp only [← IsScalarTower.algebraMap_apply] at e
    obtain ⟨⟨m₂, hm₂⟩, hm₂s⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hs
    simp only [Submonoid.smul_def, Algebra.smul_def] at hm₂s
    obtain ⟨m₃, hm₃, hm₃s⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map (Sₘ := Bₘ)
      M (x := m₂ • x) <| by
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← e, ← mul_assoc]
        exact hm₂s.mul isIntegral_algebraMap
    obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hm₃s
    let m : M := ⟨_, mul_mem hm₁ (mul_mem hm₂ hm₃)⟩
    refine ⟨IsLocalization.mk' Aₘ a m, ?_⟩
    have hu : IsUnit (algebraMap A Bₘ m) := by
      rw [IsScalarTower.algebraMap_apply A Aₘ Bₘ]
      exact (IsLocalization.map_units Aₘ m).map _
    apply hu.mul_right_cancel
    rw [IsScalarTower.algebraMap_apply A Aₘ Bₘ, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A B Bₘ a, ha]
    simp only [m, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← e]
    ring
theorem isDomain_and_isIntegrallyClosed_away {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [IsIntegrallyClosedIn A B] (a : A)
    [IsLocalization.Away (algebraMap A B a) C] [IsDomain C] [IsIntegrallyClosed C] :
    IsDomain (Localization.Away a) ∧ IsIntegrallyClosed (Localization.Away a) := by
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := .of_algebraMap_eq' rfl
  have hu : IsUnit (algebraMap A C a) := IsLocalization.Away.algebraMap_isUnit (algebraMap A B a)
  let : Algebra (Localization.Away a) C := (IsLocalization.Away.lift a hu).toAlgebra
  have : IsScalarTower A (Localization.Away a) C :=
    .of_algebraMap_eq' (IsLocalization.Away.lift_comp a hu).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid B (.powers a)) C := by
    rwa [Algebra.algebraMapSubmonoid_powers]
  have := isIntegrallyClosedIn_localization (B := B) (Aₘ := Localization.Away a) (Bₘ := C)
    (.powers a)
  have hinj : Function.Injective (algebraMap (Localization.Away a) C) :=
    IsIntegralClosure.algebraMap_injective _ (Localization.Away a) C
  have : FaithfulSMul (Localization.Away a) C :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact ⟨hinj.isDomain _, .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ C⟩
theorem exists_isIdempotentElem_basicOpen_eq {X : Scheme.{u}} {U V W : X.Opens}
    (hU : V ⊔ W = U) (hVW : Disjoint V W) :
    ∃ e : Γ(X, U), IsIdempotentElem e ∧ X.basicOpen e = V ∧ X.basicOpen (1 - e) = W := by
  have hV : V ≤ U := hU ▸ le_sup_left
  have hW : W ≤ U := hU ▸ le_sup_right
  have hs : ∀ T : X.Opens, T = ⊥ → Subsingleton Γ(X, T) := fun T hT ↦
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)
  obtain ⟨e, he, -⟩ := X.sheaf.existsUnique_gluing' (fun b : Bool ↦ cond b V W) U
    (fun b ↦ homOfLE (by cases b <;> assumption))
    (by rw [iSup_bool_eq]; exact hU.ge)
    (fun b ↦ match b with | true => (1 : Γ(X, V)) | false => (0 : Γ(X, W))) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact (hs _ (hVW.symm.eq_bot)).elim _ _
      · exact (hs _ (hVW.eq_bot)).elim _ _
      · rfl)
  replace he : ∃ e : Γ(X, U), X.presheaf.map (homOfLE hV).op e = 1 ∧
    X.presheaf.map (homOfLE hW).op e = 0 := ⟨e, he true, he false⟩
  clear e
  obtain ⟨e, h1, h0⟩ := he
  have key : ∀ {V W : X.Opens} (hV : V ≤ U) (hW : W ≤ U), V ⊔ W = U → ∀ e : Γ(X, U),
      X.presheaf.map (homOfLE hV).op e = 1 → X.presheaf.map (homOfLE hW).op e = 0 →
      X.basicOpen e = V := by
    intro V W hV hW hU e h1 h0
    have a1 := X.basicOpen_res e (homOfLE hV).op
    have a0 := X.basicOpen_res e (homOfLE hW).op
    rw [h1, X.basicOpen_one] at a1
    rw [h0, X.basicOpen_zero] at a0
    calc X.basicOpen e = (V ⊔ W) ⊓ X.basicOpen e := by
          rw [hU, inf_eq_right.mpr (X.basicOpen_le e)]
      _ = V := by rw [inf_sup_right, ← a1, ← a0, sup_bot_eq]
  refine ⟨e, ?_, key hV hW hU e h1 h0, key hW hV (sup_comm W V ▸ hU) _ ?_ ?_⟩
  · refine X.sheaf.eq_of_locally_eq₂ (homOfLE hV) (homOfLE hW) hU.ge _ _ ?_ ?_
    · change X.presheaf.map (homOfLE hV).op (e * e) = X.presheaf.map (homOfLE hV).op e
      rw [map_mul, h1, mul_one]
    · change X.presheaf.map (homOfLE hW).op (e * e) = X.presheaf.map (homOfLE hW).op e
      rw [map_mul, h0, mul_zero]
  · rw [map_sub, map_one, h0, sub_zero]
  · rw [map_sub, map_one, h1, sub_self]
theorem exists_algebraMap_eq_of_isIdempotentElem {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsIntegrallyClosedIn A B] {e : B} (he : IsIdempotentElem e) :
    ∃ a : A, algebraMap A B a = e := by
  refine IsIntegrallyClosedIn.algebraMap_eq_of_integral
    ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simp [mul_sub, he.eq]
theorem spec_of_isIntegrallyClosedIn {X : Scheme.{u}} [IsNormalScheme X] [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) (A : Type u) [CommRing A] [Algebra A Γ(X, U)]
    [IsIntegrallyClosedIn A Γ(X, U)] : IsNormalScheme (Spec (.of A)) := by
  classical
  have hinj : Function.Injective (algebraMap A Γ(X, U)) :=
    IsIntegralClosure.algebraMap_injective A A _
  let W (Z : irreducibleComponents X) : X.Opens := ⟨Z.1ᶜ, (isClosed_component Z).isOpen_compl⟩
  have H (Z : irreducibleComponents X) := exists_isIdempotentElem_basicOpen_eq (X := X) (U := U)
    (V := U ⊓ component Z) (W := U ⊓ W Z)
    (by
      refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx ↦ ?_
      by_cases h : x ∈ Z.1
      exacts [Or.inl ⟨hx, h⟩, Or.inr ⟨hx, h⟩])
    (by
      rw [← Opens.coe_disjoint]
      exact Set.disjoint_left.mpr fun x hx hx' ↦ hx'.2 hx.2)
  choose e he h1 h0 using H
  choose a ha using fun Z ↦ exists_algebraMap_eq_of_isIdempotentElem (A := A) (he Z)
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun Z : irreducibleComponents X ↦ Z.1)
    (fun Z ↦ isOpen_of_mem_irreducibleComponents Z.2) (fun x _ ↦ Set.mem_iUnion.mpr
      ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩)
  have hprod : ∏ Z ∈ s, (1 - a Z) = 0 := by
    apply hinj
    rw [map_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp (hs (X.basicOpen_le _ hx))
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun Z ↦ 1 - a Z) hZ
    rw [hc, map_mul, X.basicOpen_mul, map_sub, map_one, ha, h0] at hx
    exact hx.1.2 hxZ
  refine of_forall_exists_isOpenImmersion fun p ↦ ?_
  have hp := p.isPrime
  obtain ⟨Z, hZ⟩ : ∃ Z, a Z ∉ p.asIdeal := by
    by_contra! h
    obtain ⟨Z, -, hZ⟩ := (Ideal.IsPrime.prod_mem_iff (s := s) (x := fun Z ↦ 1 - a Z)
      (p := p.asIdeal)).mp (hprod ▸ p.asIdeal.zero_mem)
    exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using p.asIdeal.add_mem hZ (h Z)))
  have hne : X.basicOpen (e Z) ≠ ⊥ := fun h ↦ hZ <| by
    rw [basicOpen_eq_bot_iff, ← ha, map_eq_zero_iff _ hinj] at h
    exact h ▸ p.asIdeal.zero_mem
  have hirr : IsIrreducible (X.basicOpen (e Z) : Set X) :=
    ⟨(Opens.ne_bot_iff_nonempty _).mp hne,
      Z.2.1.2.open_subset (X.basicOpen (e Z)).isOpen (by rw [h1]; exact fun _ h ↦ h.2)⟩
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isIrreducible hirr
  have : IsLocalization.Away (algebraMap A Γ(X, U) (a Z)) Γ(X, X.basicOpen (e Z)) := by
    rw [ha]
    exact isLocalization_basicOpen_of_qcqs hU (.of_quasiSeparatedSpace _) (e Z)
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_away (B := Γ(X, U))
    (C := Γ(X, X.basicOpen (e Z))) (a Z)
  refine ⟨Spec (.of (Localization.Away (a Z))),
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (a Z)))), inferInstance,
    inferInstance, ?_⟩
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away (a Z))))
  rw [PrimeSpectrum.localization_away_comap_range _ (a Z)]
  exact hZ
instance normalization {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsNormalScheme X] [IsLocallyNoetherian X] : IsNormalScheme f.normalization :=
  (iff_of_openCover f.normalizationOpenCover).mpr fun U ↦
    letI := (f.app U.1).hom.toAlgebra
    spec_of_isIntegrallyClosedIn (f.isCompact_preimage U.2.isCompact)
      (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
instance sigma {ι : Type v} [Small.{u} ι] (X : ι → Scheme.{u}) [h : ∀ i, IsNormalScheme (X i)] :
    IsNormalScheme (∐ X) :=
  (iff_of_openCover (sigmaOpenCover X)).mpr h
instance coprod (X Y : Scheme.{u}) [IsNormalScheme X] [IsNormalScheme Y] :
    IsNormalScheme (X ⨿ Y) :=
  (iff_of_openCover (coprodOpenCover.{u, 0} X Y)).mpr fun i ↦ by
    rcases i with _ | _
    · exact inferInstanceAs (IsNormalScheme X)
    · exact inferInstanceAs (IsNormalScheme Y)
example : IsNormalScheme (Spec (.of ℤ)) := inferInstance
example : IsNormalScheme (Spec (.of (MvPolynomial (Fin 2) ℤ))) := inferInstance
example : IsNormalScheme (Spec (.of (ℚ × ℚ))) ∧ ¬ IsIntegral (Spec (.of (ℚ × ℚ))) :=
  ⟨of_isIso (coprodSpec ℚ ℚ), fun h ↦
    have : IsDomain (ℚ × ℚ) := (affine_isIntegral_iff _).mp h
    false_of_nontrivial_of_product_domain ℚ ℚ⟩
example : ¬ IsNormalScheme (Spec (.of (ZMod 4))) := fun _ ↦ by
  have : _root_.IsReduced (ZMod 4) := (affine_isReduced_iff (.of (ZMod 4))).mp inferInstance
  exact absurd (IsNilpotent.eq_zero (x := (2 : ZMod 4)) ⟨2, by decide⟩) (by decide)
example : ¬ IsNormalScheme (Spec (.of (ℤ√((5 : ℕ) : ℤ)))) := fun h ↦ by
  have : Zsqrtd.Nonsquare 5 := ⟨fun n hn ↦ by
    have : n ≤ 2 := by nlinarith
    interval_cases n <;> omega⟩
  have : IsIntegrallyClosed (ℤ√((5 : ℕ) : ℤ)) := (spec_iff_of_isDomain _).mp h
  have h1 : (⟨2, 0⟩ : ℤ√((5 : ℕ) : ℤ)) ^ 3 ∣ ⟨1, 1⟩ ^ 3 := ⟨⟨2, 1⟩, by decide⟩
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.pow_dvd_pow_iff three_ne_zero).mp h1
  have := congrArg Zsqrtd.re hc
  simp at this
  omega
example : IsNormalScheme
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))).normalization := inferInstance
example : ∃ x : Spec (.of ℤ), Order.coheight x = 1 ∧
    IsDiscreteValuationRing ((Spec (.of ℤ)).presheaf.stalk x) := by
  let x : Spec (.of ℤ) :=
    ⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two⟩
  have hx : Order.coheight x = 1 := by
    rw [← idealHeight_eq_coheight]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (R := ℤ)
      (mem_nonZeroDivisors_of_ne_zero two_ne_zero) Int.prime_two.not_unit
  exact ⟨x, hx, isDiscreteValuationRing_stalk hx⟩
example : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Spec (.of ℤ)) := pred _
example : ¬ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Spec (.of (ZMod 4))) := fun h ↦ by
  have := of_pred h
  have : _root_.IsReduced (ZMod 4) := (affine_isReduced_iff (.of (ZMod 4))).mp inferInstance
  exact absurd (IsNilpotent.eq_zero (x := (2 : ZMod 4)) ⟨2, by decide⟩) (by decide)
end IsNormalScheme
end GlobalTheory


