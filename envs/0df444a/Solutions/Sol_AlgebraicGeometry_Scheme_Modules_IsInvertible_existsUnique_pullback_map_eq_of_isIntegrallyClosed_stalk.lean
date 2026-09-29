-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/adee2736-435f-5343-9aa9-959ce1d4283c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.Modules.pullback Scheme.Modules.Hom Scheme Scheme.Modules.Hom.isIso_iff_isIso_app Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Opens Scheme.Opens.opensRange_ι Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforward Modules.pullback Hom Γ Modules.Hom Modules.Hom.isIso_iff_isIso_app Modules.pullbackPushforwardAdjunction Modules Opens Opens.opensRange_ι Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom isSheaf Hom.isIso_iff_isIso_app pullbackPushforwardAdjunction IsInvertible IsFrameOn pullbackLocalSection pullbackLocalSection_zero pullbackLocalSection_sub pullbackLocalSection_smul map_homOfLE_pullbackLocalSection IsInvertible.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk exists_isFrameOn_of_pullback_iso_unit"
namespace NormalS2
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma map_map {M : X.Modules} {A B C : X.Opens} (i : B ⟶ A) (j : C ⟶ B) (s : Γ(M, A)) :
    M.presheaf.map j.op (M.presheaf.map i.op s) = M.presheaf.map (j ≫ i).op s := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

lemma map_congr {M : X.Modules} {A B : X.Opens} (i j : B ⟶ A) (s : Γ(M, A)) :
    M.presheaf.map i.op s = M.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]

lemma map_id' {M : X.Modules} {A : X.Opens} (i : A ⟶ A) (s : Γ(M, A)) : M.presheaf.map i.op s = s := by
  rw [Subsingleton.elim i (𝟙 A), op_id, M.presheaf.map_id]
  rfl

lemma bijective_map_of_eq {M : X.Modules} {A B : X.Opens} (h : B = A) :
    Function.Bijective (M.presheaf.map (homOfLE h.le).op) := by
  subst h
  have : (fun s : Γ(M, B) => M.presheaf.map (homOfLE le_rfl).op s) = id := funext fun s => map_id' _ s
  change Function.Bijective (fun s : Γ(M, B) => M.presheaf.map (homOfLE le_rfl).op s)
  rw [this]
  exact Function.bijective_id

noncomputable def shf (M : X.Modules) : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

lemma bijective_smul_of_isFrameOn {M : X.Modules} {A : X.Opens} {e : Γ(M, A)} (he : IsFrameOn e A) :
    Function.Bijective fun g : Γ(X, A) => g • e := by
  have hb := he le_rfl le_rfl
  have hid : (fun g : Γ(X, A) => g • M.presheaf.map (homOfLE le_rfl).op e) = fun g => g • e :=
    funext fun g => by rw [map_id']
  rwa [hid] at hb

section InsideU

variable (U : X.Opens) {L : X.Modules}

lemma preimage_inf_eq (W : X.Opens) : U.ι ⁻¹ᵁ (W ⊓ U) = U.ι ⁻¹ᵁ W := by
  ext x
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h; exact ⟨h, x.2⟩

lemma bijective_pl_of_frame {O W : X.Opens} (e : Γ(L, O)) (he : IsFrameOn e O) (hWO : W ≤ O) (hWU : W ≤ U) :
    Function.Bijective (fun s : Γ(L, W) => pullbackLocalSection U.ι s) := by
  have heW : IsFrameOn (L.presheaf.map (homOfLE hWO).op e) W := (he.map _).mono hWO
  have heι : IsFrameOn (pullbackLocalSection U.ι (L.presheaf.map (homOfLE hWO).op e)) (U.ι ⁻¹ᵁ W) :=
    heW.pullbackLocalSection U.ι
  have hB1 := bijective_smul_of_isFrameOn heW
  have hB2 := bijective_smul_of_isFrameOn heι
  have hι : Function.Bijective (U.ι.app W) := by
    haveI := U.ι.isIso_app W (by rw [Scheme.Opens.opensRange_ι]; exact hWU)
    exact ConcreteCategory.bijective_of_isIso (U.ι.app W)
  have hcomp : (fun s : Γ(L, W) => pullbackLocalSection U.ι s) ∘
      (fun g : Γ(X, W) => g • L.presheaf.map (homOfLE hWO).op e) =
      (fun h : Γ(U, U.ι ⁻¹ᵁ W) => h • pullbackLocalSection U.ι (L.presheaf.map (homOfLE hWO).op e)) ∘
        (fun g => U.ι.app W g) := by
    funext g
    simp only [Function.comp_apply, pullbackLocalSection_smul]
  rw [← Function.Bijective.of_comp_iff _ hB1, hcomp]
  exact hB2.comp hι

lemma injective_pl (O : X → X.Opens) (e : ∀ x, Γ(L, O x)) (hxO : ∀ x, x ∈ O x)
    (he : ∀ x, IsFrameOn (e x) (O x)) (W : X.Opens) (hWU : W ≤ U) :
    Function.Injective (fun s : Γ(L, W) => pullbackLocalSection U.ι s) := by
  intro s t hst
  rw [← sub_eq_zero] at hst ⊢
  change pullbackLocalSection U.ι s - pullbackLocalSection U.ι t = 0 at hst
  rw [← pullbackLocalSection_sub] at hst
  set d := s - t
  have hcov : W ≤ ⨆ x : X, W ⊓ O x := fun y hy => Opens.mem_iSup.mpr ⟨y, ⟨hy, hxO y⟩⟩
  apply (shf L).eq_of_locally_eq' (fun x : X => W ⊓ O x) W (fun x => homOfLE inf_le_left) hcov
  intro x
  change L.presheaf.map (homOfLE (inf_le_left : W ⊓ O x ≤ W)).op d =
    L.presheaf.map (homOfLE (inf_le_left : W ⊓ O x ≤ W)).op 0
  rw [map_zero]
  apply (bijective_pl_of_frame U (e x) (he x) (inf_le_right : W ⊓ O x ≤ O x) (inf_le_left.trans hWU)).1
  change pullbackLocalSection U.ι _ = pullbackLocalSection U.ι _
  rw [pullbackLocalSection_zero, ← map_homOfLE_pullbackLocalSection, hst, map_zero]

lemma bijective_pl (hL : IsInvertible L) (W : X.Opens) (hWU : W ≤ U) :
    Function.Bijective (fun s : Γ(L, W) => pullbackLocalSection U.ι s) := by
  have hfr : ∀ x : X, ∃ (O : X.Opens) (e : Γ(L, O)), x ∈ O ∧ IsFrameOn e O := fun x => by
    obtain ⟨O, hxO, ⟨eO⟩⟩ := hL.exists_trivialization x
    obtain ⟨e, he⟩ := exists_isFrameOn_of_pullback_iso_unit O eO
    exact ⟨O, e, hxO, he⟩
  choose O e hxO he using hfr
  refine ⟨injective_pl U O e hxO he W hWU, ?_⟩
  intro τ

  have hloc : ∀ x : X, ∃ t : Γ(L, W ⊓ O x), pullbackLocalSection U.ι t =
      ((Modules.pullback U.ι).obj L).presheaf.map
        (homOfLE (U.ι.preimage_mono (inf_le_left : W ⊓ O x ≤ W))).op τ :=
    fun x => (bijective_pl_of_frame U (e x) (he x) (inf_le_right : W ⊓ O x ≤ O x) (inf_le_left.trans hWU)).2 _
  choose t ht using hloc

  have hcompat : TopCat.Presheaf.IsCompatible L.presheaf (fun x : X => W ⊓ O x) t := by
    intro x y
    apply injective_pl U O e hxO he ((W ⊓ O x) ⊓ (W ⊓ O y)) (inf_le_left.trans (inf_le_left.trans hWU))
    change pullbackLocalSection U.ι (L.presheaf.map _ (t x)) = pullbackLocalSection U.ι (L.presheaf.map _ (t y))
    rw [map_congr _ (homOfLE (inf_le_left : (W ⊓ O x) ⊓ (W ⊓ O y) ≤ W ⊓ O x)) (t x),
      map_congr _ (homOfLE (inf_le_right : (W ⊓ O x) ⊓ (W ⊓ O y) ≤ W ⊓ O y)) (t y),
      ← map_homOfLE_pullbackLocalSection, ← map_homOfLE_pullbackLocalSection, ht, ht, map_map, map_map]
    rfl

  have hcov : W ≤ ⨆ x : X, W ⊓ O x := fun y hy => Opens.mem_iSup.mpr ⟨y, ⟨hy, hxO y⟩⟩
  obtain ⟨s, hs, -⟩ := (shf L).existsUnique_gluing' (fun x : X => W ⊓ O x) W (fun x => homOfLE inf_le_left)
    hcov t hcompat
  refine ⟨s, ?_⟩

  have hcovι : U.ι ⁻¹ᵁ W ≤ ⨆ x : X, U.ι ⁻¹ᵁ (W ⊓ O x) :=
    fun y hy => Opens.mem_iSup.mpr ⟨U.ι.base y, ⟨hy, hxO _⟩⟩
  apply (shf ((Modules.pullback U.ι).obj L)).eq_of_locally_eq' (fun x : X => U.ι ⁻¹ᵁ (W ⊓ O x)) (U.ι ⁻¹ᵁ W)
    (fun x => homOfLE (U.ι.preimage_mono inf_le_left)) hcovι
  intro x
  change ((Modules.pullback U.ι).obj L).presheaf.map _ (pullbackLocalSection U.ι s) =
    ((Modules.pullback U.ι).obj L).presheaf.map _ τ
  rw [map_homOfLE_pullbackLocalSection U.ι (inf_le_left : W ⊓ O x ≤ W)]
  have hsx : L.presheaf.map (homOfLE (inf_le_left : W ⊓ O x ≤ W)).op s = t x := hs x
  rw [hsx, ht]

end InsideU

section Unit

variable [IsLocallyNoetherian X]
  (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
  (U : X.Opens) (hU : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)

include hX hU in
theorem isIso_unit {L : X.Modules} (hL : IsInvertible L) :
    IsIso ((pullbackPushforwardAdjunction U.ι).unit.app L) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun s : Γ(L, W) => pullbackLocalSection U.ι s)

  have hH : Function.Bijective (L.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) :=
    IsInvertible.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk W U (fun x _ => hX x)
      (fun x _ hdim => hU x hdim) hL
  have hI := bijective_pl U hL (W ⊓ U) inf_le_right
  have hr : Function.Bijective (((Modules.pullback U.ι).obj L).presheaf.map
      (homOfLE (U.ι.preimage_mono (inf_le_left : W ⊓ U ≤ W))).op) := by
    have h := bijective_map_of_eq (M := (Modules.pullback U.ι).obj L) (preimage_inf_eq U W)
    exact h
  have hfac : (fun s' => ((Modules.pullback U.ι).obj L).presheaf.map
      (homOfLE (U.ι.preimage_mono (inf_le_left : W ⊓ U ≤ W))).op s') ∘
      (fun s : Γ(L, W) => pullbackLocalSection U.ι s) =
      (fun s : Γ(L, W ⊓ U) => pullbackLocalSection U.ι s) ∘
        (fun s => L.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op s) := by
    funext s
    simp only [Function.comp_apply]
    exact map_homOfLE_pullbackLocalSection U.ι inf_le_left s
  rw [← Function.Bijective.of_comp_iff' hr, hfac]
  exact hI.comp hH

end Unit

section Main

variable [IsLocallyNoetherian X]
  (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
  (U : X.Opens) (hU : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
  {L L' : X.Modules} (hL : IsInvertible L) (hL' : IsInvertible L')
  (φ : (Modules.pullback U.ι).obj L ⟶ (Modules.pullback U.ι).obj L')

include hX hU hL hL' in
theorem main :
    (∃! ψ : L ⟶ L', (Modules.pullback U.ι).map ψ = φ) ∧
      ∀ ψ : L ⟶ L', (Modules.pullback U.ι).map ψ = φ → IsIso φ → IsIso ψ := by

  obtain ⟨θ', hθ'₁, hθ'₂⟩ := (isIso_unit hX U hU hL').out
  obtain ⟨θ, hθ₁, hθ₂⟩ := (isIso_unit hX U hU hL).out
  let ηL' : L' ≅ (Modules.pushforward U.ι).obj ((Modules.pullback U.ι).obj L') :=
    { hom := (pullbackPushforwardAdjunction U.ι).unit.app L'
      inv := θ'
      hom_inv_id := hθ'₁
      inv_hom_id := hθ'₂ }
  let ηL : L ≅ (Modules.pushforward U.ι).obj ((Modules.pullback U.ι).obj L) :=
    { hom := (pullbackPushforwardAdjunction U.ι).unit.app L
      inv := θ
      hom_inv_id := hθ₁
      inv_hom_id := hθ₂ }

  set φb : L ⟶ (Modules.pushforward U.ι).obj ((Modules.pullback U.ι).obj L') :=
    (pullbackPushforwardAdjunction U.ι).homEquiv _ _ φ with hφb

  have hnat : ∀ ψ : L ⟶ L',
      (pullbackPushforwardAdjunction U.ι).homEquiv _ _ ((Modules.pullback U.ι).map ψ) = ψ ≫ ηL'.hom := by
    intro ψ
    rw [Adjunction.homEquiv_unit]
    have h := (pullbackPushforwardAdjunction U.ι).unit.naturality ψ
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h
    exact h.symm
  have key : ∀ ψ : L ⟶ L', (Modules.pullback U.ι).map ψ = φ ↔ ψ ≫ ηL'.hom = φb := by
    intro ψ
    constructor
    · intro h
      rw [← hnat, h]
    · intro h
      apply ((pullbackPushforwardAdjunction U.ι).homEquiv _ _).injective
      rw [hnat, h]

  have hψ₀ : (φb ≫ ηL'.inv) ≫ ηL'.hom = φb := by
    rw [Category.assoc, ηL'.inv_hom_id, Category.comp_id]
  have huniq : ∀ ψ : L ⟶ L', (Modules.pullback U.ι).map ψ = φ → ψ = φb ≫ ηL'.inv := by
    intro ψ h
    calc ψ = ψ ≫ (ηL'.hom ≫ ηL'.inv) := by rw [ηL'.hom_inv_id, Category.comp_id]
      _ = (ψ ≫ ηL'.hom) ≫ ηL'.inv := (Category.assoc _ _ _).symm
      _ = φb ≫ ηL'.inv := by rw [(key ψ).mp h]
  refine ⟨⟨φb ≫ ηL'.inv, (key _).mpr hψ₀, huniq⟩, ?_⟩

  intro ψ h hφ
  haveI := hφ
  have hφb' : φb = ηL.hom ≫ (Modules.pushforward U.ι).map φ := Adjunction.homEquiv_unit _ _ _ _
  rw [huniq ψ h, hφb', Category.assoc]
  refine ⟨⟨ηL'.hom ≫ (Modules.pushforward U.ι).map (inv φ) ≫ ηL.inv, ?_, ?_⟩⟩
  · simp only [Category.assoc]
    rw [ηL'.inv_hom_id_assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      ηL.hom_inv_id]
  · simp only [Category.assoc]
    rw [ηL.inv_hom_id_assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
      ηL'.hom_inv_id]

end Main

end AlgebraicGeometry.Scheme.Modules.NormalS2

theorem solution
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U)
    {L L' : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (φ : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj L') :
    (∃! ψ : L ⟶ L', (Scheme.Modules.pullback U.ι).map ψ = φ) ∧
      ∀ ψ : L ⟶ L', (Scheme.Modules.pullback U.ι).map ψ = φ → IsIso φ → IsIso ψ :=
  AlgebraicGeometry.Scheme.Modules.NormalS2.main hX U hU hL hL' φ

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk (solution)
