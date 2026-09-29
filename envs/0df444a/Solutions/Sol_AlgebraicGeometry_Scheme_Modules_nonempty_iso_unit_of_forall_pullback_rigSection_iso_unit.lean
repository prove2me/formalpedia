-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/3b6d7eb3-8d28-5c81-801d-0327b36ab0bf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard

namespace S1C
namespace NodeTriv

noncomputable def pb2 {X₀ X₁ X₂ : Scheme.{u}} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (L : X₂.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅ (Scheme.Modules.pullback (f ≫ g)).obj L :=
  (Scheme.Modules.pullbackComp f g).app L

theorem nonempty_iso_unit_of_iso_comp {X Y Y' : Scheme.{u}} {K : X.Modules} (f : Y ⟶ X) (f' : Y' ⟶ X) (e : Y' ⟶ Y)
    [IsIso e] (hef : e ≫ f = f')
    (h : Nonempty ((Scheme.Modules.pullback f).obj K ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f').obj K ≅ SheafOfModules.unit Y'.ringCatSheaf) :=
  ⟨(Scheme.Modules.pullbackCongr hef.symm).app K ≪≫ (pb2 e f K).symm ≪≫
    (Scheme.Modules.pullback e).mapIso h.some ≪≫ Scheme.Modules.pullbackUnitIso e⟩

theorem nonempty_iso_unit_of_iSup_eq_top_of_pairwise_disjoint
    {Y : Scheme.{u}} (N : Y.Modules) {ι' : Type*} (V : ι' → Y.Opens) (hV : ⨆ i, V i = ⊤)
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (htriv : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj N ≅ SheafOfModules.unit (V i).toScheme.ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  classical

  choose s hs using fun i => Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit (M := N) (V i) (htriv i).some

  let F : TopCat.Sheaf Ab Y.toPresheafedSpace := ⟨N.presheaf, N.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.val V s := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · have hbot : V i ⊓ V j = ⊥ := (hdisj hij).eq_bot
      apply F.eq_of_locally_eq' (fun e : PEmpty.{1} => e.elim) (V i ⊓ V j) (fun e => e.elim)
      · rw [hbot]; exact bot_le
      · intro e; exact e.elim
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) (by rw [hV]) s hcompat

  have hframe : ∀ i, Scheme.Modules.IsFrameOn (t : Γ(N, ⊤)) (V i) := by
    intro i W hWU hWV
    have key : N.presheaf.map (homOfLE hWU).op t = N.presheaf.map (homOfLE hWV).op (s i) := by
      rw [← ht i, ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    have hb := hs i hWV hWV
    simp only [← key] at hb
    exact hb
  have htop : Scheme.Modules.IsFrameOn (t : Γ(N, ⊤)) (⊤ : Y.Opens) := by
    have h := Scheme.Modules.IsFrameOn.of_iSup V hframe
    rwa [hV] at h
  obtain ⟨e⟩ := htop.nonempty_pullback_iso_unit ⊤ le_rfl le_rfl

  haveI : IsIso (⊤ : Y.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  refine ⟨((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id (⊤ : Y.Opens).ι).symm).app N ≪≫
    (pb2 (inv (⊤ : Y.Opens).ι) (⊤ : Y.Opens).ι N).symm ≪≫
    (Scheme.Modules.pullback (inv (⊤ : Y.Opens).ι)).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _⟩

theorem isOpenImmersion_of_rationalPoint
    {k : Type u} [Field k] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k))
    [IsSeparated z] [IsReduced Z] [DiscreteTopology Z]
    (ζ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z) : IsOpenImmersion ζ.1 := by
  haveI : IsClosedImmersion (ζ.1 ≫ z) := by rw [ζ.2]; infer_instance
  haveI : IsClosedImmersion ζ.1 := IsClosedImmersion.of_comp ζ.1 z

  let W : Z.Opens := ⟨{ζ.1.base (IsLocalRing.closedPoint k)}, isOpen_discrete _⟩
  have hfw : ∀ p : Spec (CommRingCat.of k), ζ.1.base p = ζ.1.base (IsLocalRing.closedPoint k) := fun p => by
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
  have hpre : ζ.1 ⁻¹ᵁ W = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, TopologicalSpace.Opens.coe_top, Set.mem_univ,
      iff_true]
    exact hfw p

  haveI : IsClosedImmersion (ζ.1 ∣_ W) := IsZariskiLocalAtTarget.restrict ‹_› W
  haveI : Surjective (ζ.1 ∣_ W) := ⟨fun y => ⟨⟨IsLocalRing.closedPoint k, by rw [hpre]; trivial⟩, by
    apply Subtype.ext
    rw [morphismRestrict_base_coe]
    have hy : y.1 = ζ.1.base (IsLocalRing.closedPoint k) := y.2
    exact hy.symm⟩⟩
  haveI : IsIso (ζ.1 ∣_ W) := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (ζ.1 ⁻¹ᵁ W).ι := by rw [hpre, ← Scheme.topIso_hom]; infer_instance
  have hfac : ζ.1 = inv (ζ.1 ⁻¹ᵁ W).ι ≫ (ζ.1 ∣_ W) ≫ W.ι := by
    rw [IsIso.eq_inv_comp, morphismRestrict_ι]
  rw [hfac]; infer_instance

end S1C.NodeTriv

open S1C.NodeTriv in
theorem solution
    {k : Type u} [Field k] {Z T : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k)) [IsSeparated z] [IsReduced Z] [Finite Z]
    (t : T ⟶ Spec (CommRingCat.of k)) {ι : Type v} (ζ : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z)
    (hcov : ∀ w : Z, ∃ j, (ζ j).1.base (IsLocalRing.closedPoint k) = w)
    (F : (Limits.pullback z t).Modules)
    (htriv : ∀ j, Nonempty ((Scheme.Modules.pullback (rigSection z t (ζ j))).obj F ≅ SheafOfModules.unit T.ringCatSheaf)) :
    Nonempty (F ≅ SheafOfModules.unit (Limits.pullback z t).ringCatSheaf) := by
  classical

  choose jw hjw using hcov

  have hci : ∀ j, IsClosedImmersion (ζ j).1 := fun j => by
    haveI : IsClosedImmersion ((ζ j).1 ≫ z) := by rw [(ζ j).2]; infer_instance
    exact IsClosedImmersion.of_comp (ζ j).1 z
  have hrange : ∀ j, Set.range (ζ j).1.base = {(ζ j).1.base (IsLocalRing.closedPoint k)} := fun j => by
    ext p
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q (IsLocalRing.closedPoint k)]
    · intro hp; exact ⟨IsLocalRing.closedPoint k, hp.symm⟩
  haveI : T1Space Z := ⟨fun w => by
    rw [← hjw w, ← hrange (jw w)]
    exact (hci (jw w)).base_closed.isClosed_range⟩
  haveI : DiscreteTopology Z := inferInstance
  haveI : ∀ j, IsOpenImmersion (ζ j).1 := fun j => isOpenImmersion_of_rationalPoint z (ζ j)

  let np : ∀ w : Z, pullback (pullback.fst z t) (ζ (jw w)).1 ⟶ pullback z t := fun w => pullback.fst _ _
  let V : ↥Z → (pullback z t).Opens := fun w => Scheme.Hom.opensRange (np w)
  have hVmem : ∀ w p, p ∈ V w ↔ (pullback.fst z t).base p = w := fun w p => by
    show p ∈ Set.range (np w).base ↔ _
    simp only [np]
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hrange, hjw, Set.mem_singleton_iff]
  have hVcov : ⨆ w, V w = ⊤ := by
    rw [eq_top_iff]
    rintro p -
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨(pullback.fst z t).base p, (hVmem _ p).mpr rfl⟩
  have hVdisj : Pairwise fun w w' => Disjoint (V w) (V w') := by
    intro w w' hww'
    rw [disjoint_iff, eq_bot_iff]
    rintro p ⟨hp, hp'⟩
    exact hww' (((hVmem w p).mp hp).symm.trans ((hVmem w' p).mp hp'))

  let n : ∀ w : Z, T ⟶ pullback z t := fun w => rigSection z t (ζ (jw w))
  have hn_fst : ∀ w, n w ≫ pullback.fst z t = t ≫ (ζ (jw w)).1 := fun w => by
    simp only [n, rigSection, pullback.lift_fst]
  have hn_snd : ∀ w, n w ≫ pullback.snd z t = 𝟙 _ := fun w => by
    simp only [n, rigSection, pullback.lift_snd]
  let e : ∀ w : Z, pullback (pullback.fst z t) (ζ (jw w)).1 ⟶ T := fun w => np w ≫ pullback.snd z t
  have he_t : ∀ w, e w ≫ t = pullback.snd (pullback.fst z t) (ζ (jw w)).1 := fun w => by
    simp only [e, np, Category.assoc]
    rw [← pullback.condition, pullback.condition_assoc, (ζ (jw w)).2, Category.comp_id]
  have he_n : ∀ w, e w ≫ n w = np w := fun w => by
    apply pullback.hom_ext
    · rw [Category.assoc, hn_fst, ← Category.assoc, he_t]
      simp only [np]
      exact pullback.condition.symm
    · rw [Category.assoc, hn_snd, Category.comp_id]
  let eInv : ∀ w : Z, T ⟶ pullback (pullback.fst z t) (ζ (jw w)).1 := fun w => pullback.lift (n w) t (hn_fst w)
  have hInv_np : ∀ w, eInv w ≫ np w = n w := fun w => by simp only [eInv, np, pullback.lift_fst]
  have h1 : ∀ w, eInv w ≫ e w = 𝟙 _ := fun w => by
    simp only [e]
    rw [← Category.assoc, hInv_np, hn_snd]
  have h2 : ∀ w, e w ≫ eInv w = 𝟙 _ := fun w => by
    apply pullback.hom_ext
    · rw [Category.assoc, hInv_np, he_n, Category.id_comp]
    · rw [Category.assoc, Category.id_comp]
      simp only [eInv, pullback.lift_snd]
      exact he_t w
  haveI : ∀ w, IsIso (e w) := fun w => ⟨⟨eInv w, h2 w, h1 w⟩⟩

  refine nonempty_iso_unit_of_iSup_eq_top_of_pairwise_disjoint F V hVcov hVdisj fun w => ?_
  have hpiece := nonempty_iso_unit_of_iso_comp (K := F) (n w) (np w) (e w) (he_n w) (htriv (jw w))
  exact nonempty_iso_unit_of_iso_comp (np w) (V w).ι (Scheme.Hom.isoOpensRange (np w)).inv
    (Scheme.Hom.isoOpensRange_inv_comp (np w)) hpiece

end S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit (solution)
