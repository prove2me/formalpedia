-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fc552dfc-a91f-56e7-92c7-f9cb97970e62

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Theorems.Thm_Module_ker_baseChange_field_of_subsingleton_H1
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

universe u

set_option autoImplicit false
section alpha_solution
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct

namespace AlphaSol

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

theorem map_map (M : V.Modules) {U U' U'' : V.Opens} (f : U' ⟶ U) (g : U'' ⟶ U') (k : U'' ⟶ U) (x : Γ(M, U)) :
    M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem d_zero_res (π : V ⟶ Spec (.of R)) (M : V.Modules) (K : V.OrderedAffineCover) (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (fun s => M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x) = 0 := by
  funext t
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  change _ + _ = (0 : Γ(M, K.inter t))
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, one_smul]
  change M.presheaf.map _ (M.presheaf.map _ x) + -(M.presheaf.map _ (M.presheaf.map _ x)) = 0
  rw [map_map M _ _ (homOfLE le_top), map_map M _ _ (homOfLE le_top), add_neg_cancel]

theorem app_map {M N : V.Modules} (φ : M ⟶ N) {U W : V.Opens} (i : W ⟶ U) (m : Γ(M, U)) :
    φ.app W (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app U m) := by
  have := ((PresheafOfModules.toPresheaf _).map φ.val).naturality i.op
  exact ConcreteCategory.congr_hom this m

theorem subsingleton_cochain (π : V ⟶ Spec (.of R)) (F : OModulePresheaf π) (K : V.OrderedAffineCover)
    {i : ℕ} (hi : Fintype.card K.ι < i + 1) : Subsingleton (F.cochain K i) := by
  haveI : IsEmpty (K.Idx i) := ⟨fun s => by
    have := Fintype.card_le_of_injective _ s.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  infer_instance

end AlphaSol

open AlphaSol in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfin : ∀ 𝒰 : X.OrderedAffineCover, (OModulePresheaf.ofModules f M).CechFinite 𝒰)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : ∀ 𝒲 : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).OrderedAffineCover,
      Subsingleton
        ((OModulePresheaf.ofModules (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            ((Scheme.Modules.pullback
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M)).HSucc 𝒲 0))
    {k : ℕ} (τ : Fin k → Γ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, ⊤)) :
    ∃ (N : ℕ) (m : Fin (N + 1) → Γ(M, ⊤)) (c : Fin k → Fin (N + 1) → K), ∀ i,
      τ i = ∑ j, ((Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop
                    ((Scheme.ΓSpecIso (.of K)).inv (c i j))) •
        (show Γ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).unit.app M).app ⊤) (m j)) := by
  classical

  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let pK := Limits.pullback.fst f ιK
  let fK := Limits.pullback.snd f ιK
  let MK := (Scheme.Modules.pullback pK).obj M
  let F := OModulePresheaf.ofModules f M
  let FK := OModulePresheaf.ofModules fK MK
  let uTop : Γ(M, ⊤) → FK.obj ⊤ := fun x =>
    show Γ(MK, ⊤) from (((Scheme.Modules.pullbackPushforwardAdjunction pK).unit.app M).app ⊤) x

  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨𝒰⟩ := Scheme.OrderedAffineCover.nonempty_of_compactSpace X
  let 𝒰K := 𝒰.baseChange f K

  let C : ℕ → Type u := fun i => F.cochain 𝒰 i
  let d : ∀ i, C i →ₗ[R] C (i + 1) := fun i => F.d 𝒰 i
  haveI hflat : ∀ i, Module.Flat R (C i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial f M hM.1 𝒰 i
  obtain ⟨E, hEd, hEt⟩ := OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial f 𝒰 M hM.1 K
  have hH1' : LinearMap.ker ((d 1).baseChange K) ≤ LinearMap.range ((d 0).baseChange K) := by
    intro v hv
    have htop : (LinearMap.range (FK.d 𝒰K 0)).comap (LinearMap.ker (FK.d 𝒰K 1)).subtype = ⊤ :=
      Submodule.Quotient.subsingleton_iff.1 (hH1 𝒰K)
    have hEv : E 1 v ∈ LinearMap.ker (FK.d 𝒰K 1) := by
      rw [LinearMap.mem_ker]
      have := congrArg (fun φ => φ v) (hEd 1)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
      rw [← this, LinearMap.mem_ker.1 hv, map_zero]
    have hmem : (⟨E 1 v, hEv⟩ : LinearMap.ker (FK.d 𝒰K 1)) ∈
        (LinearMap.range (FK.d 𝒰K 0)).comap (LinearMap.ker (FK.d 𝒰K 1)).subtype := by
      rw [htop]; trivial
    obtain ⟨z', hz'⟩ := hmem
    obtain ⟨y', rfl⟩ := (E 0).surjective z'
    refine ⟨y', (E 1).injective ?_⟩
    have := congrArg (fun φ => φ y') (hEd 0)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
    rw [this]
    exact hz'
  obtain ⟨hrange, -⟩ := Module.ker_baseChange_field_of_subsingleton_H1 R C d
    (fun i => OModulePresheaf.d_comp_d F 𝒰 i) (Fintype.card 𝒰.ι)
    (fun i hi => subsingleton_cochain f F 𝒰 (by omega)) (hfin 𝒰).1 (hfin 𝒰).2 K hH1'

  have hglob : ∀ x : LinearMap.ker (d 0), ∃! g : Γ(M, ⊤), ∀ s : 𝒰.Idx 0,
      (x.1 : F.cochain 𝒰 0) s = M.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op g := fun x =>
    (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique f M 𝒰 x.1).1 x.2
  choose g hg _hgu using hglob

  have key : ∀ i, ∃ S : Finset (K × LinearMap.ker (d 0)),
      (show FK.obj ⊤ from τ i) = ∑ q ∈ S, q.1 • uTop (g q.2) := by
    intro i

    let cK : FK.cochain 𝒰K 0 := fun s => MK.presheaf.map (homOfLE (le_top : 𝒰K.inter s ≤ ⊤)).op (τ i)
    have hcK : FK.d 𝒰K 0 cK = 0 := d_zero_res fK MK 𝒰K (τ i)
    let y := (E 0).symm cK
    have hy : (d 0).baseChange K y ∈ LinearMap.ker ((E 1).toLinearMap) := by
      rw [LinearMap.mem_ker, LinearEquiv.coe_coe]
      have := congrArg (fun φ => φ y) (hEd 0)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
      rw [this]
      show FK.d 𝒰K 0 (E 0 ((E 0).symm cK)) = 0
      rw [LinearEquiv.apply_symm_apply, hcK]
    have hy' : y ∈ LinearMap.ker ((d 0).baseChange K) := by
      rw [LinearMap.mem_ker]
      have : LinearMap.ker ((E 1).toLinearMap) = ⊥ := LinearEquiv.ker _
      rw [this] at hy
      exact hy
    rw [← hrange] at hy'
    obtain ⟨w, hw⟩ := hy'
    obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
    refine ⟨S, ?_⟩

    have hσ : ∀ s : 𝒰K.Idx 0, cK s = MK.presheaf.map (homOfLE (le_top : 𝒰K.inter s ≤ ⊤)).op
        (show Γ(MK, ⊤) from ∑ q ∈ S, q.1 • uTop (g q.2)) := by
      intro s
      have h1 : cK = E 0 y := ((E 0).apply_symm_apply cK).symm
      rw [h1, ← hw, hS, map_sum, map_sum]
      simp only [LinearMap.baseChange_tmul, Submodule.coe_subtype]
      rw [Finset.sum_apply]
      change ∑ q ∈ S, E 0 (q.1 ⊗ₜ[R] (q.2 : F.cochain 𝒰 0)) s = FK.res le_top (∑ q ∈ S, q.1 • uTop (g q.2))
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, hEt 0 q.1 (q.2 : F.cochain 𝒰 0) s]
      congr 1
      have hq : ((q.2 : F.cochain 𝒰 0) s : Γ(M, 𝒰.inter s)) =
          M.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op (g q.2) := hg q.2 s
      change MK.presheaf.map _ ((((Scheme.Modules.pullbackPushforwardAdjunction pK).unit.app M).app (𝒰.inter s))
        ((q.2 : F.cochain 𝒰 0) s : Γ(M, 𝒰.inter s))) = MK.presheaf.map _ (uTop (g q.2))
      rw [hq]
      erw [app_map ((Scheme.Modules.pullbackPushforwardAdjunction pK).unit.app M)
        (homOfLE (le_top : 𝒰.inter s ≤ ⊤)) (g q.2)]
      exact map_map MK _ _ _ _
    obtain ⟨x, hx, hxu⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique fK MK 𝒰K cK).1 hcK
    have e1 : τ i = x := hxu _ fun s => rfl
    have e2 : (show Γ(MK, ⊤) from ∑ q ∈ S, q.1 • uTop (g q.2)) = x := hxu _ hσ
    exact e1.trans e2.symm
  choose S hS using key

  let T : Finset (K × LinearMap.ker (d 0)) := Finset.univ.biUnion S
  let N := T.card
  let enum : Fin N ≃ T := (T.equivFin).symm
  let m : Fin (N + 1) → Γ(M, ⊤) := Fin.snoc (fun j => g (enum j).1.2) 0
  let c : Fin k → Fin (N + 1) → K := fun i => Fin.snoc (fun j => if (enum j).1 ∈ S i then (enum j).1.1 else 0) 0
  refine ⟨N, m, c, fun i => ?_⟩

  have hsmul : ∀ (a : K) (z : FK.obj ⊤), a • z =
      (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv a)) • (show Γ(MK, ⊤) from z) := by
    intro a z
    have happ : fK.appLE ⊤ ⊤ le_top = fK.appTop := (Scheme.Hom.app_eq_appLE fK).symm
    show ((Scheme.ΓSpecIso (.of K)).inv ≫ fK.appLE ⊤ ⊤ le_top).hom a • (show Γ(MK, ⊤) from z) = _
    rw [happ]
    rfl

  have step1 : (show FK.obj ⊤ from τ i) = ∑ q ∈ T, (if q ∈ S i then q.1 else 0) • uTop (g q.2) := by
    rw [hS i]
    have hsub : T ∩ S i = S i := Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem S (Finset.mem_univ i))
    have hite : ∀ q : K × LinearMap.ker (d 0),
        (if q ∈ S i then q.1 else 0) • uTop (g q.2) = if q ∈ S i then q.1 • uTop (g q.2) else 0 := by
      intro q
      split_ifs <;> simp
    simp_rw [hite]
    rw [Finset.sum_ite_mem, hsub]
  have step2 : ∑ q ∈ T, (if q ∈ S i then q.1 else 0) • uTop (g q.2) =
      ∑ j : Fin (N + 1), c i j • uTop (m j) := by
    rw [Fin.sum_univ_castSucc]
    simp only [m, c, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
    rw [← Finset.sum_coe_sort T, ← Equiv.sum_comp enum]
  change (show FK.obj ⊤ from τ i) = ∑ j, (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (c i j))) • uTop (m j)
  rw [step1, step2]
  exact Finset.sum_congr rfl fun j _ => hsmul _ _

end alpha_solution

end S_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc (solution)
