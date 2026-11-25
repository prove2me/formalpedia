-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateShapiro
-- name    : GroundTheory_TateCohomology_TateShapiro
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:24.393455+00:00
-- url     : https://prove2.me/theorems/00bc9ae9-77e7-4f41-a0a9-4b4dd9c48170
-- title:
--   Tate Shapiro
-- statement:
--   Definitions and structural lemmas for Tate Shapiro, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateShapiro.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_sum_coindBotProj
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_coind_bot
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_of_sum_eq
import Theorems.Thm_P2M_GroundTheory_GroupCoh___apply_norm_cd75b4d7bf64
import Theorems.Thm_P2M_GroundTheory_GroupCoh_barResolution___f_zero_single_ee18ab47ac91
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology groupHomology Rep HomologicalComplex
universe u
section Cochains
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
noncomputable abbrev resBarResolution : ProjectiveResolution (Rep.trivial k S k) :=
  (resFunctor S.subtype).mapProjectiveResolution (barResolution k G)
noncomputable def barHomotopyEquiv :
    HomotopyEquiv (barResolution k S).complex (resBarResolution (k := k) S).complex :=
  ProjectiveResolution.homotopyEquiv _ _
noncomputable def shapiroCochainsHomotopyEquiv (B : Rep.{u} k S) :
    HomotopyEquiv (inhomogeneousCochains B) (inhomogeneousCochains (coind S.subtype B)) :=
  (HomotopyEquiv.ofIso (inhomogeneousCochainsIso B)).trans
    ((linearYonedaObjHomotopyEquiv (barHomotopyEquiv (k := k) S) B).symm.trans
      ((HomotopyEquiv.ofIso (linearYonedaObjResProjectiveResolutionIso (barResolution k G) B)).trans
        (HomotopyEquiv.ofIso (inhomogeneousCochainsIso (coind S.subtype B)).symm)))
lemma shapiroCochains_hom_f_apply (B : Rep.{u} k S) (n : ℕ) (x : (Fin n → S) → B)
    (v : Fin n → G) (g : G) :
    ((((shapiroCochainsHomotopyEquiv S B).hom.f n).hom x v).1 g) =
      (freeLift k S B x).hom (((barHomotopyEquiv (k := k) S).inv.f n).hom
        (Finsupp.single v (MonoidAlgebra.single g 1))) := by
  change (freeLiftLEquiv k G (Fin n → G) (coind S.subtype B) (resCoindHomEquiv.{u} S.subtype _ B
    ((barHomotopyEquiv (k := k) S).inv.f n ≫ (freeLiftLEquiv k S (Fin n → S) B).symm x)) v).1 g = _
  erw [resCoindToHom_hom_apply_coe]
  simp
  rfl
noncomputable def trivialToInvariant (B : Rep.{u} k S) (c : B) (hc : ∀ s : S, B.ρ s c = c) :
    Rep.trivial k S k ⟶ B :=
  Rep.ofHom ⟨LinearMap.toSpanSingleton k B c, fun s => by ext; simp [hc]⟩
lemma freeLift_const_eq (B : Rep.{u} k S) (c : B) (hc : ∀ s : S, B.ρ s c = c) :
    freeLift k S B (fun _ : Fin 0 → S => c) =
      (barResolution k S).π.f 0 ≫ trivialToInvariant S B c hc := by
  refine free_ext _ _ _ _ _ fun i => ?_
  change _ = (trivialToInvariant S B c hc).hom (((barResolution k S).π.f 0).hom
    (Finsupp.single i (MonoidAlgebra.single 1 1)))
  rw [barResolution_π_f_zero_single]
  simp [trivialToInvariant]
lemma shapiroCochains_hom_f_zero_const (B : Rep.{u} k S) (c : B) (hc : ∀ s : S, B.ρ s c = c)
    (v : Fin 0 → G) (g : G) :
    ((((shapiroCochainsHomotopyEquiv S B).hom.f 0).hom (fun _ => c) v).1 g) = c := by
  rw [shapiroCochains_hom_f_apply, freeLift_const_eq S B c hc]
  have h := ProjectiveResolution.lift_commutes_zero (𝟙 (Rep.trivial k S k))
    (resBarResolution (k := k) S) (barResolution k S)
  have h3 := congrArg (fun φ => φ.hom (Finsupp.single v (MonoidAlgebra.single g (1 : k)))) h
  simp at h3
  change (trivialToInvariant S B c hc).hom (((barResolution k S).π.f 0).hom
    (((barHomotopyEquiv (k := k) S).inv.f 0).hom (Finsupp.single v (MonoidAlgebra.single g 1)))) = c
  erw [h3]
  simp only [trivialToInvariant]
  have h4 := barResolution_π_f_zero_single (k := k) v g 1
  change (show k from ((barResolution k G).π.f 0).hom
    (Finsupp.single v (MonoidAlgebra.single g 1))) • c = c
  rw [h4, one_smul]
end Cochains
section Unit
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
open scoped Classical in

noncomputable def toResCoind (B : Rep.{u} k S) : B ⟶ res S.subtype (coind S.subtype B) :=
  Rep.ofHom ⟨LinearMap.codRestrict _
    (LinearMap.pi fun g : G => if h : g ∈ S then B.ρ ⟨g, h⟩ else 0) (fun b => by
      rw [Representation.mem_coindV]
      intro s x
      by_cases hx : x ∈ S
      · have hsx : (S.subtype s) * x ∈ S := S.mul_mem s.2 hx
        simp only [LinearMap.pi_apply, dif_pos hx, dif_pos hsx]
        rw [← Module.End.mul_apply, ← map_mul]
        rfl
      · have hsx : (S.subtype s) * x ∉ S := fun h => hx (by
          simpa using S.mul_mem (S.inv_mem s.2) h)
        simp only [LinearMap.pi_apply, dif_neg hx, dif_neg hsx, LinearMap.zero_apply, map_zero]),
    fun s => LinearMap.ext fun b => Subtype.ext (funext fun x => by
      by_cases hx : x ∈ S
      · have hxs : x * (S.subtype s) ∈ S := S.mul_mem hx s.2
        change (if h : x ∈ S then B.ρ ⟨x, h⟩ else 0) (B.ρ s b) =
          (if h : x * (S.subtype s) ∈ S then B.ρ ⟨x * (S.subtype s), h⟩ else 0) b
        rw [dif_pos hx, dif_pos hxs, ← Module.End.mul_apply, ← map_mul]
        rfl
      · have hxs : x * (S.subtype s) ∉ S := fun h => hx (by
          simpa using S.mul_mem h (S.inv_mem s.2))
        change (if h : x ∈ S then B.ρ ⟨x, h⟩ else 0) (B.ρ s b) =
          (if h : x * (S.subtype s) ∈ S then B.ρ ⟨x * (S.subtype s), h⟩ else 0) b
        rw [dif_neg hx, dif_neg hxs]
        rfl)⟩
open scoped Classical in

lemma toResCoind_apply (B : Rep.{u} k S) (b : B) (x : G) :
    ((toResCoind S B).hom b).1 x = if h : x ∈ S then B.ρ ⟨x, h⟩ b else 0 := by
  change (if h : x ∈ S then B.ρ ⟨x, h⟩ else 0) b = _
  split_ifs <;> rfl
variable [Fintype G] [Fintype S]
open scoped Classical in

lemma sum_toResCoind (B : Rep.{u} k S) (b : B) (g : G) :
    ∑ h : G, ((toResCoind S B).hom b).1 (g * h) = B.ρ.norm b := by
  rw [show (∑ h : G, ((toResCoind S B).hom b).1 (g * h)) =
      ∑ h : G, ((toResCoind S B).hom b).1 h from
    Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => rfl]
  refine (Finset.sum_congr rfl fun h _ => toResCoind_apply S B b h).trans ?_
  rw [← Fintype.sum_subtype_add_sum_subtype (fun h : G => h ∈ S)]
  have h0 : ∑ h : {x // ¬ x ∈ S}, (if hh : (h : G) ∈ S then B.ρ ⟨h, hh⟩ b else 0) = 0 :=
    Finset.sum_eq_zero fun h _ => dif_neg h.2
  rw [h0, add_zero, Representation.norm, LinearMap.sum_apply]
  exact Finset.sum_congr (by convert rfl) fun h _ => dif_pos h.2
lemma shapiro_comm_zero (B : Rep.{u} k S) :
    (chainsMap S.subtype (toResCoind S B)).f 0 ≫ (tateComplexConnectData (coind S.subtype B)).d₀ =
      (tateComplexConnectData B).d₀ ≫ (shapiroCochainsHomotopyEquiv S B).hom.f 0 := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun v b => ?_)
  refine funext fun w => Subtype.ext (funext fun g => ?_)
  have e1 : ((tateComplexConnectData B).d₀).hom (Finsupp.single v b) = fun _ => B.ρ.norm b := by
    simp [Rep.tateNorm_eq]
    rfl
  have e2 : ((tateComplexConnectData (coind S.subtype B)).d₀).hom
      (((chainsMap S.subtype (toResCoind S B)).f 0).hom (Finsupp.single v b)) =
      fun _ => (coind S.subtype B).ρ.norm ((toResCoind S B).hom b) := by
    rw [chainsMap_f_single]
    simp [Rep.tateNorm_eq]
    rfl
  change (((tateComplexConnectData (coind S.subtype B)).d₀).hom
      (((chainsMap S.subtype (toResCoind S B)).f 0).hom (Finsupp.single v b)) w).1 g =
    (((shapiroCochainsHomotopyEquiv S B).hom.f 0).hom
      (((tateComplexConnectData B).d₀).hom (Finsupp.single v b)) w).1 g
  rw [e1, e2, shapiroCochains_hom_f_zero_const S B _ (fun s => ρ_apply_norm B b s),
    Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  exact sum_toResCoind S B b g
end Unit
section TateMap
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
noncomputable def tateShapiroMap (B : Rep.{u} k S) :
    tateComplex B ⟶ tateComplex (coind S.subtype B) :=
  CochainComplex.ConnectData.map _ _ (chainsMap S.subtype (toResCoind S B))
    (shapiroCochainsHomotopyEquiv S B).hom (shapiro_comm_zero S B)
omit [Fintype G] [Fintype S] in

lemma toResCoind_naturality {B B' : Rep.{u} k S} (φ : B ⟶ B') :
    toResCoind S B ≫ (resFunctor S.subtype).map (coindMap S.subtype φ) = φ ≫ toResCoind S B' := by
  classical
  ext b : 3
  refine Subtype.ext (funext fun x => ?_)
  change (φ.hom (((toResCoind S B).hom b).1 x)) = ((toResCoind S B').hom (φ.hom b)).1 x
  rw [toResCoind_apply, toResCoind_apply]
  split_ifs with hx
  · exact hom_comm_apply φ _ _
  · exact map_zero _
omit [Fintype G] [Fintype S] in

lemma freeLift_comp_hom {H : Type u} [Group H] {B B' : Rep.{u} k H} (φ : B ⟶ B') {α : Type u}
    (x : α → B) : freeLift k H B x ≫ φ = freeLift k H B' (fun a => φ.hom (x a)) :=
  free_ext _ _ _ _ _ fun i => by simp
omit [Fintype G] [Fintype S] in

lemma shapiroCochains_naturality {B B' : Rep.{u} k S} (φ : B ⟶ B') :
    (shapiroCochainsHomotopyEquiv S B).hom ≫ cochainsMap (MonoidHom.id G) (coindMap S.subtype φ) =
      cochainsMap (MonoidHom.id S) φ ≫ (shapiroCochainsHomotopyEquiv S B').hom := by
  ext n x : 3
  refine funext fun v => Subtype.ext (funext fun g => ?_)
  change φ.hom ((((shapiroCochainsHomotopyEquiv S B).hom.f n).hom x v).1 g) =
    (((shapiroCochainsHomotopyEquiv S B').hom.f n).hom (fun a => φ.hom (x a)) v).1 g
  rw [shapiroCochains_hom_f_apply, shapiroCochains_hom_f_apply, ← freeLift_comp_hom]
  rfl
lemma tateShapiroMap_naturality {B B' : Rep.{u} k S} (φ : B ⟶ B') :
    tateShapiroMap S B ≫ tateComplex.map (coindMap S.subtype φ) =
      tateComplex.map φ ≫ tateShapiroMap S B' := by
  ext (m | m) : 1
  · exact congrArg (fun f => f.f m) (shapiroCochains_naturality S φ)
  · change (chainsMap S.subtype (toResCoind S B) ≫ chainsMap (MonoidHom.id G)
      (coindMap S.subtype φ)).f m = (chainsMap (MonoidHom.id S) φ ≫
        chainsMap S.subtype (toResCoind S B')).f m
    rw [← chainsMap_comp, ← chainsMap_comp]
    have h1 : (MonoidHom.id G).comp S.subtype = S.subtype.comp (MonoidHom.id S) := by
      ext; rfl
    exact congrArg (fun f => f.f m) (chainsMap_congr h1
      (congrArg (fun f => f.hom.toLinearMap) (toResCoind_naturality S φ)))
end TateMap
section Homology
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
lemma isIso_homologyMap_tateShapiroMap_of_pos (B : Rep.{u} k S) (n : ℕ) [NeZero n] :
    IsIso (HomologicalComplex.homologyMap (tateShapiroMap S B) (n : ℤ)) := by
  rw [tateShapiroMap,
    CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _ _ n (n : ℤ) rfl]
  have : IsIso (HomologicalComplex.homologyMap (shapiroCochainsHomotopyEquiv S B).hom n) :=
    (inferInstance : IsIso ((shapiroCochainsHomotopyEquiv S B).toHomologyIso n).hom)
  infer_instance
@[simps]
noncomputable def tateShapiroMapShortComplex (X : ShortComplex (Rep.{u} k S)) :
    X.map (tateComplexFunctor k S) ⟶
      (X.map (coindFunctor k S.subtype)).map (tateComplexFunctor k G) where
  τ₁ := tateShapiroMap S X.X₁
  τ₂ := tateShapiroMap S X.X₂
  τ₃ := tateShapiroMap S X.X₃
  comm₁₂ := tateShapiroMap_naturality S X.f
  comm₂₃ := tateShapiroMap_naturality S X.g
omit [Fintype S] in

lemma shortExact_map_coindFunctor {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) :
    (X.map (coindFunctor k S.subtype)).ShortExact := by
  classical
  have : (coindFunctor k S.subtype).IsRightAdjoint :=
    (Rep.resCoindAdjunction.{u, u} k S.subtype).isRightAdjoint
  have : (coindFunctor k S.subtype).IsLeftAdjoint := (Rep.coindResAdjunction k S).isLeftAdjoint
  have := hX.mono_f
  have := hX.epi_g
  exact hX.map (coindFunctor k S.subtype)
lemma tateShapiroMap_δ {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ HomologicalComplex.homologyMap (tateShapiroMap S X.X₁) (n + 1) =
      HomologicalComplex.homologyMap (tateShapiroMap S X.X₃) n ≫
        TateCohomology.δ (shortExact_map_coindFunctor S hX) n :=
  HomologicalComplex.HomologySequence.δ_naturality (tateShapiroMapShortComplex S X)
    (TateCohomology.map_tateComplexFunctor_shortExact hX)
    (TateCohomology.map_tateComplexFunctor_shortExact (shortExact_map_coindFunctor S hX))
    n (n + 1) rfl
end Homology
section Shift
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
noncomputable def coindNormLift (M : Rep.{u} k S) (φ : M.V →ₗ[k] M.V) :
    (coind S.subtype M).V →ₗ[k] (coind S.subtype M).V :=
  (toResCoind S M).hom.toLinearMap ∘ₗ φ ∘ₗ
    (LinearMap.proj (1 : G) ∘ₗ (Representation.coindV S.subtype M.ρ).subtype)
lemma sum_coindNormLift (M : Rep.{u} k S) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ s : S, M.ρ s (φ (M.ρ s⁻¹ m)) = m) (f : coind S.subtype M) :
    ∑ g : G, (coind S.subtype M).ρ g (coindNormLift S M φ ((coind S.subtype M).ρ g⁻¹ f)) = f := by
  classical
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ g : G, ((toResCoind S M).hom (φ (f.1 (1 * g⁻¹)))).1 (x * g) = f.1 x
  have step : ∀ g : G, ((toResCoind S M).hom (φ (f.1 (1 * g⁻¹)))).1 (x * g) =
      if h : x * g ∈ S then M.ρ ⟨x * g, h⟩ (φ (f.1 g⁻¹)) else 0 := fun g => by
    rw [toResCoind_apply, one_mul]
  rw [Finset.sum_congr rfl fun g _ => step g]
  rw [show (∑ g : G, if h : x * g ∈ S then M.ρ ⟨x * g, h⟩ (φ (f.1 g⁻¹)) else 0) =
      ∑ h : G, if hh : h ∈ S then M.ρ ⟨h, hh⟩ (φ (f.1 (h⁻¹ * x))) else 0 from
    Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun g => by
      simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right]]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun h : G => h ∈ S)]
  have h0 : ∑ h : {y // ¬ y ∈ S},
      (if hh : (h : G) ∈ S then M.ρ ⟨h, hh⟩ (φ (f.1 ((h : G)⁻¹ * x))) else 0) = 0 :=
    Finset.sum_eq_zero fun h _ => dif_neg h.2
  rw [h0, add_zero]
  conv_rhs => rw [← hφ (f.1 x)]
  refine Finset.sum_congr (by convert rfl) fun s _ => ?_
  rw [dif_pos s.2]
  congr 2
  exact f.2 s⁻¹ x
theorem tateAcyclic_coind_of_sum_eq (M : Rep.{u} k S) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ s : S, M.ρ s (φ (M.ρ s⁻¹ m)) = m) : TateAcyclic (coind S.subtype M) :=
  tateAcyclic_of_sum_eq _ (coindNormLift S M φ) (sum_coindNormLift S M φ hφ)
omit [Fintype G] in

lemma fromCoindRes_id_surjective (B : Rep.{u} k S) :
    Function.Surjective (fromCoindRes B LinearMap.id).hom := by
  classical
  intro b
  refine ⟨⟨Pi.single (1 : S) b, fun t y => ?_⟩, ?_⟩
  · obtain rfl : t = 1 := Subsingleton.elim _ _
    simp
  · change (fromCoindRes B LinearMap.id).hom.toLinearMap ⟨Pi.single (1 : S) b, _⟩ = b
    simp only [fromCoindRes, Rep.hom_ofHom, LinearMap.sum_apply, LinearMap.comp_apply]
    change ∑ x : S, B.ρ x⁻¹ ((Pi.single (1 : S) b : S → (B : Type u)) x) = b
    rw [Fintype.sum_eq_single 1 fun x hx => by simp [hx]]
    simp
noncomputable abbrev coindBotShiftShortComplex (B : Rep.{u} k S) : ShortComplex (Rep.{u} k S) :=
  ShortComplex.mk (kernel.ι (fromCoindRes B LinearMap.id)) (fromCoindRes B LinearMap.id)
    (kernel.condition _)
omit [Fintype G] in

lemma coindBotShiftShortComplex_shortExact (B : Rep.{u} k S) :
    (coindBotShiftShortComplex S B).ShortExact := by
  have : Epi (fromCoindRes B LinearMap.id) :=
    (Rep.epi_iff_surjective _).2 (fromCoindRes_id_surjective S B)
  exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
theorem isIso_homologyMap_tateShapiroMap (B : Rep.{u} k S) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (tateShapiroMap S B) n) := by
  suffices h : ∀ m : ℕ, ∀ B : Rep.{u} k S,
      IsIso (HomologicalComplex.homologyMap (tateShapiroMap S B) (1 - m)) by
    rcases le_or_gt n 1 with hn | hn
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = 1 - m := ⟨(1 - n).toNat, by omega⟩
      exact h m B
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = ((m + 1 : ℕ) : ℤ) := ⟨(n - 1).toNat, by omega⟩
      exact isIso_homologyMap_tateShapiroMap_of_pos S B (m + 1)
  intro m
  induction m with
  | zero =>
    intro B
    simpa using isIso_homologyMap_tateShapiroMap_of_pos S B 1
  | succ m ih =>
    intro B
    have hX := coindBotShiftShortComplex_shortExact S B
    have e : (1 - ((m + 1 : ℕ) : ℤ)) + 1 = 1 - (m : ℤ) := by push_cast; ring
    have h1 : IsIso (HomologicalComplex.homologyMap
        (tateShapiroMap S (coindBotShiftShortComplex S B).X₁) ((1 - ((m + 1 : ℕ) : ℤ)) + 1)) := by
      rw [e]
      exact ih _
    have hδ1 := isIso_δ_of_tateAcyclic hX (tateAcyclic_coind_bot _) (1 - ((m + 1 : ℕ) : ℤ))
    have hδ2 := isIso_δ_of_tateAcyclic (shortExact_map_coindFunctor S hX)
      (tateAcyclic_coind_of_sum_eq S _ _ (sum_coindBotProj _)) (1 - ((m + 1 : ℕ) : ℤ))
    have key := tateShapiroMap_δ S hX (1 - ((m + 1 : ℕ) : ℤ))
    have h4 : IsIso (TateCohomology.δ hX (1 - ((m + 1 : ℕ) : ℤ)) ≫
        HomologicalComplex.homologyMap (tateShapiroMap S (coindBotShiftShortComplex S B).X₁)
          ((1 - ((m + 1 : ℕ) : ℤ)) + 1)) := @IsIso.comp_isIso _ _ _ _ _ _ _ hδ1 h1
    rw [key] at h4
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hδ2 h4
attribute [instance] isIso_homologyMap_tateShapiroMap
end Shift
section Main
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
noncomputable def tateShapiroNatIso (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := S) n ≅
      coindFunctor k S.subtype ⋙ tateCohomologyFunctor n :=
  NatIso.ofComponents
    (fun B => @asIso _ _ _ _ (HomologicalComplex.homologyMap (tateShapiroMap S B) n)
      (isIso_homologyMap_tateShapiroMap S B n))
    fun {B B'} f => by
      change HomologicalComplex.homologyMap (tateComplex.map f) n ≫
          HomologicalComplex.homologyMap (tateShapiroMap S B') n =
        HomologicalComplex.homologyMap (tateShapiroMap S B) n ≫
          HomologicalComplex.homologyMap (tateComplex.map (coindMap S.subtype f)) n
      rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
        tateShapiroMap_naturality]
noncomputable def tateCoindNatIso (n : ℤ) :
    coindFunctor k S.subtype ⋙ tateCohomologyFunctor n ≅
      tateCohomologyFunctor (R := k) (G := S) n :=
  (tateShapiroNatIso S n).symm
noncomputable def tateCoindIso (B : Rep.{u} k S) (n : ℤ) :
    tateCohomology (coind S.subtype B) n ≅ tateCohomology B n :=
  (tateCoindNatIso S n).app B
end Main
section Ind
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [Fintype G] [Fintype S]
open scoped Classical in

noncomputable def tateIndNatIso (n : ℤ) :
    indFunctor k S.subtype ⋙ tateCohomologyFunctor n ≅
      tateCohomologyFunctor (R := k) (G := S) n :=
  Functor.isoWhiskerRight (indCoindNatIso k S) (tateCohomologyFunctor n) ≪≫ tateCoindNatIso S n
noncomputable def tateIndIso (B : Rep.{u} k S) (n : ℤ) :
    tateCohomology (ind S.subtype B) n ≅ tateCohomology B n :=
  (tateIndNatIso S n).app B
omit [Fintype S] in

lemma shortExact_map_indFunctor {X : ShortComplex (Rep.{u} k S)} (hX : X.ShortExact) :
    (X.map (indFunctor k S.subtype)).ShortExact := by
  classical
  have : (indFunctor k S.subtype).IsLeftAdjoint :=
    (Rep.indResAdjunction k S.subtype).isLeftAdjoint
  have : (indFunctor k S.subtype).IsRightAdjoint := (Rep.resIndAdjunction k S).isRightAdjoint
  have := hX.mono_f
  have := hX.epi_g
  exact hX.map (indFunctor k S.subtype)
end Ind
end GroundTheory.GroupCoh


