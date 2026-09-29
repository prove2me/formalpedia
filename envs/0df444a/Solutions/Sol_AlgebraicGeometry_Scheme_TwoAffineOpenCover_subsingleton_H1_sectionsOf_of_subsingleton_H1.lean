-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_subsingleton_H1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0f3dc2d6-e717-5f87-a480-7defc415487c

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_subsingleton_H1
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_subsingleton_H1.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf IsAffine Spec Scheme IsOpenImmersion IsSeparated Scheme.Hom.isIso_app isAffineOpen_top isAffineHom_diagonal_iff Scheme.Modules.pullbackPushforwardAdjunction Scheme.Hom.preimage_image_eq IsAffineOpen Scheme.Modules Scheme.Opens IsAffineHom Scheme.Opens.opensRange_ι toSpecΓ Scheme.Hom.image_le_opensRange Scheme.TwoAffineOpenCover OModulePresheaf OModulePresheaf.d_apply OModulePresheaf.ofModules OModulePresheaf.ofModules_res_apply Scheme.Modules.IsInvertible Scheme.Modules.bijective_unit_app_of_le_opensRange OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pushforward Modules.pullback Hom mk Γ Hom.isAffineOpen_iff_of_isOpenImmersion Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.naturality Hom.isIso_app Modules.pullbackPushforwardAdjunction Hom.preimage_image_eq Modules Opens Opens.opensRange_ι Hom.image_le_opensRange PresheafOfModules toSpecΓ TwoAffineOpenCover OrderedAffineCover Modules.IsInvertible Modules.bijective_unit_app_of_le_opensRange"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom isSheaf pullbackPushforwardAdjunction IsFrameOn IsInvertible bijective_unit_app_of_le_opensRange"
namespace CoverIndep
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (m : Γ(M, V)) :
    N.presheaf.map i.op (φ.app V m) = φ.app U (M.presheaf.map i.op m) := by
  have h := PresheafOfModules.Hom.naturality φ.val i.op
  have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) m
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h'
  exact h'.symm

theorem comp_app_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) (m : Γ(M, U)) :
    (φ ≫ ψ).app U m = ψ.app U (φ.app U m) := rfl

theorem zero_app_apply {M N : X.Modules} (U : X.Opens) (m : Γ(M, U)) : (0 : M ⟶ N).app U m = 0 := rfl

section OpenImm

variable {X' : Scheme.{u}} (p : X' ⟶ X) [IsOpenImmersion p] (M : X.Modules)

abbrev η : M ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M

abbrev pull (V : X.Opens) (m : Γ(M, V)) : Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ V) := (η p M).app V m

theorem pull_smul (V : X.Opens) (c : Γ(X, V)) (m : Γ(M, V)) :
    pull p M V (c • m) = p.app V c • pull p M V m := by
  rw [pull, Scheme.Modules.Hom.app_smul]
  rfl

theorem pull_add (V : X.Opens) (m m' : Γ(M, V)) : pull p M V (m + m') = pull p M V m + pull p M V m' := map_add _ _ _
theorem pull_sub (V : X.Opens) (m m' : Γ(M, V)) : pull p M V (m - m') = pull p M V m - pull p M V m' := map_sub _ _ _
theorem pull_zero (V : X.Opens) : pull p M V 0 = 0 := map_zero _

theorem map_pull {U V : X.Opens} (h : U ≤ V) (m : Γ(M, V)) :
    ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE ((Opens.map p.base).monotone h)).op (pull p M V m)
      = pull p M U (M.presheaf.map (homOfLE h).op m) := by
  rw [pull, pull, ← app_naturality (η p M) (homOfLE h) m]
  rfl

theorem pull_bijective (V : X.Opens) (hV : V ≤ p.opensRange) : Function.Bijective (pull p M V) :=
  Scheme.Modules.bijective_unit_app_of_le_opensRange p M V hV

theorem app_bijective (V : X.Opens) (hV : V ≤ p.opensRange) : Function.Bijective (p.app V) := by
  haveI := Scheme.Hom.isIso_app p V hV
  exact ConcreteCategory.bijective_of_isIso (p.app V)

theorem isFrameOn_pull {V : X.Opens} (hV : V ≤ p.opensRange) (s : Γ(M, V)) (hs : IsFrameOn s V) :
    IsFrameOn (pull p M V s) (p ⁻¹ᵁ V) := by
  intro W' hW'U hW'V

  have hWV : p ''ᵁ W' ≤ V := by
    have h1 : p ''ᵁ W' ≤ p ''ᵁ p ⁻¹ᵁ V := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨y, hW'U hy, rfl⟩
    calc p ''ᵁ W' ≤ p ''ᵁ p ⁻¹ᵁ V := h1
      _ = p.opensRange ⊓ V := Scheme.Hom.image_preimage_eq_opensRange_inf p V
      _ ≤ V := inf_le_right
  have hWr : p ''ᵁ W' ≤ p.opensRange := Scheme.Hom.image_le_opensRange p W'
  have hpre : p ⁻¹ᵁ p ''ᵁ W' = W' := Scheme.Hom.preimage_image_eq p W'

  have hsq : (pull p M (p ''ᵁ W')) ∘ (fun g : Γ(X, p ''ᵁ W') => g • M.presheaf.map (homOfLE hWV).op s)
      = (fun g' : Γ(X', p ⁻¹ᵁ p ''ᵁ W') =>
          g' • ((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE ((Opens.map p.base).monotone hWV)).op
            (pull p M V s)) ∘ (p.app (p ''ᵁ W')) := by
    funext g
    simp only [Function.comp_apply]
    rw [pull_smul, map_pull]
  have h1 : Function.Bijective ((pull p M (p ''ᵁ W')) ∘
      (fun g : Γ(X, p ''ᵁ W') => g • M.presheaf.map (homOfLE hWV).op s)) :=
    (pull_bijective p M _ hWr).comp (hs hWV hWV)
  rw [hsq] at h1
  have h2 := (Function.Bijective.of_comp_iff _ (app_bijective p _ hWr)).mp h1

  clear hsq h1
  revert h2
  generalize_proofs e1
  revert e1
  rw [hpre]
  intro e1 h2
  exact h2

end OpenImm

section PFam

variable {n : ℕ} (P : Fin n → X.Opens)

abbrev P2 (i j : Fin n) : X.Opens := P i ⊓ P j
abbrev P3 (i j k : Fin n) : X.Opens := P i ⊓ P j ⊓ P k

theorem P3_le_left (i j k : Fin n) : P3 P i j k ≤ P i := inf_le_left.trans inf_le_left
theorem P3_le_mid (i j k : Fin n) : P3 P i j k ≤ P j := inf_le_left.trans inf_le_right
theorem P3_le_right (i j k : Fin n) : P3 P i j k ≤ P k := inf_le_right

end PFam

section Transport

variable (N : X.Modules) (U : X.Opens) (hU : IsAffineOpen U) {n : ℕ} (P : Fin n → X.Opens)
  (hPU : ∀ i, P i ≤ U) (haff : ∀ i, IsAffineOpen (P i)) (hcov : U ≤ ⨆ i, P i)

def cover : (U : Scheme.{u}).OrderedAffineCover where
  ι := ULift.{u} (Fin n)
  instLinearOrder := LinearOrder.lift' ULift.down ULift.down_injective
  U i := U.ι ⁻¹ᵁ P i.down
  isAffineOpen i := by
    have himg : U.ι ''ᵁ (U.ι ⁻¹ᵁ P i.down) = P i.down := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr (hPU i.down)]
    have := haff i.down
    rw [← himg] at this
    exact (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).mp this
  iSup_eq_top := by
    apply top_unique
    intro y _
    have hy : U.ι.base y ∈ U := y.2
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hy)
    exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩

theorem cover_U (i : ULift.{u} (Fin n)) : (cover U P hPU haff hcov).U i = U.ι ⁻¹ᵁ P i.down := rfl

abbrev F : OModulePresheaf (U : Scheme.{u}).toSpecΓ :=
  OModulePresheaf.ofModules (U : Scheme.{u}).toSpecΓ ((Scheme.Modules.pullback U.ι).obj N)

omit hU hPU haff hcov in

theorem isQuasicoherent_F
    (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj N ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)) :
    (F N U).IsQuasicoherent := by
  refine OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial _ _ fun y => ?_
  have hinv : Scheme.Modules.IsInvertible N := ⟨htriv⟩
  obtain ⟨V, sV, hxV, hfr⟩ := hinv.exists_isFrameOn (U.ι.base y)

  let V' : X.Opens := V ⊓ U
  have hV'r : V' ≤ U.ι.opensRange := by rw [Scheme.Opens.opensRange_ι]; exact inf_le_right
  have hfr' : IsFrameOn (N.presheaf.map (homOfLE (inf_le_left : V' ≤ V)).op sV) V' :=
    (hfr.map (homOfLE (inf_le_left : V' ≤ V))).mono inf_le_left
  have hfr'' := isFrameOn_pull U.ι N hV'r _ hfr'
  have hy : y ∈ U.ι ⁻¹ᵁ V' := ⟨hxV, y.2⟩
  exact ⟨U.ι ⁻¹ᵁ V', hy, hfr''.nonempty_pullback_iso_unit (U.ι ⁻¹ᵁ V') le_rfl le_rfl⟩

variable (u : ∀ i j, Γ(N, P2 P i j))

theorem inter_le_pre (σ : (cover U P hPU haff hcov).Idx 1) :
    (cover U P hPU haff hcov).inter σ ≤ U.ι ⁻¹ᵁ P2 P (σ.1 0).down (σ.1 1).down := fun y hy =>
  ⟨(cover U P hPU haff hcov).inter_le σ 0 hy, (cover U P hPU haff hcov).inter_le σ 1 hy⟩

def u' : (F N U).cochain (cover U P hPU haff hcov) 1 := fun σ =>
  ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE (inter_le_pre U P hPU haff hcov σ)).op
    (pull U.ι N (P2 P (σ.1 0).down (σ.1 1).down) (u (σ.1 0).down (σ.1 1).down))

theorem F_res_apply {O O' : (U : Scheme.{u}).Opens} (h : O ≤ O') (x : (F N U).obj O') :
    (F N U).res h x = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE h).op x :=
  OModulePresheaf.ofModules_res_apply _ _ h x

set_option maxHeartbeats 6400000 in

theorem res_u'_eq (τ : (cover U P hPU haff hcov).Idx 2) (j : Fin 3) (a b : Fin n)
    (e0 : (((cover U P hPU haff hcov).face τ j).1 0).down = a) (e1 : (((cover U P hPU haff hcov).face τ j).1 1).down = b)
    (h3 : (cover U P hPU haff hcov).inter τ ≤ U.ι ⁻¹ᵁ P3 P (τ.1 0).down (τ.1 1).down (τ.1 2).down)
    (hab3 : P3 P (τ.1 0).down (τ.1 1).down (τ.1 2).down ≤ P2 P a b) :
    (F N U).res ((cover U P hPU haff hcov).inter_le_inter_face τ j) (u' N U P hPU haff hcov u ((cover U P hPU haff hcov).face τ j))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE h3).op
          (pull U.ι N (P3 P (τ.1 0).down (τ.1 1).down (τ.1 2).down) (N.presheaf.map (homOfLE hab3).op (u a b))) := by
  subst e0; subst e1
  rw [F_res_apply, u', ← map_pull]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem face_val (τ : (cover U P hPU haff hcov).Idx 2) (j : Fin 3) (k : Fin 2) :
    ((cover U P hPU haff hcov).face τ j).1 k = τ.1 (j.succAbove k) := rfl

theorem d_u' (hcoc : ∀ i j k : Fin n,
      N.presheaf.map (homOfLE (le_inf (P3_le_mid P i j k) (P3_le_right P i j k))).op (u j k)
        - N.presheaf.map (homOfLE (le_inf (P3_le_left P i j k) (P3_le_right P i j k))).op (u i k)
        + N.presheaf.map (homOfLE (le_inf (P3_le_left P i j k) (P3_le_mid P i j k))).op (u i j) = 0) :
    (F N U).d (cover U P hPU haff hcov) 1 (u' N U P hPU haff hcov u) = 0 := by
  funext τ
  have h3 : (cover U P hPU haff hcov).inter τ ≤ U.ι ⁻¹ᵁ P3 P (τ.1 0).down (τ.1 1).down (τ.1 2).down := fun y hy =>
    ⟨⟨(cover U P hPU haff hcov).inter_le τ 0 hy, (cover U P hPU haff hcov).inter_le τ 1 hy⟩, (cover U P hPU haff hcov).inter_le τ 2 hy⟩
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
  rw [res_u'_eq N U P hPU haff hcov u τ 0 (τ.1 1).down (τ.1 2).down rfl rfl h3
      (le_inf (P3_le_mid P _ _ _) (P3_le_right P _ _ _)),
    res_u'_eq N U P hPU haff hcov u τ 1 (τ.1 0).down (τ.1 2).down rfl rfl h3
      (le_inf (P3_le_left P _ _ _) (P3_le_right P _ _ _)),
    res_u'_eq N U P hPU haff hcov u τ 2 (τ.1 0).down (τ.1 1).down rfl rfl h3
      (le_inf (P3_le_left P _ _ _) (P3_le_mid P _ _ _))]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_one_smul, Pi.zero_apply]
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_smul, ← sub_eq_add_neg]
  have key2 := congrArg (pull U.ι N (P3 P (τ.1 0).down (τ.1 1).down (τ.1 2).down))
    (hcoc (τ.1 0).down (τ.1 1).down (τ.1 2).down)
  rw [pull_add, pull_sub, pull_zero] at key2
  have key3 := congrArg (((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE h3).op) key2
  rw [map_add, map_sub, map_zero] at key3
  exact key3

def idx0 (i : Fin n) : (cover U P hPU haff hcov).Idx 0 :=
  ⟨fun _ => ⟨i⟩, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩

theorem pre_le_inter_idx0 (i : Fin n) : U.ι ⁻¹ᵁ P i ≤ (cover U P hPU haff hcov).inter (idx0 U P hPU haff hcov i) :=
  le_iInf fun _ => le_rfl

def idx1 {a b : Fin n} (hab : a < b) : (cover U P hPU haff hcov).Idx 1 :=
  ⟨![(⟨a⟩ : ULift.{u} (Fin n)), ⟨b⟩], by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · exact absurd hxy (lt_irrefl _)
    · change a < b
      exact hab
    · exact absurd hxy (by decide)
    · exact absurd hxy (lt_irrefl _)⟩

theorem face_idx1_zero {a b : Fin n} (hab : a < b) :
    (cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 0 = idx0 U P hPU haff hcov b := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem face_idx1_one {a b : Fin n} (hab : a < b) :
    (cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 1 = idx0 U P hPU haff hcov a := by
  apply Subtype.ext; funext k; fin_cases k; rfl

theorem inter_idx1 {a b : Fin n} (hab : a < b) :
    (cover U P hPU haff hcov).inter (idx1 U P hPU haff hcov hab) = U.ι ⁻¹ᵁ P2 P a b := by
  refine le_antisymm (inter_le_pre U P hPU haff hcov _) (le_iInf fun k => ?_)
  fin_cases k
  · exact fun y hy => hy.1
  · exact fun y hy => hy.2

theorem res_at_eq (c : (F N U).cochain (cover U P hPU haff hcov) 0) {σ τ : (cover U P hPU haff hcov).Idx 0} (e : σ = τ)
    {O : (U : Scheme.{u}).Opens} (hσ : O ≤ (cover U P hPU haff hcov).inter σ) (hτ : O ≤ (cover U P hPU haff hcov).inter τ) :
    (F N U).res hσ (c σ) = (F N U).res hτ (c τ) := by
  subst e; rfl

theorem map_injective_of_eq (N : (U : Scheme.{u}).Modules) {W W' : (U : Scheme.{u}).Opens} (h : W = W') (hle : W ≤ W') :
    Function.Injective (N.presheaf.map (homOfLE hle).op) := by
  subst h
  intro a b hab
  have : (homOfLE hle) = 𝟙 W := rfl
  rw [this, op_id, N.presheaf.map_id] at hab
  exact hab

theorem exists_v (v' : (F N U).cochain (cover U P hPU haff hcov) 0)
    (hv' : (F N U).d (cover U P hPU haff hcov) 0 v' = u' N U P hPU haff hcov u) :
    ∃ v : ∀ i, Γ(N, P i), ∀ a b : Fin n, a < b →
      u a b = N.presheaf.map (homOfLE inf_le_right).op (v b) - N.presheaf.map (homOfLE inf_le_left).op (v a) := by
  have hDr : ∀ i, P i ≤ U.ι.opensRange := fun i => by
    rw [Scheme.Opens.opensRange_ι]; exact hPU i

  let w : ∀ i, Γ((Scheme.Modules.pullback U.ι).obj N, U.ι ⁻¹ᵁ P i) := fun i =>
    (F N U).res (pre_le_inter_idx0 U P hPU haff hcov i) (v' (idx0 U P hPU haff hcov i))
  choose v hv using fun i => (pull_bijective U.ι N (P i) (hDr i)).2 (w i)
  refine ⟨v, fun a b hab => ?_⟩

  have hcomp := congrFun hv' (idx1 U P hPU haff hcov hab)
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two] at hcomp
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul] at hcomp
  have hle2 : (cover U P hPU haff hcov).inter (idx1 U P hPU haff hcov hab) ≤ U.ι ⁻¹ᵁ P2 P a b :=
    (inter_idx1 U P hPU haff hcov hab).le

  have hb' : (F N U).res ((cover U P hPU haff hcov).inter_le_inter_face (idx1 U P hPU haff hcov hab) 0)
        (v' ((cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 0))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (N.presheaf.map (homOfLE inf_le_right).op (v b))) := by
    rw [res_at_eq N U P hPU haff hcov v' (face_idx1_zero U P hPU haff hcov hab) _
      (hle2.trans (((Opens.map U.ι.base).monotone inf_le_right).trans (pre_le_inter_idx0 U P hPU haff hcov b))),
      ← (F N U).res_res ((hle2.trans ((Opens.map U.ι.base).monotone inf_le_right))) (pre_le_inter_idx0 U P hPU haff hcov b)]
    change (F N U).res _ (w b) = _
    rw [← hv b, F_res_apply, ← map_pull]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have ha' : (F N U).res ((cover U P hPU haff hcov).inter_le_inter_face (idx1 U P hPU haff hcov hab) 1)
        (v' ((cover U P hPU haff hcov).face (idx1 U P hPU haff hcov hab) 1))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (N.presheaf.map (homOfLE inf_le_left).op (v a))) := by
    rw [res_at_eq N U P hPU haff hcov v' (face_idx1_one U P hPU haff hcov hab) _
      (hle2.trans (((Opens.map U.ι.base).monotone inf_le_left).trans (pre_le_inter_idx0 U P hPU haff hcov a))),
      ← (F N U).res_res ((hle2.trans ((Opens.map U.ι.base).monotone inf_le_left))) (pre_le_inter_idx0 U P hPU haff hcov a)]
    change (F N U).res _ (w a) = _
    rw [← hv a, F_res_apply, ← map_pull]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  rw [hb', ha'] at hcomp

  have hu' : u' N U P hPU haff hcov u (idx1 U P hPU haff hcov hab)
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (u a b)) := rfl
  rw [hu', ← sub_eq_add_neg] at hcomp
  have hcomp' : ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
        (pull U.ι N (P2 P a b)
          (N.presheaf.map (homOfLE inf_le_right).op (v b) - N.presheaf.map (homOfLE inf_le_left).op (v a)))
      = ((Scheme.Modules.pullback U.ι).obj N).presheaf.map (homOfLE hle2).op
          (pull U.ι N (P2 P a b) (u a b)) := by
    rw [pull_sub, map_sub]
    exact hcomp
  have hinj1 := map_injective_of_eq U ((Scheme.Modules.pullback U.ι).obj N) (inter_idx1 U P hPU haff hcov hab) hle2
  have hinj2 := (pull_bijective U.ι N (P2 P a b) ((inf_le_left).trans (hDr a))).1
  exact (hinj2 (hinj1 hcomp')).symm

end Transport

section TwoPieces

variable (N : X.Modules) (U : X.Opens) (hU : IsAffineOpen U) (P0 P1 : X.Opens)
  (h0U : P0 ≤ U) (h1U : P1 ≤ U) (haff0 : IsAffineOpen P0) (haff1 : IsAffineOpen P1) (hcov2 : U ≤ P0 ⊔ P1)
  (htriv : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧
    Nonempty ((Scheme.Modules.pullback W.ι).obj N ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))

abbrev fam : Fin 2 → X.Opens := ![P0, P1]

omit hU haff0 haff1 hcov2 htriv in
include h0U h1U in
theorem fam_le : ∀ i, fam P0 P1 i ≤ U := fun i => by
  fin_cases i
  · exact h0U
  · exact h1U
omit hU h0U h1U hcov2 htriv in
include haff0 haff1 in
theorem fam_aff : ∀ i, IsAffineOpen (fam P0 P1 i) := fun i => by
  fin_cases i
  · exact haff0
  · exact haff1
omit hU h0U h1U haff0 haff1 htriv in
include hcov2 in
theorem fam_cov : U ≤ ⨆ i, fam P0 P1 i := by
  refine hcov2.trans (sup_le ?_ ?_)
  · exact le_iSup (fam P0 P1) 0
  · exact le_iSup (fam P0 P1) 1

include hU h0U h1U haff0 haff1 hcov2 htriv in

theorem exists_sub_eq (s : Γ(N, P0 ⊓ P1)) :
    ∃ (x0 : Γ(N, P0)) (x1 : Γ(N, P1)),
      s = N.presheaf.map (homOfLE inf_le_right).op x1 - N.presheaf.map (homOfLE inf_le_left).op x0 := by
  classical
  haveI : IsAffine (U : Scheme.{u}) := hU
  let P : Fin 2 → X.Opens := fam P0 P1

  let u : ∀ i j : Fin 2, Γ(N, P2 P i j) := fun i j =>
    match i, j with
    | 0, 1 => s
    | 1, 0 => N.presheaf.map (homOfLE (le_of_eq (inf_comm P1 P0))).op s
    | 0, 0 => 0
    | 1, 1 => 0
  have hF := isQuasicoherent_F N U htriv

  have hempty : IsEmpty ((cover U P (fam_le U P0 P1 h0U h1U) (fam_aff P0 P1 haff0 haff1)
      (fam_cov U P0 P1 hcov2)).Idx 2) := by
    refine ⟨fun τ => ?_⟩
    have hinj : Function.Injective (fun k : Fin 3 => (τ.1 k).down) := fun a b hab =>
      τ.2.injective (ULift.ext _ _ hab)
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  have hd : (F N U).d (cover U P (fam_le U P0 P1 h0U h1U) (fam_aff P0 P1 haff0 haff1) (fam_cov U P0 P1 hcov2)) 1
      (u' N U P (fam_le U P0 P1 h0U h1U) (fam_aff P0 P1 haff0 haff1) (fam_cov U P0 P1 hcov2) u) = 0 := by
    funext τ; exact (hempty.false τ).elim
  obtain ⟨v', hv'⟩ := OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent (F N U) hF
    (cover U P (fam_le U P0 P1 h0U h1U) (fam_aff P0 P1 haff0 haff1) (fam_cov U P0 P1 hcov2)) 0
    (LinearMap.mem_ker.mpr hd)
  obtain ⟨v, huv⟩ := exists_v N U P (fam_le U P0 P1 h0U h1U) (fam_aff P0 P1 haff0 haff1) (fam_cov U P0 P1 hcov2)
    u v' hv'
  refine ⟨v 0, v 1, ?_⟩
  exact huv 0 1 (by decide)

end TwoPieces

section Glue2

variable (N : X.Modules)

theorem le_iSup_pair {V Q0 Q1 : X.Opens} (hcov : V ≤ Q0 ⊔ Q1) :
    V ≤ iSup (fun i : ULift.{u} (Fin 2) => (![Q0, Q1] : Fin 2 → X.Opens) i.down) := by
  refine hcov.trans (sup_le ?_ ?_)
  · exact le_iSup (fun i : ULift.{u} (Fin 2) => (![Q0, Q1] : Fin 2 → X.Opens) i.down) ⟨0⟩
  · exact le_iSup (fun i : ULift.{u} (Fin 2) => (![Q0, Q1] : Fin 2 → X.Opens) i.down) ⟨1⟩

theorem glue2 {V Q0 Q1 : X.Opens} (h0 : Q0 ≤ V) (h1 : Q1 ≤ V) (hcov : V ≤ Q0 ⊔ Q1)
    (a : Γ(N, Q0)) (b : Γ(N, Q1))
    (hab : N.presheaf.map (homOfLE (inf_le_left : Q0 ⊓ Q1 ≤ Q0)).op a
      = N.presheaf.map (homOfLE (inf_le_right : Q0 ⊓ Q1 ≤ Q1)).op b) :
    ∃ s : Γ(N, V), N.presheaf.map (homOfLE h0).op s = a ∧ N.presheaf.map (homOfLE h1).op s = b := by
  let Nsh : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let ι : Type u := ULift.{u} (Fin 2)
  let Q : ι → X.Opens := fun i => (![Q0, Q1] : Fin 2 → X.Opens) i.down
  have hQ : ∀ i, Q i ≤ V := fun i => by rcases i with ⟨i⟩; fin_cases i <;> assumption
  let sf : ∀ i : ι, Γ(N, Q i) := fun i => match i with
    | ⟨0⟩ => a
    | ⟨1⟩ => b
  have hcompat : TopCat.Presheaf.IsCompatible Nsh.1 Q sf := by
    rintro ⟨a'⟩ ⟨b'⟩
    fin_cases a' <;> fin_cases b'
    · rfl
    · exact hab
    · have := congrArg (N.presheaf.map (homOfLE (le_of_eq (inf_comm Q1 Q0))).op) hab
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] at this
      exact this.symm
    · rfl
  obtain ⟨s, hs, -⟩ := Nsh.existsUnique_gluing' Q V (fun i => homOfLE (hQ i)) (le_iSup_pair hcov) sf hcompat
  exact ⟨s, hs ⟨0⟩, hs ⟨1⟩⟩

theorem sep2 {V Q0 Q1 : X.Opens} (h0 : Q0 ≤ V) (h1 : Q1 ≤ V) (hcov : V ≤ Q0 ⊔ Q1)
    (s t : Γ(N, V)) (hs0 : N.presheaf.map (homOfLE h0).op s = N.presheaf.map (homOfLE h0).op t)
    (hs1 : N.presheaf.map (homOfLE h1).op s = N.presheaf.map (homOfLE h1).op t) : s = t := by
  let Nsh : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let ι : Type u := ULift.{u} (Fin 2)
  let Q : ι → X.Opens := fun i => (![Q0, Q1] : Fin 2 → X.Opens) i.down
  have hQ : ∀ i, Q i ≤ V := fun i => by rcases i with ⟨i⟩; fin_cases i <;> assumption
  apply Nsh.eq_of_locally_eq' Q V (fun i => homOfLE (hQ i)) (le_iSup_pair hcov)
  rintro ⟨i⟩
  fin_cases i
  · exact hs0
  · exact hs1

end Glue2

section Chase

variable {R : Type u} [CommRing R] (c : X ⟶ Spec (.of R)) [IsSeparated c] (M : X.Modules)
  (htriv : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
    Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))

def rs {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) : Γ(M, V) := M.presheaf.map (homOfLE h).op x

omit [IsSeparated c] in
theorem rs_def {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) : rs M h x = M.presheaf.map (homOfLE h).op x := rfl

omit [IsSeparated c] in
theorem rs_rs {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(M, U)) : rs M h' (rs M h x) = rs M (h'.trans h) x := by
  simp only [rs, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

omit [IsSeparated c] in
theorem rs_sub {U V : X.Opens} (h : V ≤ U) (x y : Γ(M, U)) : rs M h (x - y) = rs M h x - rs M h y := map_sub _ _ _
omit [IsSeparated c] in
theorem rs_add {U V : X.Opens} (h : V ≤ U) (x y : Γ(M, U)) : rs M h (x + y) = rs M h x + rs M h y := map_add _ _ _

include c htriv in

theorem chase (A B A' B' : X.Opens) (hAB : A ⊔ B = ⊤) (hA'B' : A' ⊔ B' = ⊤)
    (affA : IsAffineOpen A) (affB : IsAffineOpen B) (affA' : IsAffineOpen A') (affB' : IsAffineOpen B')
    (hsurj' : ∀ d : Γ(M, A' ⊓ B'), ∃ (e0 : Γ(M, A')) (e1 : Γ(M, B')),
      d = rs M inf_le_right e1 - rs M inf_le_left e0)
    (s : Γ(M, A ⊓ B)) :
    ∃ (s0 : Γ(M, A)) (s1 : Γ(M, B)), s = rs M inf_le_right s1 - rs M inf_le_left s0 := by
  have aff : ∀ {P Q : X.Opens}, IsAffineOpen P → IsAffineOpen Q → IsAffineOpen (P ⊓ Q) := fun {P Q} hP hQ => by
    haveI : IsAffineHom (pullback.diagonal c) := inferInstance
    exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) P (by simp) Q (by simp) hP hQ
  have cov2 : ∀ (W : X.Opens), W ≤ (A ⊓ W) ⊔ (B ⊓ W) := fun W x hx => by
    have : x ∈ (⊤ : X.Opens) := trivial
    rw [← hAB] at this
    rcases this with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hx⟩
  have cov2' : ∀ (W : X.Opens), W ≤ (W ⊓ A') ⊔ (W ⊓ B') := fun W x hx => by
    have : x ∈ (⊤ : X.Opens) := trivial
    rw [← hA'B'] at this
    rcases this with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

  let Q0 : X.Opens := (A ⊓ A') ⊓ (B ⊓ A')
  let Q1 : X.Opens := (A ⊓ B') ⊓ (B ⊓ B')
  let OA : X.Opens := (A ⊓ A') ⊓ (A ⊓ B')
  let OB : X.Opens := (B ⊓ A') ⊓ (B ⊓ B')
  have hQ0 : Q0 ≤ A ⊓ B := inf_le_inf inf_le_left inf_le_left
  have hQ1 : Q1 ≤ A ⊓ B := inf_le_inf inf_le_left inf_le_left
  have hOA : OA ≤ A' ⊓ B' := inf_le_inf inf_le_right inf_le_right
  have hOB : OB ≤ A' ⊓ B' := inf_le_inf inf_le_right inf_le_right
  have hcovQ : A ⊓ B ≤ Q0 ⊔ Q1 := fun x hx => by
    rcases cov2' (A ⊓ B) hx with h | h
    · exact Or.inl ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩
    · exact Or.inr ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩
  have hcovO : A' ⊓ B' ≤ OA ⊔ OB := fun x hx => by
    rcases cov2 (A' ⊓ B') hx with h | h
    · exact Or.inl ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩
    · exact Or.inr ⟨⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩

  let T : X.Opens := OA ⊓ OB
  have hTQ0 : T ≤ Q0 := inf_le_inf inf_le_left inf_le_left
  have hTQ1 : T ≤ Q1 := inf_le_inf inf_le_right inf_le_right

  obtain ⟨a0, a1, ha⟩ := exists_sub_eq M A' affA' (A ⊓ A') (B ⊓ A') inf_le_right inf_le_right
    (aff affA affA') (aff affB affA') (cov2 A') htriv (rs M hQ0 s)
  obtain ⟨b0, b1, hb⟩ := exists_sub_eq M B' affB' (A ⊓ B') (B ⊓ B') inf_le_right inf_le_right
    (aff affA affB') (aff affB affB') (cov2 B') htriv (rs M hQ1 s)
  change rs M hQ0 s = rs M (inf_le_right : Q0 ≤ B ⊓ A') a1 - rs M (inf_le_left : Q0 ≤ A ⊓ A') a0 at ha
  change rs M hQ1 s = rs M (inf_le_right : Q1 ≤ B ⊓ B') b1 - rs M (inf_le_left : Q1 ≤ A ⊓ B') b0 at hb

  have haT := congrArg (rs M hTQ0) ha
  have hbT := congrArg (rs M hTQ1) hb
  simp only [rs_sub, rs_rs] at haT hbT

  let δ0 : Γ(M, OA) := rs M inf_le_left a0 - rs M inf_le_right b0
  let δ1 : Γ(M, OB) := rs M inf_le_left a1 - rs M inf_le_right b1
  have hδ : rs M (inf_le_left : T ≤ OA) δ0 = rs M (inf_le_right : T ≤ OB) δ1 := by
    simp only [δ0, δ1, rs_sub, rs_rs]
    have eA0 : rs M ((inf_le_left : T ≤ OA).trans inf_le_left) a0
        = rs M ((inf_le_right : T ≤ OB).trans inf_le_left) a1 - rs M (hTQ0.trans hQ0) s := by
      rw [haT]; abel
    have eB0 : rs M ((inf_le_left : T ≤ OA).trans inf_le_right) b0
        = rs M ((inf_le_right : T ≤ OB).trans inf_le_right) b1 - rs M (hTQ1.trans hQ1) s := by
      rw [hbT]; abel
    rw [eA0, eB0]
    have : rs M (hTQ0.trans hQ0) s = rs M (hTQ1.trans hQ1) s := rfl
    rw [this]; abel
  obtain ⟨d, hd0, hd1⟩ := glue2 M hOA hOB hcovO δ0 δ1 hδ
  change rs M hOA d = δ0 at hd0
  change rs M hOB d = δ1 at hd1

  obtain ⟨e0, e1, he⟩ := hsurj' d

  let p0 : Γ(M, A ⊓ A') := a0 + rs M inf_le_right e0
  let q0 : Γ(M, A ⊓ B') := b0 + rs M inf_le_right e1
  have hpq0 : rs M (inf_le_left : OA ≤ A ⊓ A') p0 = rs M (inf_le_right : OA ≤ A ⊓ B') q0 := by
    simp only [p0, q0, rs_add, rs_rs]
    have hdd : rs M inf_le_left a0 - rs M inf_le_right b0 = rs M hOA d := hd0.symm
    rw [he, rs_sub, rs_rs, rs_rs] at hdd

    rw [sub_eq_sub_iff_add_eq_add] at hdd
    have e' : rs M ((inf_le_left : OA ≤ A ⊓ A').trans inf_le_right) e0 = rs M (hOA.trans inf_le_left) e0 := rfl
    have e'' : rs M ((inf_le_right : OA ≤ A ⊓ B').trans inf_le_right) e1 = rs M (hOA.trans inf_le_right) e1 := rfl
    rw [e', e'']

    rw [hdd]; abel
  obtain ⟨s0, hs0p, hs0q⟩ := glue2 M (inf_le_left : A ⊓ A' ≤ A) (inf_le_left : A ⊓ B' ≤ A) (cov2' A) p0 q0 hpq0
  change rs M (inf_le_left : A ⊓ A' ≤ A) s0 = p0 at hs0p
  change rs M (inf_le_left : A ⊓ B' ≤ A) s0 = q0 at hs0q

  let p1 : Γ(M, B ⊓ A') := a1 + rs M inf_le_right e0
  let q1 : Γ(M, B ⊓ B') := b1 + rs M inf_le_right e1
  have hpq1 : rs M (inf_le_left : OB ≤ B ⊓ A') p1 = rs M (inf_le_right : OB ≤ B ⊓ B') q1 := by
    simp only [p1, q1, rs_add, rs_rs]
    have hdd : rs M inf_le_left a1 - rs M inf_le_right b1 = rs M hOB d := hd1.symm
    rw [he, rs_sub, rs_rs, rs_rs] at hdd
    rw [sub_eq_sub_iff_add_eq_add] at hdd
    have e' : rs M ((inf_le_left : OB ≤ B ⊓ A').trans inf_le_right) e0 = rs M (hOB.trans inf_le_left) e0 := rfl
    have e'' : rs M ((inf_le_right : OB ≤ B ⊓ B').trans inf_le_right) e1 = rs M (hOB.trans inf_le_right) e1 := rfl
    rw [e', e'', hdd]; abel
  obtain ⟨s1, hs1p, hs1q⟩ := glue2 M (inf_le_left : B ⊓ A' ≤ B) (inf_le_left : B ⊓ B' ≤ B) (cov2' B) p1 q1 hpq1
  change rs M (inf_le_left : B ⊓ A' ≤ B) s1 = p1 at hs1p
  change rs M (inf_le_left : B ⊓ B' ≤ B) s1 = q1 at hs1q

  refine ⟨s0, s1, sep2 M hQ0 hQ1 hcovQ _ _ ?_ ?_⟩
  ·
    change rs M hQ0 s = rs M hQ0 (rs M inf_le_right s1 - rs M inf_le_left s0)
    rw [ha, rs_sub, rs_rs, rs_rs]
    have h1 : rs M (hQ0.trans inf_le_right) s1 = rs M (inf_le_right : Q0 ≤ B ⊓ A') p1 := by
      rw [← hs1p, rs_rs]
    have h0 : rs M (hQ0.trans inf_le_left) s0 = rs M (inf_le_left : Q0 ≤ A ⊓ A') p0 := by
      rw [← hs0p, rs_rs]
    rw [h1, h0]
    simp only [p0, p1, rs_add, rs_rs]
    have : rs M ((inf_le_right : Q0 ≤ B ⊓ A').trans inf_le_right) e0 = rs M ((inf_le_left : Q0 ≤ A ⊓ A').trans inf_le_right) e0 := rfl
    rw [this]; abel
  ·
    change rs M hQ1 s = rs M hQ1 (rs M inf_le_right s1 - rs M inf_le_left s0)
    rw [hb, rs_sub, rs_rs, rs_rs]
    have h1 : rs M (hQ1.trans inf_le_right) s1 = rs M (inf_le_right : Q1 ≤ B ⊓ B') q1 := by
      rw [← hs1q, rs_rs]
    have h0 : rs M (hQ1.trans inf_le_left) s0 = rs M (inf_le_left : Q1 ≤ A ⊓ B') q0 := by
      rw [← hs0q, rs_rs]
    rw [h1, h0]
    simp only [q0, q1, rs_add, rs_rs]
    have : rs M ((inf_le_right : Q1 ≤ B ⊓ B').trans inf_le_right) e1 = rs M ((inf_le_left : Q1 ≤ A ⊓ B').trans inf_le_right) e1 := rfl
    rw [this]; abel

include htriv in
theorem main (𝒱 𝒱' : X.TwoAffineOpenCover) (h : Subsingleton (𝒱'.sectionsOf c M).H1) :
    Subsingleton (𝒱.sectionsOf c M).H1 := by

  have hsurj' : ∀ d : Γ(M, 𝒱'.U0 ⊓ 𝒱'.U1), ∃ (e0 : Γ(M, 𝒱'.U0)) (e1 : Γ(M, 𝒱'.U1)),
      d = rs M inf_le_right e1 - rs M inf_le_left e0 := by
    intro d
    have hq : (Submodule.Quotient.mk d : (𝒱'.sectionsOf c M).H1) = 0 := Subsingleton.elim _ _
    obtain ⟨⟨e0, e1⟩, he⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    refine ⟨e0, e1, ?_⟩
    rw [← he, TwoChartCech.Sections.cechDiff_apply]
    rfl
  refine subsingleton_of_forall_eq 0 fun q => ?_
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  obtain ⟨s0, s1, hs⟩ := chase c M htriv 𝒱.U0 𝒱.U1 𝒱'.U0 𝒱'.U1 𝒱.sup_eq_top 𝒱'.sup_eq_top
    𝒱.isAffineOpen_U0 𝒱.isAffineOpen_U1 𝒱'.isAffineOpen_U0 𝒱'.isAffineOpen_U1 hsurj' s
  refine ⟨(s0, s1), ?_⟩
  rw [TwoChartCech.Sections.cechDiff_apply, hs]
  rfl

end Chase

end AlgebraicGeometry.Scheme.Modules.CoverIndep

end

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_subsingleton_H1.AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsSeparated c]
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (𝒱 𝒱' : X.TwoAffineOpenCover) (h : Subsingleton (𝒱'.sectionsOf c M).H1) :
    Subsingleton (𝒱.sectionsOf c M).H1 :=
  AlgebraicGeometry.Scheme.Modules.CoverIndep.main c M htriv 𝒱 𝒱' h

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_subsingleton_H1
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_subsingleton_H1 (solution)
