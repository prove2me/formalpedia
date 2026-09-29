-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e6e289dc-6189-5e30-99f5-d5cd0410d57c

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace
import Theorems.Thm_AutomorphicForm_continuous_archFlowAt_and_continuous_archFlowAtComplex
import Theorems.Thm_MeasureTheory_exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain
open NumberField.InfiniteAdeleRing NumberField.mixedEmbedding
open scoped Classical NNReal ENNReal

noncomputable section

namespace H2Basis

variable (K : Type) [Field K] [NumberField K]

abbrev Letter : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

abbrev Key : Type :=
  ({w : InfinitePlace K // w.IsReal} × ArchDir) ⊕ ({w : InfinitePlace K // w.IsComplex} × ArchDirComplex)

private abbrev _root_.H2Basis.E : Type := Fin 2 → Fin 2 → mixedSpace K

p2m_export "H2Basis" "E"
variable {K}

def key : Letter K → Key K
  | Sum.inl ⟨w, hw, d⟩ => Sum.inl (⟨w, hw⟩, d)
  | Sum.inr ⟨w, hw, d⟩ => Sum.inr (⟨w, hw⟩, d)

theorem key_injective : Function.Injective (key (K := K)) := by
  rintro (⟨w, hw, d⟩ | ⟨w, hw, d⟩) (⟨w', hw', d'⟩ | ⟨w', hw', d'⟩) h <;>
    simp only [key, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Subtype.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · obtain ⟨rfl, rfl⟩ := h; rfl

theorem key_surjective : Function.Surjective (key (K := K)) := by
  rintro (⟨⟨w, hw⟩, d⟩ | ⟨⟨w, hw⟩, d⟩)
  · exact ⟨Sum.inl ⟨w, hw, d⟩, rfl⟩
  · exact ⟨Sum.inr ⟨w, hw, d⟩, rfl⟩

def XC : ArchDirComplex → Matrix (Fin 2) (Fin 2) ℂ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]
  | .iH => !![Complex.I, 0; 0, -Complex.I]
  | .iE => !![0, Complex.I; 0, 0]
  | .iFm => !![0, 0; Complex.I, 0]

def XhatKey : Key K → E K
  | Sum.inl (w, d) => fun p q => (fun w' => if w' = w then archDirMatrix d p q else 0, 0)
  | Sum.inr (w, d) => fun p q => (0, fun w' => if w' = w then XC d p q else 0)

def Xhat (l : Letter K) : E K := XhatKey (key l)

theorem Xhat_inl (w : InfinitePlace K) (hw : w.IsReal) (d : ArchDir) :
    Xhat (Sum.inl ⟨w, hw, d⟩ : Letter K) =
      fun p q => (fun w' => if w' = ⟨w, hw⟩ then archDirMatrix d p q else 0, 0) := rfl

theorem Xhat_inr (w : InfinitePlace K) (hw : w.IsComplex) (d : ArchDirComplex) :
    Xhat (Sum.inr ⟨w, hw, d⟩ : Letter K) =
      fun p q => (0, fun w' => if w' = ⟨w, hw⟩ then XC d p q else 0) := rfl

variable (K) in

def central : mixedSpace K →ₗ[ℝ] E K :=
  LinearMap.pi fun p => LinearMap.pi fun q => if p = q then LinearMap.id else 0

theorem central_apply (x : mixedSpace K) (p q : Fin 2) :
    central K x p q = if p = q then x else 0 := by
  unfold central
  split_ifs <;> simp [*]

variable (K) in

def tangentMap (L₀ : List (Letter K)) : ((Fin L₀.length → ℝ) × mixedSpace K) →ₗ[ℝ] E K :=
  (∑ j : Fin L₀.length,
      ((LinearMap.proj j).comp (LinearMap.fst ℝ (Fin L₀.length → ℝ) (mixedSpace K))).smulRight
        (Xhat (L₀.get j))) +
    (central K).comp (LinearMap.snd ℝ (Fin L₀.length → ℝ) (mixedSpace K))

theorem tangentMap_apply (L₀ : List (Letter K)) (v : (Fin L₀.length → ℝ) × mixedSpace K) :
    tangentMap K L₀ v = (∑ j : Fin L₀.length, v.1 j • Xhat (L₀.get j)) + central K v.2 := by
  simp [tangentMap, LinearMap.sum_apply, LinearMap.smulRight_apply]

def evR (p q : Fin 2) (w : {w : InfinitePlace K // w.IsReal}) : E K →ₗ[ℝ] ℝ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace K // w.IsReal} => ℝ) w).comp
    ((LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ) ({w : InfinitePlace K // w.IsComplex} → ℂ)).comp
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedSpace K) q).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → mixedSpace K) p)))

def evC (p q : Fin 2) (w : {w : InfinitePlace K // w.IsComplex}) : E K →ₗ[ℝ] ℂ :=
  (LinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace K // w.IsComplex} => ℂ) w).comp
    ((LinearMap.snd ℝ ({w : InfinitePlace K // w.IsReal} → ℝ) ({w : InfinitePlace K // w.IsComplex} → ℂ)).comp
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedSpace K) q).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → mixedSpace K) p)))

@[scoped simp] theorem evR_apply (p q : Fin 2) (w : {w : InfinitePlace K // w.IsReal}) (e : E K) :
    evR p q w e = (e p q).1 w := rfl

@[scoped simp] theorem evC_apply (p q : Fin 2) (w : {w : InfinitePlace K // w.IsComplex}) (e : E K) :
    evC p q w e = (e p q).2 w := rfl

def coefKey : Key K → (E K →ₗ[ℝ] ℝ)
  | Sum.inl (w, .H) => (1 / 2 : ℝ) • (evR 0 0 w - evR 1 1 w)
  | Sum.inl (w, .E) => evR 0 1 w
  | Sum.inl (w, .Fm) => evR 1 0 w
  | Sum.inr (w, .H) => (1 / 2 : ℝ) • Complex.reLm.comp (evC 0 0 w - evC 1 1 w)
  | Sum.inr (w, .iH) => (1 / 2 : ℝ) • Complex.imLm.comp (evC 0 0 w - evC 1 1 w)
  | Sum.inr (w, .E) => Complex.reLm.comp (evC 0 1 w)
  | Sum.inr (w, .iE) => Complex.imLm.comp (evC 0 1 w)
  | Sum.inr (w, .Fm) => Complex.reLm.comp (evC 1 0 w)
  | Sum.inr (w, .iFm) => Complex.imLm.comp (evC 1 0 w)

def cenR (w : {w : InfinitePlace K // w.IsReal}) : E K →ₗ[ℝ] ℝ := (1 / 2 : ℝ) • (evR 0 0 w + evR 1 1 w)

def cenC (w : {w : InfinitePlace K // w.IsComplex}) : E K →ₗ[ℝ] ℂ := (1 / 2 : ℝ) • (evC 0 0 w + evC 1 1 w)

theorem coefKey_XhatKey (k k' : Key K) :
    coefKey k (XhatKey k') = if k' = k then 1 else 0 := by
  rcases k with ⟨w, d⟩ | ⟨w, d⟩ <;> rcases k' with ⟨w', d'⟩ | ⟨w', d'⟩
  · by_cases h : w = w'
    · subst h
      cases d <;> cases d' <;> simp [coefKey, XhatKey, archDirMatrix]
      all_goals norm_num
    · have h' : ¬ (w' = w) := fun h'' => h h''.symm
      cases d <;> cases d' <;> simp [coefKey, XhatKey, h, h']
  · cases d <;> simp [coefKey, XhatKey]
  · cases d <;> simp [coefKey, XhatKey]
  · by_cases h : w = w'
    · subst h
      cases d <;> cases d' <;> simp [coefKey, XhatKey, XC]
      all_goals norm_num
    · have h' : ¬ (w' = w) := fun h'' => h h''.symm
      cases d <;> cases d' <;> simp [coefKey, XhatKey, h, h']

theorem coefKey_central (k : Key K) (x : mixedSpace K) : coefKey k (central K x) = 0 := by
  rcases k with ⟨w, d⟩ | ⟨w, d⟩ <;> cases d <;> simp [coefKey, central_apply]

theorem cenR_XhatKey (w : {w : InfinitePlace K // w.IsReal}) (k : Key K) : cenR w (XhatKey k) = 0 := by
  rcases k with ⟨w', d⟩ | ⟨w', d⟩
  · cases d <;> simp [cenR, XhatKey, archDirMatrix] <;> split_ifs <;> norm_num
  · simp [cenR, XhatKey]

theorem cenC_XhatKey (w : {w : InfinitePlace K // w.IsComplex}) (k : Key K) : cenC w (XhatKey k) = 0 := by
  rcases k with ⟨w', d⟩ | ⟨w', d⟩
  · simp [cenC, XhatKey]
  · cases d <;> simp [cenC, XhatKey, XC] <;> split_ifs <;> norm_num

theorem cenR_central (w : {w : InfinitePlace K // w.IsReal}) (x : mixedSpace K) :
    cenR w (central K x) = x.1 w := by
  simp [cenR, central_apply]; ring

theorem cenC_central (w : {w : InfinitePlace K // w.IsComplex}) (x : mixedSpace K) :
    cenC w (central K x) = x.2 w := by
  simp [cenC, central_apply]; ring

theorem reconstructR (e : E K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsReal}) :
    (e p q).1 w =
      coefKey (Sum.inl (w, ArchDir.H)) e * archDirMatrix ArchDir.H p q +
      coefKey (Sum.inl (w, ArchDir.E)) e * archDirMatrix ArchDir.E p q +
      coefKey (Sum.inl (w, ArchDir.Fm)) e * archDirMatrix ArchDir.Fm p q +
      (if p = q then cenR w e else 0) := by
  fin_cases p <;> fin_cases q <;> simp [coefKey, cenR, archDirMatrix] <;> ring

theorem reconstructC (e : E K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsComplex}) :
    (e p q).2 w =
      (coefKey (Sum.inr (w, ArchDirComplex.H)) e : ℂ) * XC ArchDirComplex.H p q +
      (coefKey (Sum.inr (w, ArchDirComplex.E)) e : ℂ) * XC ArchDirComplex.E p q +
      (coefKey (Sum.inr (w, ArchDirComplex.Fm)) e : ℂ) * XC ArchDirComplex.Fm p q +
      (coefKey (Sum.inr (w, ArchDirComplex.iH)) e : ℂ) * XC ArchDirComplex.iH p q +
      (coefKey (Sum.inr (w, ArchDirComplex.iE)) e : ℂ) * XC ArchDirComplex.iE p q +
      (coefKey (Sum.inr (w, ArchDirComplex.iFm)) e : ℂ) * XC ArchDirComplex.iFm p q +
      (if p = q then cenC w e else 0) := by
  fin_cases p <;> fin_cases q <;> (apply Complex.ext <;> simp [coefKey, cenC, XC] <;> ring)

theorem tangentMap_apply_fst (L₀ : List (Letter K)) (v : (Fin L₀.length → ℝ) × mixedSpace K)
    (p q : Fin 2) (w : {w : InfinitePlace K // w.IsReal}) :
    (tangentMap K L₀ v p q).1 w =
      (∑ j : Fin L₀.length, v.1 j * (Xhat (L₀.get j) p q).1 w) + (if p = q then v.2.1 w else 0) := by
  rw [tangentMap_apply]
  simp only [Pi.add_apply, Prod.fst_add, Finset.sum_apply, Prod.fst_sum, Pi.smul_apply,
    Prod.smul_fst, smul_eq_mul, central_apply]
  split_ifs <;> simp

theorem tangentMap_apply_snd (L₀ : List (Letter K)) (v : (Fin L₀.length → ℝ) × mixedSpace K)
    (p q : Fin 2) (w : {w : InfinitePlace K // w.IsComplex}) :
    (tangentMap K L₀ v p q).2 w =
      (∑ j : Fin L₀.length, (v.1 j : ℂ) * (Xhat (L₀.get j) p q).2 w) + (if p = q then v.2.2 w else 0) := by
  rw [tangentMap_apply]
  simp only [Pi.add_apply, Prod.snd_add, Finset.sum_apply, Prod.snd_sum, Pi.smul_apply,
    Prod.smul_snd, Complex.real_smul, central_apply]
  split_ifs <;> simp

theorem termR (k : Key K) (e : E K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsReal}) :
    coefKey k e * (XhatKey k p q).1 w =
      (if k = Sum.inl (w, ArchDir.H) then coefKey (Sum.inl (w, ArchDir.H)) e * archDirMatrix ArchDir.H p q
        else 0) +
      (if k = Sum.inl (w, ArchDir.E) then coefKey (Sum.inl (w, ArchDir.E)) e * archDirMatrix ArchDir.E p q
        else 0) +
      (if k = Sum.inl (w, ArchDir.Fm) then coefKey (Sum.inl (w, ArchDir.Fm)) e * archDirMatrix ArchDir.Fm p q
        else 0) := by
  rcases k with ⟨w', d⟩ | ⟨w', d⟩
  · by_cases h : w = w'
    · subst h
      cases d <;> simp [XhatKey]
    · have h' : ¬ (w' = w) := fun h'' => h h''.symm
      cases d <;> simp [XhatKey, h, h']
  · simp [XhatKey]

theorem termC (k : Key K) (e : E K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsComplex}) :
    (coefKey k e : ℂ) * (XhatKey k p q).2 w =
      (if k = Sum.inr (w, ArchDirComplex.H) then
        (coefKey (Sum.inr (w, ArchDirComplex.H)) e : ℂ) * XC ArchDirComplex.H p q else 0) +
      (if k = Sum.inr (w, ArchDirComplex.E) then
        (coefKey (Sum.inr (w, ArchDirComplex.E)) e : ℂ) * XC ArchDirComplex.E p q else 0) +
      (if k = Sum.inr (w, ArchDirComplex.Fm) then
        (coefKey (Sum.inr (w, ArchDirComplex.Fm)) e : ℂ) * XC ArchDirComplex.Fm p q else 0) +
      (if k = Sum.inr (w, ArchDirComplex.iH) then
        (coefKey (Sum.inr (w, ArchDirComplex.iH)) e : ℂ) * XC ArchDirComplex.iH p q else 0) +
      (if k = Sum.inr (w, ArchDirComplex.iE) then
        (coefKey (Sum.inr (w, ArchDirComplex.iE)) e : ℂ) * XC ArchDirComplex.iE p q else 0) +
      (if k = Sum.inr (w, ArchDirComplex.iFm) then
        (coefKey (Sum.inr (w, ArchDirComplex.iFm)) e : ℂ) * XC ArchDirComplex.iFm p q else 0) := by
  rcases k with ⟨w', d⟩ | ⟨w', d⟩
  · simp [XhatKey]
  · by_cases h : w = w'
    · subst h
      cases d <;> simp [XhatKey]
    · have h' : ¬ (w' = w) := fun h'' => h h''.symm
      cases d <;> simp [XhatKey, h, h']

variable (K) in

def coordMap (L₀ : List (Letter K)) (e : E K) : (Fin L₀.length → ℝ) × mixedSpace K :=
  (fun j => coefKey (key (L₀.get j)) e, (fun w => cenR w e, fun w => cenC w e))

theorem sum_ite_key_eq {M : Type} [AddCommMonoid M] (L₀ : List (Letter K)) (hL₀ : L₀.Nodup)
    (hL₀' : ∀ d, d ∈ L₀) (k : Key K) (x : M) :
    (∑ j : Fin L₀.length, if key (L₀.get j) = k then x else 0) = x := by
  have kinj : Function.Injective (fun j : Fin L₀.length => key (L₀.get j)) :=
    key_injective.comp (List.nodup_iff_injective_get.mp hL₀)
  obtain ⟨l, rfl⟩ := key_surjective k
  obtain ⟨j₀, hj₀⟩ := List.mem_iff_get.mp (hL₀' l)
  rw [Finset.sum_eq_single j₀]
  · rw [if_pos (by rw [hj₀])]
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (kinj (show key (L₀.get j) = key (L₀.get j₀) by rw [h, hj₀]))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coordMap_tangentMap (L₀ : List (Letter K)) (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀)
    (v : (Fin L₀.length → ℝ) × mixedSpace K) : coordMap K L₀ (tangentMap K L₀ v) = v := by
  have kinj : Function.Injective (fun j : Fin L₀.length => key (L₀.get j)) :=
    key_injective.comp (List.nodup_iff_injective_get.mp hL₀)
  simp only [coordMap, tangentMap_apply, map_add, map_sum, map_smul, Xhat, coefKey_XhatKey,
    coefKey_central, cenR_XhatKey, cenC_XhatKey, cenR_central, cenC_central, smul_eq_mul, mul_zero,
    smul_zero, Finset.sum_const_zero, zero_add, add_zero]
  refine Prod.ext (funext fun j => ?_) (Prod.ext rfl rfl)
  have : ∀ j' : Fin L₀.length,
      (v.1 j' * if key (L₀.get j') = key (L₀.get j) then (1 : ℝ) else 0) =
        if j' = j then v.1 j' else 0 := by
    intro j'
    by_cases h : j' = j
    · subst h; simp
    · rw [if_neg (fun h' => h (kinj h')), if_neg h, mul_zero]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem tangentMap_coordMap (L₀ : List (Letter K)) (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀)
    (e : E K) : tangentMap K L₀ (coordMap K L₀ e) = e := by
  funext p q
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · rw [tangentMap_apply_fst]
    simp only [coordMap, Xhat]
    simp_rw [termR]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_key_eq L₀ hL₀ hL₀',
      sum_ite_key_eq L₀ hL₀ hL₀', sum_ite_key_eq L₀ hL₀ hL₀']
    exact (reconstructR e p q w).symm
  · rw [tangentMap_apply_snd]
    simp only [coordMap, Xhat]
    simp_rw [termC]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_ite_key_eq L₀ hL₀ hL₀', sum_ite_key_eq L₀ hL₀ hL₀',
      sum_ite_key_eq L₀ hL₀ hL₀', sum_ite_key_eq L₀ hL₀ hL₀', sum_ite_key_eq L₀ hL₀ hL₀',
      sum_ite_key_eq L₀ hL₀ hL₀']
    exact (reconstructC e p q w).symm

theorem tangentMap_bijective (L₀ : List (Letter K)) (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) :
    Function.Bijective (tangentMap K L₀) :=
  ⟨(Function.LeftInverse.injective (g := coordMap K L₀) fun v => coordMap_tangentMap L₀ hL₀ hL₀' v),
    Function.RightInverse.surjective (g := coordMap K L₀) fun e => tangentMap_coordMap L₀ hL₀ hL₀' e⟩

variable (K) in

def tangentEquiv (L₀ : List (Letter K)) (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) :
    ((Fin L₀.length → ℝ) × mixedSpace K) ≃L[ℝ] E K :=
  (LinearEquiv.ofBijective (tangentMap K L₀) (tangentMap_bijective L₀ hL₀ hL₀')).toContinuousLinearEquiv

@[scoped simp] theorem tangentEquiv_apply (L₀ : List (Letter K)) (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀)
    (v : (Fin L₀.length → ℝ) × mixedSpace K) :
    tangentEquiv K L₀ hL₀ hL₀' v = tangentMap K L₀ v := rfl

theorem coe_tangentEquiv (L₀ : List (Letter K)) (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) :
    (tangentEquiv K L₀ hL₀ hL₀' : ((Fin L₀.length → ℝ) × mixedSpace K) →L[ℝ] E K) =
      LinearMap.toContinuousLinearMap (tangentMap K L₀) :=
  ContinuousLinearMap.ext fun _ => rfl

theorem tangentEquiv_symm_apply (L₀ : List (Letter K)) (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) (e : E K) :
    (tangentEquiv K L₀ hL₀ hL₀').symm e = coordMap K L₀ e := by
  apply (tangentEquiv K L₀ hL₀ hL₀').injective
  rw [ContinuousLinearEquiv.apply_symm_apply, tangentEquiv_apply, tangentMap_coordMap L₀ hL₀ hL₀']

theorem tangentMap_single (L₀ : List (Letter K)) (j : Fin L₀.length) :
    tangentMap K L₀ (Pi.single j 1, 0) = Xhat (L₀.get j) := by
  rw [tangentMap_apply, map_zero, add_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'; simp [Pi.single_apply, hj']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tangentMap_inr (L₀ : List (Letter K)) (x : mixedSpace K) :
    tangentMap K L₀ (0, x) = central K x := by
  rw [tangentMap_apply]
  simp

theorem eq_tangentMap_of (L₀ : List (Letter K))
    (T : ((Fin L₀.length → ℝ) × mixedSpace K) →ₗ[ℝ] E K)
    (h1 : ∀ j, T (Pi.single j 1, 0) = Xhat (L₀.get j)) (h2 : ∀ x, T (0, x) = central K x) :
    T = tangentMap K L₀ := by
  refine LinearMap.prod_ext (LinearMap.pi_ext_iff.2 fun j x => ?_) (LinearMap.ext fun x => ?_)
  · have hs : (Pi.single j x : Fin L₀.length → ℝ) = x • (Pi.single j (1 : ℝ)) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    have hp : ((x • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)), (0 : mixedSpace K)) =
        x • ((Pi.single j (1 : ℝ) : Fin L₀.length → ℝ), (0 : mixedSpace K)) := by
      rw [Prod.smul_mk, smul_zero]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply, hs, hp, map_smul, h1,
      tangentMap_single]
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply, h2, tangentMap_inr]

end H2Basis
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.H2Basis"

section
open Topology Set Filter

namespace H2Cov

theorem setLIntegral_comp_eq_of_map_eq_smul {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β) (c : ℝ≥0∞) (hc : μ.map e = c • ν)
    (t : Set α) (h : β → ℝ≥0∞) :
    ∫⁻ x in t, h (e x) ∂μ = c * ∫⁻ y in e '' t, h y ∂ν := by
  have h1 : ∫⁻ y in e '' t, h y ∂(μ.map e) = ∫⁻ x in t, h (e x) ∂μ := by
    rw [e.restrict_map, e.preimage_image, lintegral_map_equiv]
  rw [← h1, hc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

theorem exists_isOpen_injOn_mul_lintegral_comp_le {V E : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μV : Measure V) [μV.IsAddHaarMeasure] (μE : Measure E) [μE.IsAddHaarMeasure]
    (F : V → E) (T : V ≃L[ℝ] E) (hF : ContDiffAt ℝ 1 F 0) (hF' : HasFDerivAt F (T : V →L[ℝ] E) 0) :
    ∃ s : Set V, IsOpen s ∧ (0 : V) ∈ s ∧ Set.InjOn F s ∧ ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ t ⊆ s, MeasurableSet t → ∀ g : E → ℝ≥0∞,
        (δ : ℝ≥0∞) * ∫⁻ x in t, g (F x) ∂μV ≤ ∫⁻ y in F '' t, g y ∂μE := by

  set f : E → E := F ∘ T.symm with hf_def
  have hfT : ∀ x : V, f (T x) = F x := fun x => by simp [hf_def]
  have hf : ContDiffAt ℝ 1 f (T 0) := by
    have h : ContDiffAt ℝ 1 F (T.symm (T 0)) := by rwa [T.symm_apply_apply]
    exact h.comp _ T.symm.contDiff.contDiffAt
  have hfd : HasFDerivAt f ((T : V →L[ℝ] E).comp (T.symm : E →L[ℝ] V)) (T 0) := by
    have h : HasFDerivAt F (T : V →L[ℝ] E) (T.symm (T 0)) := by rwa [T.symm_apply_apply]
    exact h.comp _ T.symm.hasFDerivAt
  have hdet : (fderiv ℝ f (T 0)).det ≠ 0 := by
    rw [hfd.fderiv, ContinuousLinearEquiv.coe_comp_coe_symm, ContinuousLinearMap.det,
      ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact one_ne_zero
  obtain ⟨s, hs, hmem, hinj, δ, hδ, hle⟩ :=
    MeasureTheory.exists_isOpen_injOn_forall_mul_lintegral_comp_le_lintegral_image_of_det_fderiv_ne_zero
      μE f (T 0) hf hdet

  let eT : V ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have heT : (eT : V → E) = T := rfl
  haveI : (μV.map eT).IsAddHaarMeasure := by rw [heT]; exact T.isAddHaarMeasure_map μV
  set c : ℝ≥0 := (μV.map eT).addHaarScalarFactor μE with hc_def
  have hc : μV.map eT = c • μE := Measure.isAddLeftInvariant_eq_smul _ _
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hc' : μV.map eT = (c : ℝ≥0∞) • μE := by rw [hc, ENNReal.smul_def]
  have key : ∀ (t : Set V) (h : E → ℝ≥0∞),
      ∫⁻ x in t, h (T x) ∂μV = (c : ℝ≥0∞) * ∫⁻ y in T '' t, h y ∂μE := by
    intro t h
    rw [← heT]
    exact setLIntegral_comp_eq_of_map_eq_smul eT μV μE c hc' t h
  refine ⟨T ⁻¹' s, hs.preimage T.continuous, hmem, ?_, δ / c, div_pos hδ hcpos, ?_⟩
  · intro x hx y hy hxy
    exact T.injective (hinj hx hy (by rw [hfT, hfT]; exact hxy))
  · intro t ht htm g
    have hTt : T '' t ⊆ s := image_subset_iff.2 ht
    have hTt_meas : MeasurableSet (T '' t) := by
      rw [← heT]; exact eT.measurableSet_image.2 htm
    have hmain := hle (T '' t) hTt hTt_meas g
    have himage : f '' (T '' t) = F '' t := by
      rw [image_image]; exact congrArg (· '' t) (funext hfT)
    rw [himage] at hmain
    have hcomp : ∫⁻ x in t, g (F x) ∂μV = (c : ℝ≥0∞) * ∫⁻ y in T '' t, g (f y) ∂μE := by
      rw [← key t (fun y => g (f y))]
      simp only [hfT]
    calc ((δ / c : ℝ≥0) : ℝ≥0∞) * ∫⁻ x in t, g (F x) ∂μV
        = (δ : ℝ≥0∞) * ∫⁻ y in T '' t, g (f y) ∂μE := by
          rw [hcomp, ENNReal.coe_div hcpos.ne', ← mul_assoc,
            ENNReal.div_mul_cancel (ENNReal.coe_ne_zero.2 hcpos.ne') ENNReal.coe_ne_top]
      _ ≤ ∫⁻ y in F '' t, g y ∂μE := hmain

section Instances

variable (n : Type) [Fintype n] (K : Type) [Field K] [NumberField K]

theorem borelSpace_pi_mixedSpace : BorelSpace (n → mixedSpace K) := Pi.borelSpace

theorem borelSpace_E : BorelSpace (n → n → mixedSpace K) := by
  haveI : BorelSpace (n → mixedSpace K) := borelSpace_pi_mixedSpace n K
  exact Pi.borelSpace

theorem sigmaFinite_volume_pi_mixedSpace : SigmaFinite (volume : Measure (n → mixedSpace K)) :=
  Measure.pi.sigmaFinite (ι := n) (α := fun _ => mixedSpace K) (fun _ => volume)

theorem measurableAdd_mixedSpace : MeasurableAdd (mixedSpace K) := inferInstance

theorem isAddHaarMeasure_volume_pi_mixedSpace :
    (volume : Measure (n → mixedSpace K)).IsAddHaarMeasure := by
  haveI : BorelSpace (n → mixedSpace K) := borelSpace_pi_mixedSpace n K
  exact @Measure.pi.isAddHaarMeasure n (fun _ => mixedSpace K) _ _ (fun _ => volume) _ _ _ _
    (fun _ => measurableAdd_mixedSpace K)

theorem sigmaFinite_volume_E : SigmaFinite (volume : Measure (n → n → mixedSpace K)) := by
  haveI := sigmaFinite_volume_pi_mixedSpace n K
  exact Measure.pi.sigmaFinite (ι := n) (α := fun _ => n → mixedSpace K) (fun _ => volume)

theorem isAddHaarMeasure_volume_E : (volume : Measure (n → n → mixedSpace K)).IsAddHaarMeasure := by
  haveI : BorelSpace (n → mixedSpace K) := borelSpace_pi_mixedSpace n K
  haveI : BorelSpace (n → n → mixedSpace K) := borelSpace_E n K
  haveI := sigmaFinite_volume_pi_mixedSpace n K
  haveI := isAddHaarMeasure_volume_pi_mixedSpace n K
  have hMA : MeasurableAdd (n → mixedSpace K) := inferInstance
  exact @Measure.pi.isAddHaarMeasure n (fun _ => n → mixedSpace K) _ _ (fun _ => volume)
    (fun _ => sigmaFinite_volume_pi_mixedSpace n K) _ _
    (fun _ => isAddHaarMeasure_volume_pi_mixedSpace n K) (fun _ => hMA)

theorem borelSpace_V (m : Type) [Fintype m] : BorelSpace ((m → ℝ) × mixedSpace K) := inferInstance

theorem sigmaFinite_volume_V (m : Type) [Fintype m] :
    SigmaFinite (volume : Measure ((m → ℝ) × mixedSpace K)) := inferInstance

theorem isAddHaarMeasure_volume_V (m : Type) [Fintype m] :
    (volume : Measure ((m → ℝ) × mixedSpace K)).IsAddHaarMeasure := by
  have h1 : MeasurableAdd (m → ℝ) := inferInstance
  exact @Measure.prod.instIsAddHaarMeasure (m → ℝ) _ _ _ (mixedSpace K) _ _ _
    (volume : Measure (m → ℝ)) (volume : Measure (mixedSpace K)) _ _ _ _ h1 (measurableAdd_mixedSpace K)

end Instances
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.H2Basis"

end H2Cov
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.H2Basis"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.H2Basis"

namespace H2Proof

variable (K : Type) [Field K] [NumberField K]

def evR (w : {w : InfinitePlace K // w.IsReal}) : InfiniteAdeleRing K →+* ℝ :=
  (Pi.evalRingHom (fun _ : {w : InfinitePlace K // w.IsReal} => ℝ) w).comp
    ((RingHom.fst _ _).comp (ringEquiv_mixedSpace K).toRingHom)

def evC (w : {w : InfinitePlace K // w.IsComplex}) : InfiniteAdeleRing K →+* ℂ :=
  (Pi.evalRingHom (fun _ : {w : InfinitePlace K // w.IsComplex} => ℂ) w).comp
    ((RingHom.snd _ _).comp (ringEquiv_mixedSpace K).toRingHom)

def projR (w : {w : InfinitePlace K // w.IsReal}) : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (evR K w)

def projC (w : {w : InfinitePlace K // w.IsComplex}) : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.map (evC K w)

omit [NumberField K] in
theorem projR_apply (w : {w : InfinitePlace K // w.IsReal}) (g : GL (Fin 2) (InfiniteAdeleRing K)) (p q : Fin 2) :
    (projR K w g : Matrix (Fin 2) (Fin 2) ℝ) p q =
      (ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) p q)).1 w := rfl

omit [NumberField K] in
theorem projC_apply (w : {w : InfinitePlace K // w.IsComplex}) (g : GL (Fin 2) (InfiniteAdeleRing K)) (p q : Fin 2) :
    (projC K w g : Matrix (Fin 2) (Fin 2) ℂ) p q =
      (ringEquiv_mixedSpace K ((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) p q)).2 w := rfl

omit [NumberField K] in
theorem extensionEmbeddingOfIsReal_symm {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) :
    Completion.extensionEmbeddingOfIsReal hw ((Completion.ringEquivRealOfIsReal hw).symm r) = r :=
  (Completion.ringEquivRealOfIsReal hw).apply_symm_apply r

omit [NumberField K] in
theorem extensionEmbedding_symm {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) :
    Completion.extensionEmbedding w ((Completion.ringEquivComplexOfIsComplex hw).symm z) = z :=
  (Completion.ringEquivComplexOfIsComplex hw).apply_symm_apply z

def piR (w : {w : InfinitePlace K // w.IsReal}) : AdelicGL2 (𝓞 K) K →* GL (Fin 2) ℝ :=
  (projR K w).comp (glArch (𝓞 K) K)

def piC (w : {w : InfinitePlace K // w.IsComplex}) : AdelicGL2 (𝓞 K) K →* GL (Fin 2) ℂ :=
  (projC K w).comp (glArch (𝓞 K) K)

theorem piR_apply (w : {w : InfinitePlace K // w.IsReal}) (g : AdelicGL2 (𝓞 K) K) :
    piR K w g = projR K w (glArch (𝓞 K) K g) := rfl

theorem piC_apply (w : {w : InfinitePlace K // w.IsComplex}) (g : AdelicGL2 (𝓞 K) K) :
    piC K w g = projC K w (glArch (𝓞 K) K g) := rfl

theorem piR_archRealGLAt (w' : {w : InfinitePlace K // w.IsReal}) {w : InfinitePlace K} (hw : w.IsReal)
    (m : GL (Fin 2) ℝ) :
    piR K w' (archRealGLAt hw m) = if w' = ⟨w, hw⟩ then m else 1 := by
  have h1 : glArch (𝓞 K) K (archRealGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (Completion.ringEquivRealOfIsReal hw).symm m) :=
    glArch_adelicArchGLIncl K _
  ext p q
  rw [piR_apply, projR_apply, h1]
  show Completion.extensionEmbeddingOfIsReal w'.2
      (archMatrixUpdate K w ((glEquivOfRingEquiv (Completion.ringEquivRealOfIsReal hw).symm m :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) p q w'.1) = _
  split_ifs with h
  · subst h
    rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]
    exact extensionEmbeddingOfIsReal_symm K hw _
  · have hne : (w'.1 : InfinitePlace K) ≠ w := fun h' => h (Subtype.ext h')
    rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hne, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem piC_archRealGLAt (w' : {w : InfinitePlace K // w.IsComplex}) {w : InfinitePlace K} (hw : w.IsReal)
    (m : GL (Fin 2) ℝ) :
    piC K w' (archRealGLAt hw m) = 1 := by
  have h1 : glArch (𝓞 K) K (archRealGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (Completion.ringEquivRealOfIsReal hw).symm m) :=
    glArch_adelicArchGLIncl K _
  have hne : (w'.1 : InfinitePlace K) ≠ w := fun h' =>
    (InfinitePlace.not_isReal_iff_isComplex.mpr w'.2) (h' ▸ hw)
  ext p q
  rw [piC_apply, projC_apply, h1]
  show Completion.extensionEmbedding w'.1
      (archMatrixUpdate K w ((glEquivOfRingEquiv (Completion.ringEquivRealOfIsReal hw).symm m :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) p q w'.1) = _
  rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hne, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem piC_archComplexGLAt (w' : {w : InfinitePlace K // w.IsComplex}) {w : InfinitePlace K}
    (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    piC K w' (archComplexGLAt hw m) = if w' = ⟨w, hw⟩ then m else 1 := by
  have h1 : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (Completion.ringEquivComplexOfIsComplex hw).symm m) :=
    glArch_adelicArchGLIncl K _
  ext p q
  rw [piC_apply, projC_apply, h1]
  show Completion.extensionEmbedding w'.1
      (archMatrixUpdate K w ((glEquivOfRingEquiv (Completion.ringEquivComplexOfIsComplex hw).symm m :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) p q w'.1) = _
  split_ifs with h
  · subst h
    rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]
    exact extensionEmbedding_symm K hw _
  · have hne : (w'.1 : InfinitePlace K) ≠ w := fun h' => h (Subtype.ext h')
    rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hne, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem piR_archComplexGLAt (w' : {w : InfinitePlace K // w.IsReal}) {w : InfinitePlace K}
    (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    piR K w' (archComplexGLAt hw m) = 1 := by
  have h1 : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (Completion.ringEquivComplexOfIsComplex hw).symm m) :=
    glArch_adelicArchGLIncl K _
  have hne : (w'.1 : InfinitePlace K) ≠ w := fun h' =>
    (InfinitePlace.not_isReal_iff_isComplex.mpr hw) (h' ▸ w'.2)
  ext p q
  rw [piR_apply, projR_apply, h1]
  show Completion.extensionEmbeddingOfIsReal w'.2
      (archMatrixUpdate K w ((glEquivOfRingEquiv (Completion.ringEquivComplexOfIsComplex hw).symm m :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) p q w'.1) = _
  rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hne, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

abbrev Letter : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

def flow : Letter K → ℝ → AdelicGL2 (𝓞 K) K :=
  fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d

theorem flow_zero (d : Letter K) : flow K d 0 = 1 := by
  rcases d with ⟨w, hw, dir⟩ | ⟨w, hw, dir⟩
  · exact archFlowAt_zero hw dir
  · exact archFlowAtComplex_zero hw dir

def scalR (a : ℝ) : GL (Fin 2) ℝ :=
  Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom (Units.mk0 (Real.exp a) (Real.exp_ne_zero a))

def scalC (b : ℂ) : GL (Fin 2) ℂ :=
  Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom (Units.mk0 (Complex.exp b) (Complex.exp_ne_zero b))

theorem scalR_apply (a : ℝ) (p q : Fin 2) : (scalR a : Matrix (Fin 2) (Fin 2) ℝ) p q = if p = q then Real.exp a else 0 := by
  show (Matrix.scalar (Fin 2) (Real.exp a)) p q = _
  by_cases h : p = q
  · subst h; simp
  · simp [h]

theorem scalC_apply (b : ℂ) (p q : Fin 2) : (scalC b : Matrix (Fin 2) (Fin 2) ℂ) p q = if p = q then Complex.exp b else 0 := by
  show (Matrix.scalar (Fin 2) (Complex.exp b)) p q = _
  by_cases h : p = q
  · subst h; simp
  · simp [h]

theorem scalR_zero : scalR 0 = 1 := by
  ext p q; rw [scalR_apply, Real.exp_zero, Units.val_one, Matrix.one_apply]

theorem scalC_zero : scalC 0 = 1 := by
  ext p q; rw [scalC_apply, Complex.exp_zero, Units.val_one, Matrix.one_apply]

def sR (w : {w : InfinitePlace K // w.IsReal}) (a : ℝ) : AdelicGL2 (𝓞 K) K := archRealGLAt w.2 (scalR a)

def sC (w : {w : InfinitePlace K // w.IsComplex}) (b : ℂ) : AdelicGL2 (𝓞 K) K := archComplexGLAt w.2 (scalC b)

theorem piR_flow (w : {w : InfinitePlace K // w.IsReal}) (d : Letter K) (t : ℝ) :
    piR K w (flow K d t) =
      Sum.elim (fun d => if w = ⟨d.1, d.2.1⟩ then archFlowMatrix d.2.2 t else 1) (fun _ => 1) d := by
  rcases d with ⟨w₀, hw₀, dir⟩ | ⟨w₀, hw₀, dir⟩
  · exact piR_archRealGLAt K w hw₀ _
  · exact piR_archComplexGLAt K w hw₀ _

theorem piC_flow (w : {w : InfinitePlace K // w.IsComplex}) (d : Letter K) (t : ℝ) :
    piC K w (flow K d t) =
      Sum.elim (fun _ => 1) (fun d => if w = ⟨d.1, d.2.1⟩ then archFlowMatrixComplex d.2.2 t else 1) d := by
  rcases d with ⟨w₀, hw₀, dir⟩ | ⟨w₀, hw₀, dir⟩
  · exact piC_archRealGLAt K w hw₀ _
  · exact piC_archComplexGLAt K w hw₀ _

theorem piR_sR (w w₀ : {w : InfinitePlace K // w.IsReal}) (a : ℝ) :
    piR K w (sR K w₀ a) = if w = w₀ then scalR a else 1 :=
  piR_archRealGLAt K w w₀.2 _

theorem piC_sR (w : {w : InfinitePlace K // w.IsComplex}) (w₀ : {w : InfinitePlace K // w.IsReal}) (a : ℝ) :
    piC K w (sR K w₀ a) = 1 :=
  piC_archRealGLAt K w w₀.2 _

theorem piC_sC (w w₀ : {w : InfinitePlace K // w.IsComplex}) (b : ℂ) :
    piC K w (sC K w₀ b) = if w = w₀ then scalC b else 1 :=
  piC_archComplexGLAt K w w₀.2 _

theorem piR_sC (w : {w : InfinitePlace K // w.IsReal}) (w₀ : {w : InfinitePlace K // w.IsComplex}) (b : ℂ) :
    piR K w (sC K w₀ b) = 1 :=
  piR_archComplexGLAt K w w₀.2 _

theorem prod_map_toList_univ_eq_single {ι M : Type} [Fintype ι] [DecidableEq ι] [Monoid M] (f : ι → M) (i : ι)
    (h : ∀ j, j ≠ i → f j = 1) : ((Finset.univ : Finset ι).toList.map f).prod = f i := by
  rw [List.prod_map_eq_pow_single i f (fun j hj _ => h j hj),
    List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.mpr (Finset.mem_univ i)), pow_one]

theorem prod_map_toList_univ_eq_one {ι M : Type} [Fintype ι] [Monoid M] (f : ι → M)
    (h : ∀ j, f j = 1) : ((Finset.univ : Finset ι).toList.map f).prod = 1 :=
  List.prod_eq_one fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact h j

theorem prod_ofFn_eq_single {M : Type} [Monoid M] {n : ℕ} (f : Fin n → M) (j : Fin n)
    (h : ∀ i, i ≠ j → f i = 1) : (List.ofFn f).prod = f j := by
  rw [List.ofFn_eq_map, List.prod_map_eq_pow_single j f (fun i hi _ => h i hi),
    List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange j), pow_one]

theorem prod_ofFn_eq_one {M : Type} [Monoid M] {n : ℕ} (f : Fin n → M) (h : ∀ i, f i = 1) :
    (List.ofFn f).prod = 1 :=
  List.prod_eq_one fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact h i

variable (L₀ : List (Letter K))

def chart (t : Fin L₀.length → ℝ) : AdelicGL2 (𝓞 K) K := (List.ofFn fun j => flow K (L₀.get j) (t j)).prod

def scal (a : {w : InfinitePlace K // w.IsReal} → ℝ) (b : {w : InfinitePlace K // w.IsComplex} → ℂ) :
    AdelicGL2 (𝓞 K) K :=
  ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w => sR K w (a w)).prod *
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w => sC K w (b w)).prod

def ψ (v : (Fin L₀.length → ℝ) × mixedSpace K) : AdelicGL2 (𝓞 K) K := chart K L₀ v.1 * scal K v.2.1 v.2.2

def F (v : (Fin L₀.length → ℝ) × mixedSpace K) : Fin 2 → Fin 2 → mixedSpace K :=
  fun p q => ringEquiv_mixedSpace K ((glArch (𝓞 K) K (ψ K L₀ v) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) p q)

theorem F_fst (v : (Fin L₀.length → ℝ) × mixedSpace K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsReal}) :
    (F K L₀ v p q).1 w = (piR K w (ψ K L₀ v) : Matrix (Fin 2) (Fin 2) ℝ) p q := rfl

theorem F_snd (v : (Fin L₀.length → ℝ) × mixedSpace K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsComplex}) :
    (F K L₀ v p q).2 w = (piC K w (ψ K L₀ v) : Matrix (Fin 2) (Fin 2) ℂ) p q := rfl

theorem F_eq : F K L₀ = fun v p q =>
    ((fun w => (piR K w (ψ K L₀ v) : Matrix (Fin 2) (Fin 2) ℝ) p q,
      fun w => (piC K w (ψ K L₀ v) : Matrix (Fin 2) (Fin 2) ℂ) p q) : mixedSpace K) := by
  funext v p q
  exact Prod.ext (funext fun w => rfl) (funext fun w => rfl)

theorem piR_scal (w : {w : InfinitePlace K // w.IsReal}) (a : {w : InfinitePlace K // w.IsReal} → ℝ)
    (b : {w : InfinitePlace K // w.IsComplex} → ℂ) : piR K w (scal K a b) = scalR (a w) := by
  have h1 : ∀ j, j ≠ w → (⇑(piR K w) ∘ fun j => sR K j (a j)) j = 1 := fun j hj => by
    show piR K w (sR K j (a j)) = 1
    rw [piR_sR, if_neg hj.symm]
  have h2 : ∀ j, (⇑(piR K w) ∘ fun j => sC K j (b j)) j = 1 := fun j => piR_sC K w j (b j)
  rw [scal, map_mul, map_list_prod, map_list_prod, List.map_map, List.map_map,
    prod_map_toList_univ_eq_single _ w h1, prod_map_toList_univ_eq_one _ h2, mul_one]
  show piR K w (sR K w (a w)) = scalR (a w)
  rw [piR_sR, if_pos rfl]

theorem piC_scal (w : {w : InfinitePlace K // w.IsComplex}) (a : {w : InfinitePlace K // w.IsReal} → ℝ)
    (b : {w : InfinitePlace K // w.IsComplex} → ℂ) : piC K w (scal K a b) = scalC (b w) := by
  have h1 : ∀ j, (⇑(piC K w) ∘ fun j => sR K j (a j)) j = 1 := fun j => piC_sR K w j (a j)
  have h2 : ∀ j, j ≠ w → (⇑(piC K w) ∘ fun j => sC K j (b j)) j = 1 := fun j hj => by
    show piC K w (sC K j (b j)) = 1
    rw [piC_sC, if_neg hj.symm]
  rw [scal, map_mul, map_list_prod, map_list_prod, List.map_map, List.map_map,
    prod_map_toList_univ_eq_one _ h1, prod_map_toList_univ_eq_single _ w h2, one_mul]
  show piC K w (sC K w (b w)) = scalC (b w)
  rw [piC_sC, if_pos rfl]

theorem piR_chart (w : {w : InfinitePlace K // w.IsReal}) (t : Fin L₀.length → ℝ) :
    piR K w (chart K L₀ t) = (List.ofFn fun j => piR K w (flow K (L₀.get j) (t j))).prod := by
  rw [chart, map_list_prod, List.map_ofFn]; rfl

theorem piC_chart (w : {w : InfinitePlace K // w.IsComplex}) (t : Fin L₀.length → ℝ) :
    piC K w (chart K L₀ t) = (List.ofFn fun j => piC K w (flow K (L₀.get j) (t j))).prod := by
  rw [chart, map_list_prod, List.map_ofFn]; rfl

theorem piR_ψ (w : {w : InfinitePlace K // w.IsReal}) (v : (Fin L₀.length → ℝ) × mixedSpace K) :
    piR K w (ψ K L₀ v) = (List.ofFn fun j => piR K w (flow K (L₀.get j) (v.1 j))).prod * scalR (v.2.1 w) := by
  rw [ψ, map_mul, piR_chart, piR_scal]

theorem piC_ψ (w : {w : InfinitePlace K // w.IsComplex}) (v : (Fin L₀.length → ℝ) × mixedSpace K) :
    piC K w (ψ K L₀ v) = (List.ofFn fun j => piC K w (flow K (L₀.get j) (v.1 j))).prod * scalC (v.2.2 w) := by
  rw [ψ, map_mul, piC_chart, piC_scal]

section Smooth

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def SmoothM {𝔽 : Type} [RCLike 𝔽] (M : X → GL (Fin 2) 𝔽) : Prop :=
  ∀ p q, ContDiff ℝ (⊤ : ℕ∞) fun x => ((M x : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p q

theorem smoothM_one {𝔽 : Type} [RCLike 𝔽] : SmoothM (fun _ : X => (1 : GL (Fin 2) 𝔽)) :=
  fun _ _ => contDiff_const

theorem smoothM_mul {𝔽 : Type} [RCLike 𝔽] {M N : X → GL (Fin 2) 𝔽} (hM : SmoothM M) (hN : SmoothM N) :
    SmoothM fun x => M x * N x := by
  intro p q
  have : (fun x => ((M x * N x : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p q) =
      fun x => ∑ k, ((M x : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) p k *
        ((N x : GL (Fin 2) 𝔽) : Matrix (Fin 2) (Fin 2) 𝔽) k q := by
    funext x; rw [Units.val_mul, Matrix.mul_apply]
  rw [this]
  exact ContDiff.sum fun k _ => (hM p k).mul (hN k q)

theorem smoothM_list_prod {𝔽 : Type} [RCLike 𝔽] {ι : Type} (l : List ι) (G : ι → X → GL (Fin 2) 𝔽)
    (h : ∀ i ∈ l, SmoothM (G i)) : SmoothM fun x => (l.map fun i => G i x).prod := by
  induction l with
  | nil => simpa using (smoothM_one (X := X) (𝔽 := 𝔽))
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact smoothM_mul (h i List.mem_cons_self) (ih fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))

theorem smoothM_ofFn_prod {𝔽 : Type} [RCLike 𝔽] {n : ℕ} (G : Fin n → X → GL (Fin 2) 𝔽) (h : ∀ j, SmoothM (G j)) :
    SmoothM fun x => (List.ofFn fun j => G j x).prod := by
  have : (fun x => (List.ofFn fun j => G j x).prod) = fun x => ((List.finRange n).map fun j => G j x).prod := by
    funext x; rw [List.ofFn_eq_map]
  rw [this]
  exact smoothM_list_prod _ G fun j _ => h j

theorem smoothM_archFlowMatrix (dir : ArchDir) (c : X → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    SmoothM fun x => archFlowMatrix dir (c x) := by
  intro p q
  cases dir <;> fin_cases p <;> fin_cases q <;>
    simp only [archFlowMatrix, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
      | exact contDiff_const
      | exact hc
      | exact Real.contDiff_exp.comp hc
      | exact Real.contDiff_exp.comp hc.neg

theorem smoothM_archFlowMatrixComplex (dir : ArchDirComplex) (c : X → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) :
    SmoothM fun x => archFlowMatrixComplex dir (c x) := by
  intro p q
  have hcC : ContDiff ℝ (⊤ : ℕ∞) fun x => ((c x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp hc
  have hcI : ContDiff ℝ (⊤ : ℕ∞) fun x => ((c x : ℝ) : ℂ) * Complex.I := hcC.mul contDiff_const
  cases dir <;> fin_cases p <;> fin_cases q <;>
    simp only [archFlowMatrixComplex, splitTorusGL2Complex, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
      | exact contDiff_const
      | exact hcC
      | exact hcI
      | exact Complex.contDiff_exp.comp hcC
      | exact Complex.contDiff_exp.comp hcC.neg
      | exact Complex.contDiff_exp.comp hcI
      | exact Complex.contDiff_exp.comp hcI.neg

theorem smoothM_scalR (c : X → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) : SmoothM fun x => scalR (c x) := by
  intro p q
  simp only [scalR_apply]
  split_ifs
  · exact Real.contDiff_exp.comp hc
  · exact contDiff_const

theorem smoothM_scalC (c : X → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) : SmoothM fun x => scalC (c x) := by
  intro p q
  simp only [scalC_apply]
  split_ifs
  · exact Complex.contDiff_exp.comp hc
  · exact contDiff_const

end Smooth
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.H2Basis"

variable (L₀ : List (Letter K))

theorem smoothM_piR_flow (w : {w : InfinitePlace K // w.IsReal}) (j : Fin L₀.length) :
    SmoothM fun v : (Fin L₀.length → ℝ) × mixedSpace K => piR K w (flow K (L₀.get j) (v.1 j)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) fun v : (Fin L₀.length → ℝ) × mixedSpace K => v.1 j :=
    (contDiff_apply ℝ ℝ j).comp contDiff_fst
  simp only [piR_flow]
  rcases L₀.get j with ⟨w₀, hw₀, dir⟩ | ⟨w₀, hw₀, dir⟩
  · simp only [Sum.elim_inl]
    split_ifs
    · exact smoothM_archFlowMatrix dir _ hc
    · exact smoothM_one
  · simp only [Sum.elim_inr]
    exact smoothM_one

theorem smoothM_piC_flow (w : {w : InfinitePlace K // w.IsComplex}) (j : Fin L₀.length) :
    SmoothM fun v : (Fin L₀.length → ℝ) × mixedSpace K => piC K w (flow K (L₀.get j) (v.1 j)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) fun v : (Fin L₀.length → ℝ) × mixedSpace K => v.1 j :=
    (contDiff_apply ℝ ℝ j).comp contDiff_fst
  simp only [piC_flow]
  rcases L₀.get j with ⟨w₀, hw₀, dir⟩ | ⟨w₀, hw₀, dir⟩
  · simp only [Sum.elim_inl]
    exact smoothM_one
  · simp only [Sum.elim_inr]
    split_ifs
    · exact smoothM_archFlowMatrixComplex dir _ hc
    · exact smoothM_one

theorem smoothM_piR_ψ (w : {w : InfinitePlace K // w.IsReal}) :
    SmoothM fun v : (Fin L₀.length → ℝ) × mixedSpace K => piR K w (ψ K L₀ v) := by
  simp only [piR_ψ]
  refine smoothM_mul (smoothM_ofFn_prod _ fun j => smoothM_piR_flow K L₀ w j) (smoothM_scalR _ ?_)
  exact (contDiff_apply ℝ ℝ w).comp (contDiff_fst.comp contDiff_snd)

theorem smoothM_piC_ψ (w : {w : InfinitePlace K // w.IsComplex}) :
    SmoothM fun v : (Fin L₀.length → ℝ) × mixedSpace K => piC K w (ψ K L₀ v) := by
  simp only [piC_ψ]
  refine smoothM_mul (smoothM_ofFn_prod _ fun j => smoothM_piC_flow K L₀ w j) (smoothM_scalC _ ?_)
  exact (contDiff_apply ℝ ℂ w).comp (contDiff_snd.comp contDiff_snd)

theorem contDiff_F : ContDiff ℝ (⊤ : ℕ∞) (F K L₀) := by
  rw [F_eq, contDiff_pi]
  intro p
  rw [contDiff_pi]
  intro q
  refine ContDiff.prodMk ?_ ?_
  · exact contDiff_pi.mpr fun w => smoothM_piR_ψ K L₀ w p q
  · exact contDiff_pi.mpr fun w => smoothM_piC_ψ K L₀ w p q

theorem continuous_F : Continuous (F K L₀) := (contDiff_F K L₀).continuous

theorem scal_zero : scal K 0 0 = 1 := by
  have h1 : ∀ w : {w : InfinitePlace K // w.IsReal}, (fun w => sR K w ((0 : {w : InfinitePlace K // w.IsReal} → ℝ) w)) w = 1 :=
    fun w => by show sR K w 0 = 1; rw [sR, scalR_zero, map_one]
  have h2 : ∀ w : {w : InfinitePlace K // w.IsComplex}, (fun w => sC K w ((0 : {w : InfinitePlace K // w.IsComplex} → ℂ) w)) w = 1 :=
    fun w => by show sC K w 0 = 1; rw [sC, scalC_zero, map_one]
  rw [scal, prod_map_toList_univ_eq_one _ h1, prod_map_toList_univ_eq_one _ h2, one_mul]

theorem chart_zero : chart K L₀ 0 = 1 :=
  prod_ofFn_eq_one _ fun i => by rw [Pi.zero_apply, flow_zero]

theorem ψ_single (j : Fin L₀.length) (s : ℝ) :
    ψ K L₀ ((Pi.single j s : Fin L₀.length → ℝ), (0 : mixedSpace K)) = flow K (L₀.get j) s := by
  rw [ψ]
  dsimp only
  rw [chart, prod_ofFn_eq_single _ j (fun i hi => by rw [Pi.single_eq_of_ne hi, flow_zero]), Pi.single_eq_same,
    Prod.fst_zero, Prod.snd_zero, scal_zero, mul_one]

theorem ψ_zero_smul (x : mixedSpace K) (s : ℝ) :
    ψ K L₀ ((0 : Fin L₀.length → ℝ), s • x) = scal K (s • x.1) (s • x.2) := by
  rw [ψ]
  dsimp only
  rw [chart_zero, one_mul, Prod.smul_fst, Prod.smul_snd]

theorem hasDerivAt_archFlowMatrixComplex_apply (d : ArchDirComplex) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i j) (H2Basis.XC d i j) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).comp_ofReal
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by simpa using h1.mul_const Complex.I
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) 1 0 := by simpa using h1.cexp
  have h4 : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ))) (-1) 0 := by simpa using h1.neg.cexp
  have h5 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) Complex.I 0 := by simpa using h2.cexp
  have h6 : HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * Complex.I))) (-Complex.I) 0 := by simpa using h2.neg.cexp
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrixComplex, splitTorusGL2Complex, unipotentGL2_coe, lowerUnipotentGL2_coe, H2Basis.XC,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
      | exact hasDerivAt_const _ _
      | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6

theorem hasDerivAt_scalR_apply (c : ℝ) (p q : Fin 2) :
    HasDerivAt (fun s : ℝ => (scalR (s * c) : Matrix (Fin 2) (Fin 2) ℝ) p q) (if p = q then c else 0) 0 := by
  simp only [scalR_apply]
  split_ifs
  · have := (Real.hasDerivAt_exp (0 * c)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).mul_const c)
    simp at this
    exact this
  · exact hasDerivAt_const _ _

theorem hasDerivAt_scalC_apply (c : ℂ) (p q : Fin 2) :
    HasDerivAt (fun s : ℝ => (scalC ((s : ℂ) * c) : Matrix (Fin 2) (Fin 2) ℂ) p q) (if p = q then c else 0) 0 := by
  simp only [scalC_apply]
  split_ifs
  · have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).comp_ofReal
    simpa using (h1.mul_const c).cexp
  · exact hasDerivAt_const _ _

theorem hasDerivAt_F_single (j : Fin L₀.length) :
    HasDerivAt (fun s : ℝ => F K L₀ ((Pi.single j s : Fin L₀.length → ℝ), (0 : mixedSpace K)))
      (H2Basis.Xhat (L₀.get j)) 0 := by
  rw [F_eq]
  simp only [ψ_single]
  rw [hasDerivAt_pi]
  intro p
  rw [hasDerivAt_pi]
  intro q
  rcases hj : L₀.get j with ⟨w₀, hw₀, dir⟩ | ⟨w₀, hw₀, dir⟩
  · rw [H2Basis.Xhat_inl]
    refine HasDerivAt.prodMk ?_ ?_
    · rw [hasDerivAt_pi]
      intro w
      simp only [piR_flow, Sum.elim_inl]
      split_ifs
      · exact hasDerivAt_archFlowMatrix_apply dir p q
      · simp only [Units.val_one]
        exact hasDerivAt_const _ _
    · rw [hasDerivAt_pi]
      intro w
      simp only [piC_flow, Sum.elim_inl, Units.val_one, Pi.zero_apply]
      exact hasDerivAt_const _ _
  · rw [H2Basis.Xhat_inr]
    refine HasDerivAt.prodMk ?_ ?_
    · rw [hasDerivAt_pi]
      intro w
      simp only [piR_flow, Sum.elim_inr, Units.val_one, Pi.zero_apply]
      exact hasDerivAt_const _ _
    · rw [hasDerivAt_pi]
      intro w
      simp only [piC_flow, Sum.elim_inr]
      split_ifs
      · exact hasDerivAt_archFlowMatrixComplex_apply dir p q
      · simp only [Units.val_one]
        exact hasDerivAt_const _ _

theorem central_fst (x : mixedSpace K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsReal}) :
    (H2Basis.central K x p q).1 w = if p = q then x.1 w else 0 := by
  rw [H2Basis.central_apply]; split_ifs <;> rfl

theorem central_snd (x : mixedSpace K) (p q : Fin 2) (w : {w : InfinitePlace K // w.IsComplex}) :
    (H2Basis.central K x p q).2 w = if p = q then x.2 w else 0 := by
  rw [H2Basis.central_apply]; split_ifs <;> rfl

theorem hasDerivAt_F_central (x : mixedSpace K) :
    HasDerivAt (fun s : ℝ => F K L₀ ((0 : Fin L₀.length → ℝ), s • x)) (H2Basis.central K x) 0 := by
  have hc : H2Basis.central K x = fun p q =>
      ((fun w => if p = q then x.1 w else 0, fun w => if p = q then x.2 w else 0) : mixedSpace K) := by
    funext p q
    exact Prod.ext (funext fun w => central_fst K x p q w) (funext fun w => central_snd K x p q w)
  rw [F_eq, hc]
  simp only [ψ_zero_smul]
  rw [hasDerivAt_pi]
  intro p
  rw [hasDerivAt_pi]
  intro q
  refine HasDerivAt.prodMk ?_ ?_
  · rw [hasDerivAt_pi]
    intro w
    simp only [piR_scal, Pi.smul_apply, smul_eq_mul]
    exact hasDerivAt_scalR_apply (x.1 w) p q
  · rw [hasDerivAt_pi]
    intro w
    simp only [piC_scal, Pi.smul_apply, Complex.real_smul]
    exact hasDerivAt_scalC_apply (x.2 w) p q

theorem hasDerivAt_F_smul (u : (Fin L₀.length → ℝ) × mixedSpace K) :
    HasDerivAt (fun s : ℝ => F K L₀ (s • u)) (fderiv ℝ (F K L₀) 0 u) 0 := by
  have hF : HasFDerivAt (F K L₀) (fderiv ℝ (F K L₀) 0) ((0 : ℝ) • u) := by
    rw [zero_smul]
    exact (((contDiff_F K L₀).differentiable (by simp)).differentiableAt).hasFDerivAt
  have hγ : HasDerivAt (fun s : ℝ => s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u)
  exact hF.comp_hasDerivAt (0 : ℝ) hγ

theorem fderiv_F_single (j : Fin L₀.length) :
    fderiv ℝ (F K L₀) 0 ((Pi.single j 1 : Fin L₀.length → ℝ), (0 : mixedSpace K)) = H2Basis.Xhat (L₀.get j) := by
  have h1 := hasDerivAt_F_smul K L₀ ((Pi.single j 1 : Fin L₀.length → ℝ), (0 : mixedSpace K))
  have heq : (fun s : ℝ => F K L₀ (s • ((Pi.single j (1 : ℝ) : Fin L₀.length → ℝ), (0 : mixedSpace K)))) =
      fun s => F K L₀ ((Pi.single j s : Fin L₀.length → ℝ), (0 : mixedSpace K)) := by
    funext s
    congr 1
    refine Prod.ext (funext fun i => ?_) (smul_zero s)
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [heq] at h1
  exact h1.unique (hasDerivAt_F_single K L₀ j)

theorem fderiv_F_central (x : mixedSpace K) :
    fderiv ℝ (F K L₀) 0 ((0 : Fin L₀.length → ℝ), x) = H2Basis.central K x := by
  have h1 := hasDerivAt_F_smul K L₀ ((0 : Fin L₀.length → ℝ), x)
  have heq : (fun s : ℝ => F K L₀ (s • ((0 : Fin L₀.length → ℝ), x))) =
      fun s => F K L₀ ((0 : Fin L₀.length → ℝ), s • x) := by
    funext s; rw [Prod.smul_mk, smul_zero]
  rw [heq] at h1
  exact h1.unique (hasDerivAt_F_central K L₀ x)

theorem fderiv_F_eq_tangentMap :
    ((fderiv ℝ (F K L₀) 0 : ((Fin L₀.length → ℝ) × mixedSpace K) →L[ℝ] (Fin 2 → Fin 2 → mixedSpace K)) :
      ((Fin L₀.length → ℝ) × mixedSpace K) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedSpace K)) = H2Basis.tangentMap K L₀ :=
  H2Basis.eq_tangentMap_of L₀ _ (fun j => fderiv_F_single K L₀ j) (fun x => fderiv_F_central K L₀ x)

theorem hasFDerivAt_F (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) :
    HasFDerivAt (F K L₀)
      (H2Basis.tangentEquiv K L₀ hL₀ hL₀' : ((Fin L₀.length → ℝ) × mixedSpace K) →L[ℝ] H2Basis.E K) 0 := by
  have h : HasFDerivAt (F K L₀) (fderiv ℝ (F K L₀) 0) 0 :=
    (((contDiff_F K L₀).differentiable (by simp)).differentiableAt).hasFDerivAt
  have he : fderiv ℝ (F K L₀) 0 =
      (H2Basis.tangentEquiv K L₀ hL₀ hL₀' : ((Fin L₀.length → ℝ) × mixedSpace K) →L[ℝ] H2Basis.E K) := by
    rw [H2Basis.coe_tangentEquiv]
    apply ContinuousLinearMap.coe_injective
    rw [fderiv_F_eq_tangentMap]
    rfl
  rw [← he]
  exact h

section Cont

open NumberField.InfinitePlace.Completion

theorem continuous_adelicArchGLInclAt_comp {X : Type*} [TopologicalSpace X] {w : InfinitePlace K} (k : X → GL (Fin 2) w.Completion)
    (hk : ∀ i j, Continuous fun t => (k t : Matrix (Fin 2) (Fin 2) w.Completion) i j)
    (hki : ∀ i j, Continuous fun t => (((k t)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) :
    Continuous fun t => (adelicArchGLInclAt K w (k t) : AdelicGL2 (𝓞 K) K) := by
  have key : ∀ (m : X → Matrix (Fin 2) (Fin 2) w.Completion), (∀ i j, Continuous fun t => m t i j) →
      Continuous fun t => fun i j => ((fun v => (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
        (m t)) v i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) := by
    intro m hm
    have hM : Continuous fun t => (fun i j => m t i j : Matrix (Fin 2) (Fin 2) w.Completion) :=
      continuous_pi fun i => continuous_pi fun j => hm i j
    have hU : Continuous fun t => Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w (m t) :=
      continuous_const.update w hM
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_pi fun v => ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply v).comp hU)))
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (fun t => ((adelicArchGLInclAt K w (k t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
        fun t => fun i j => ((fun v => (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
          ((k t : Matrix (Fin 2) (Fin 2) w.Completion))) v i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) := by
      funext t; ext i j; rfl
    change Continuous fun t => ((adelicArchGLInclAt K w (k t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    rw [this]; exact key _ hk
  · have : (fun t => (((adelicArchGLInclAt K w (k t))⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
        fun t => fun i j => ((fun v => (Function.update (1 : Π v : InfinitePlace K, Matrix (Fin 2) (Fin 2) v.Completion) w
          (((k t)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) v i j,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) : AdeleRing (𝓞 K) K) := by
      funext t; rw [← map_inv]; ext i j; rfl
    change Continuous fun t => (((adelicArchGLInclAt K w (k t))⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    rw [this]; exact key _ hki

theorem continuous_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) : Continuous (archRealGLAt (F := K) hw) := by
  have hdef : archRealGLAt (F := K) hw = (adelicArchGLInclAt K w).comp (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom := rfl
  rw [hdef, MonoidHom.coe_comp]
  refine continuous_adelicArchGLInclAt_comp K _ (fun i j => ?_) (fun i j => ?_)
  · show Continuous fun m : GL (Fin 2) ℝ => (ringEquivRealOfIsReal hw).symm (((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)
    have hv : Continuous (fun m : GL (Fin 2) ℝ => ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := Units.continuous_val
    exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (hv.matrix_elem i j)
  · have : (fun m : GL (Fin 2) ℝ => ((((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom m)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) =
        fun m : GL (Fin 2) ℝ => (ringEquivRealOfIsReal hw).symm (((m⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
      funext m; rw [← map_inv]; rfl
    rw [this]
    have hi : Continuous (fun m : GL (Fin 2) ℝ => (((m⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) := Units.continuous_coe_inv
    exact (isometryEquivRealOfIsReal hw).symm.continuous.comp (hi.matrix_elem i j)

theorem continuous_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) : Continuous (archComplexGLAt (F := K) hw) := by
  have hdef : archComplexGLAt (F := K) hw = (adelicArchGLInclAt K w).comp (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm).toMonoidHom := rfl
  rw [hdef, MonoidHom.coe_comp]
  refine continuous_adelicArchGLInclAt_comp K _ (fun i j => ?_) (fun i j => ?_)
  · show Continuous fun m : GL (Fin 2) ℂ => (ringEquivComplexOfIsComplex hw).symm (((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)
    have hv : Continuous (fun m : GL (Fin 2) ℂ => ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := Units.continuous_val
    exact (isometryEquivComplexOfIsComplex hw).symm.continuous.comp (hv.matrix_elem i j)
  · have : (fun m : GL (Fin 2) ℂ => ((((glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm).toMonoidHom m)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j) =
        fun m : GL (Fin 2) ℂ => (ringEquivComplexOfIsComplex hw).symm (((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j) := by
      funext m; rw [← map_inv]; rfl
    rw [this]
    have hi : Continuous (fun m : GL (Fin 2) ℂ => (((m⁻¹ : GL (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)) := Units.continuous_coe_inv
    exact (isometryEquivComplexOfIsComplex hw).symm.continuous.comp (hi.matrix_elem i j)

end Cont
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.H2Basis"

theorem scalR_neg (a : ℝ) : scalR (-a) = (scalR a)⁻¹ := by
  symm; apply inv_eq_of_mul_eq_one_right
  ext p q
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply]
  simp only [scalR_apply, Fin.sum_univ_two]
  fin_cases p <;> fin_cases q <;> simp [← Real.exp_add]

theorem scalC_neg (b : ℂ) : scalC (-b) = (scalC b)⁻¹ := by
  symm; apply inv_eq_of_mul_eq_one_right
  ext p q
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply]
  simp only [scalC_apply, Fin.sum_univ_two]
  fin_cases p <;> fin_cases q <;> simp [← Complex.exp_add]

theorem continuous_scalR_val : Continuous fun a : ℝ => (scalR a : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine continuous_matrix fun p q => ?_
  simp only [scalR_apply]
  split_ifs
  · exact Real.continuous_exp
  · exact continuous_const

theorem continuous_scalR : Continuous scalR := by
  refine Units.continuous_iff.mpr ⟨continuous_scalR_val, ?_⟩
  show Continuous (fun a : ℝ => (((scalR a)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
  have : (fun a : ℝ => (((scalR a)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
      fun a => ((scalR (-a) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    funext a; rw [scalR_neg]
  rw [this]
  exact continuous_scalR_val.comp continuous_neg

theorem continuous_scalC_val : Continuous fun b : ℂ => (scalC b : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine continuous_matrix fun p q => ?_
  simp only [scalC_apply]
  split_ifs
  · exact Complex.continuous_exp
  · exact continuous_const

theorem continuous_scalC : Continuous scalC := by
  refine Units.continuous_iff.mpr ⟨continuous_scalC_val, ?_⟩
  show Continuous (fun b : ℂ => (((scalC b)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))
  have : (fun b : ℂ => (((scalC b)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
      fun b => ((scalC (-b) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext b; rw [scalC_neg]
  rw [this]
  exact continuous_scalC_val.comp continuous_neg

theorem continuous_flow (d : Letter K) : Continuous (flow K d) := by
  obtain ⟨hR, hC⟩ := AutomorphicForm.continuous_archFlowAt_and_continuous_archFlowAtComplex K
  rcases d with ⟨w, hw, dir⟩ | ⟨w, hw, dir⟩
  · exact hR w hw dir
  · exact hC w hw dir

theorem continuous_chart : Continuous (chart K L₀) := by
  have : chart K L₀ = fun t => (((List.finRange L₀.length).map fun j => flow K (L₀.get j) (t j))).prod := by
    funext t; simp only [chart, List.ofFn_eq_map]
  rw [this]
  exact continuous_list_prod _ fun j _ => (continuous_flow K _).comp (continuous_apply j)

theorem continuous_scal : Continuous fun x : mixedSpace K => scal K x.1 x.2 := by
  unfold scal
  refine Continuous.mul ?_ ?_
  · exact continuous_list_prod _ fun w _ =>
      ((continuous_archRealGLAt K w.2).comp continuous_scalR).comp ((continuous_apply w).comp continuous_fst)
  · exact continuous_list_prod _ fun w _ =>
      ((continuous_archComplexGLAt K w.2).comp continuous_scalC).comp ((continuous_apply w).comp continuous_snd)

theorem continuous_ψ : Continuous (ψ K L₀) :=
  ((continuous_chart K L₀).comp continuous_fst).mul ((continuous_scal K).comp continuous_snd)

def Box (ℓ : ℝ) : Set ((Fin L₀.length → ℝ) × mixedSpace K) :=
  (Set.pi Set.univ fun _ : Fin L₀.length => Set.Icc (-ℓ) ℓ) ×ˢ
    ((Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsReal} => Set.Icc (-ℓ) ℓ) ×ˢ
      (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) ℓ))

theorem isCompact_Box (ℓ : ℝ) : IsCompact (Box K L₀ ℓ) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).prod
    ((isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _))

theorem measurableSet_Box (ℓ : ℝ) : MeasurableSet (Box K L₀ ℓ) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod
    ((MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod (MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet))

theorem norm_le_of_mem_Box {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {v : (Fin L₀.length → ℝ) × mixedSpace K} (hv : v ∈ Box K L₀ ℓ) :
    ‖v‖ ≤ ℓ := by
  obtain ⟨ht, hab⟩ := Set.mem_prod.mp hv
  obtain ⟨ha, hb⟩ := Set.mem_prod.mp hab
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg hℓ).2 fun i => ?_) ?_
  · have h := (Set.mem_univ_pi.mp ht) i
    rw [Real.norm_eq_abs, abs_le]; exact ⟨h.1, h.2⟩
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg hℓ).2 fun w => ?_) ((pi_norm_le_iff_of_nonneg hℓ).2 fun w => ?_)
  · have h := (Set.mem_univ_pi.mp ha) w
    rw [Real.norm_eq_abs, abs_le]; exact ⟨h.1, h.2⟩
  · have h := (Set.mem_univ_pi.mp hb) w
    rwa [Metric.mem_closedBall, dist_zero_right] at h

omit [NumberField K] in
theorem continuous_of : Continuous (fun e : Fin 2 → Fin 2 → mixedSpace K => Matrix.of e) :=
  continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)

theorem isOpen_U : IsOpen {e : Fin 2 → Fin 2 → mixedSpace K | IsUnit (Matrix.of e)} := by
  have : {e : Fin 2 → Fin 2 → mixedSpace K | IsUnit (Matrix.of e)} =
      (fun e : Fin 2 → Fin 2 → mixedSpace K => (Matrix.of e).det) ⁻¹' {x : mixedSpace K | IsUnit x} := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Matrix.isUnit_iff_isUnit_det]
  rw [this]
  exact Units.isOpen.preimage ((continuous_of K).matrix_det)

theorem main [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) :
    ∃ μ : Measure (GL (Fin 2) (InfiniteAdeleRing K)), μ.IsHaarMeasure ∧ μ.Regular ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ℓ ≤ 1 / 4 ∧ ∃ S : Set (GL (Fin 2) (InfiniteAdeleRing K)), IsCompact S ∧ ∃ c : NNReal,
        ∀ H : GL (Fin 2) (InfiniteAdeleRing K) → ENNReal, Measurable H →
          ∫⁻ v in Box K L₀ ℓ, H (glArch (𝓞 K) K (ψ K L₀ v)) ≤ (c : ENNReal) * ∫⁻ g in S, H g ∂μ := by

  obtain ⟨hρcont, hρpos, hΦU, hΨΦ, μ, hμ, hreg, hμf⟩ :=
    NumberField.InfiniteAdeleRing.exists_isHaarMeasure_lintegral_eq_setLIntegral_inv_abs_norm_mixedSpace (Fin 2) K
  haveI := hμ
  haveI := hreg

  set U : Set (Fin 2 → Fin 2 → mixedSpace K) := {e | IsUnit (Matrix.of e)} with hU
  set ρ : (Fin 2 → Fin 2 → mixedSpace K) → ℝ≥0∞ := fun e => ENNReal.ofReal |Algebra.norm ℝ (Matrix.of e)|⁻¹ with hρ
  set Ψ : (Fin 2 → Fin 2 → mixedSpace K) → GL (Fin 2) (InfiniteAdeleRing K) := fun e =>
    if h : IsUnit (Matrix.of e) then (h.map (ringEquiv_mixedSpace K).symm.mapMatrix).unit else 1 with hΨ
  have hFU : ∀ v, F K L₀ v ∈ U := fun v => hΦU (glArch (𝓞 K) K (ψ K L₀ v))
  have hΨF : ∀ v, Ψ (F K L₀ v) = glArch (𝓞 K) K (ψ K L₀ v) := fun v => hΨΦ (glArch (𝓞 K) K (ψ K L₀ v))

  haveI : BorelSpace (Fin 2 → Fin 2 → mixedSpace K) := H2Cov.borelSpace_E (Fin 2) K
  haveI := H2Cov.isAddHaarMeasure_volume_E (Fin 2) K
  haveI := H2Cov.sigmaFinite_volume_E (Fin 2) K
  haveI := H2Cov.isAddHaarMeasure_volume_V K (Fin L₀.length)

  have hC1 : ContDiffAt ℝ 1 (F K L₀) 0 := ((contDiff_F K L₀).of_le (by exact_mod_cast le_top)).contDiffAt
  obtain ⟨s, hs_open, hs0, -, δ, hδ, hcov⟩ :=
    H2Cov.exists_isOpen_injOn_mul_lintegral_comp_le volume volume (F K L₀) (H2Basis.tangentEquiv K L₀ hL₀ hL₀')
      hC1 (hasFDerivAt_F K L₀ hL₀ hL₀')

  have hρ0 : 0 < ρ (F K L₀ 0) := hρpos _ (hFU 0)
  have hρtop : ρ (F K L₀ 0) ≠ ⊤ := ENNReal.ofReal_ne_top
  set ρ₀ : ℝ≥0∞ := ρ (F K L₀ 0) / 2 with hρ₀
  have hρ₀pos : ρ₀ ≠ 0 := (ENNReal.half_pos hρ0.ne').ne'
  have hρ₀top : ρ₀ ≠ ⊤ := by
    rw [hρ₀]; exact ENNReal.div_ne_top hρtop two_ne_zero
  have hUo : IsOpen U := isOpen_U K
  have hWo : IsOpen (U ∩ ρ ⁻¹' Set.Ioi ρ₀) := hρcont.isOpen_inter_preimage hUo isOpen_Ioi
  have h0W : F K L₀ 0 ∈ U ∩ ρ ⁻¹' Set.Ioi ρ₀ := ⟨hFU 0, ENNReal.half_lt_self hρ0.ne' hρtop⟩

  set O : Set ((Fin L₀.length → ℝ) × mixedSpace K) := s ∩ F K L₀ ⁻¹' (U ∩ ρ ⁻¹' Set.Ioi ρ₀) with hO
  have hOo : IsOpen O := hs_open.inter (hWo.preimage (continuous_F K L₀))
  have h0O : (0 : (Fin L₀.length → ℝ) × mixedSpace K) ∈ O := ⟨hs0, h0W⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOo 0 h0O
  set ℓ : ℝ := min (ε / 2) (1 / 4) with hℓ
  have hℓpos : 0 < ℓ := lt_min (half_pos hε) (by norm_num)
  have hℓε : ℓ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hBoxO : Box K L₀ ℓ ⊆ O := fun v hv =>
    hball (by rw [Metric.mem_ball, dist_zero_right]; exact (norm_le_of_mem_Box K L₀ hℓpos.le hv).trans_lt hℓε)

  set S : Set (GL (Fin 2) (InfiniteAdeleRing K)) := (fun v => glArch (𝓞 K) K (ψ K L₀ v)) '' Box K L₀ ℓ with hS
  have hSc : IsCompact S := (isCompact_Box K L₀ ℓ).image ((continuous_glArch (𝓞 K) K).comp (continuous_ψ K L₀))
  have hSm : MeasurableSet S := hSc.measurableSet
  have hFBc : IsCompact (F K L₀ '' Box K L₀ ℓ) := (isCompact_Box K L₀ ℓ).image (continuous_F K L₀)
  have hFBm : MeasurableSet (F K L₀ '' Box K L₀ ℓ) := hFBc.measurableSet
  have hFBU : F K L₀ '' Box K L₀ ℓ ⊆ U := by
    rintro e ⟨v, -, rfl⟩; exact hFU v

  have hden0 : (δ : ℝ≥0∞) * ρ₀ ≠ 0 := mul_ne_zero (by exact_mod_cast hδ.ne') hρ₀pos
  have hdentop : (δ : ℝ≥0∞) * ρ₀ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hρ₀top
  have hcfin : ((δ : ℝ≥0∞) * ρ₀)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hden0
  refine ⟨μ, hμ, hreg, ℓ, hℓpos, min_le_right _ _, S, hSc, (((δ : ℝ≥0∞) * ρ₀)⁻¹).toNNReal, fun H hH => ?_⟩
  rw [ENNReal.coe_toNNReal hcfin]

  have h1 : (δ : ℝ≥0∞) * ∫⁻ v in Box K L₀ ℓ, H (glArch (𝓞 K) K (ψ K L₀ v)) ≤
      ∫⁻ e in F K L₀ '' Box K L₀ ℓ, H (Ψ e) := by
    have := hcov (Box K L₀ ℓ) (fun v hv => (hBoxO hv).1) (measurableSet_Box K L₀ ℓ) (fun e => H (Ψ e))
    simp only [hΨF] at this
    exact this

  have h2 : ρ₀ * ∫⁻ e in F K L₀ '' Box K L₀ ℓ, H (Ψ e) ≤ ∫⁻ e in F K L₀ '' Box K L₀ ℓ, H (Ψ e) * ρ e := by
    rw [← lintegral_const_mul' _ _ hρ₀top]
    refine setLIntegral_mono' hFBm fun e he => ?_
    obtain ⟨v, hv, rfl⟩ := he
    have hlt : ρ₀ < ρ (F K L₀ v) := ((hBoxO hv).2).2
    rw [mul_comm]
    exact mul_le_mul_right hlt.le _

  have h3 : ∫⁻ e in F K L₀ '' Box K L₀ ℓ, H (Ψ e) * ρ e ≤ ∫⁻ g in S, H g ∂μ := by
    have heq : ∀ e ∈ F K L₀ '' Box K L₀ ℓ, H (Ψ e) * ρ e = S.indicator H (Ψ e) * ρ e := by
      rintro e ⟨v, hv, rfl⟩
      rw [Set.indicator_of_mem]
      exact ⟨v, hv, (hΨF v).symm⟩
    rw [setLIntegral_congr_fun hFBm heq, ← lintegral_indicator hSm, hμf _ (hH.indicator hSm)]
    exact lintegral_mono_set hFBU

  have h4 : (δ : ℝ≥0∞) * ρ₀ * ∫⁻ v in Box K L₀ ℓ, H (glArch (𝓞 K) K (ψ K L₀ v)) ≤ ∫⁻ g in S, H g ∂μ :=
    calc (δ : ℝ≥0∞) * ρ₀ * ∫⁻ v in Box K L₀ ℓ, H (glArch (𝓞 K) K (ψ K L₀ v))
        = ρ₀ * ((δ : ℝ≥0∞) * ∫⁻ v in Box K L₀ ℓ, H (glArch (𝓞 K) K (ψ K L₀ v))) := by ring
      _ ≤ ρ₀ * ∫⁻ e in F K L₀ '' Box K L₀ ℓ, H (Ψ e) := mul_le_mul_right h1 _
      _ ≤ ∫⁻ e in F K L₀ '' Box K L₀ ℓ, H (Ψ e) * ρ e := h2
      _ ≤ ∫⁻ g in S, H g ∂μ := h3
  calc ∫⁻ v in Box K L₀ ℓ, H (glArch (𝓞 K) K (ψ K L₀ v))
      = ((δ : ℝ≥0∞) * ρ₀)⁻¹ * ((δ : ℝ≥0∞) * ρ₀ * ∫⁻ v in Box K L₀ ℓ, H (glArch (𝓞 K) K (ψ K L₀ v))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hden0 hdentop, one_mul]
    _ ≤ ((δ : ℝ≥0∞) * ρ₀)⁻¹ * ∫⁻ g in S, H g ∂μ := mul_le_mul_right h4 _

end H2Proof
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le.H2Basis"

attribute [local instance] NumberField.AdelicHaar.glBorel

open H2Proof in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀)
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))] :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    let scal : ({w : InfinitePlace K // w.IsReal} → ℝ) → ({w : InfinitePlace K // w.IsComplex} → ℂ) → AdelicGL2 (𝓞 K) K :=
      fun a b =>
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map fun w =>
            archRealGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp (a w)) (Real.exp_ne_zero (a w))))).prod *
        ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map fun w =>
            archComplexGLAt w.2 (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (b w)) (Complex.exp_ne_zero (b w))))).prod
    ∃ μ : Measure (GL (Fin 2) (InfiniteAdeleRing K)), μ.IsHaarMeasure ∧ μ.Regular ∧
      ∃ ℓ : ℝ, 0 < ℓ ∧ ℓ ≤ 1 / 4 ∧ ∃ S : Set (GL (Fin 2) (InfiniteAdeleRing K)), IsCompact S ∧ ∃ c : NNReal,
        ∀ H : GL (Fin 2) (InfiniteAdeleRing K) → ENNReal, Measurable H →
          ∫⁻ v in (Set.pi Set.univ fun _ : Fin L₀.length => Set.Icc (-ℓ) ℓ) ×ˢ
              ((Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsReal} => Set.Icc (-ℓ) ℓ) ×ˢ
                (Set.pi Set.univ fun _ : {w : InfinitePlace K // w.IsComplex} => Metric.closedBall (0 : ℂ) ℓ)),
            H (glArch (𝓞 K) K (chart v.1 * scal v.2.1 v.2.2)) ≤
          (c : ENNReal) * ∫⁻ g in S, H g ∂μ :=
  H2Proof.main K L₀ hL₀ hL₀'

end
end S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_lintegral_comp_glArch_flowChart_mul_le (solution)
