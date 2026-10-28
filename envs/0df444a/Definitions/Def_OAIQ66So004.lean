-- Prove2me | Definitions.Def_OAIQ66So004
-- name    : OAIQ66So004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:10:58.120802+00:00
-- url     : https://prove2.me/theorems/641f318f-b939-4f34-ab27-6a1fe783caac
-- title:
--   Definitions bundle OAIQ66So004 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 164 declarations of OpenAI's Lean: 85 definitions, 2 instances and 77 theorems. The definitions and types are `OAI.ControlledChains.Chain`, `OAI.ControlledChains.Simplex`, `OAI.ControlledChains.augmentation`, `OAI.ControlledChains.boundary`, `OAI.ControlledChains.cone`, `OAI.ControlledChains.mapChain`, `OAI.CoreDeck.leftAction`, `OAI.CoreDeck.right`, `OAI.CosetCoordinates.correction`, `OAI.CosetCoordinates.equiv`, `OAI.CosetCoordinates.nextCoset`, `OAI.CosetEndpoint.baseShiftCoeff`, `OAI.CosetEndpoint.endpointHomotopy`, `OAI.CosetEndpoint.leftChain`, `OAI.CosetEndpoint.leftVertexMap`, `OAI.CosetEndpoint.rightChain`, `OAI.CosetEndpoint.rightVertexMap`, `OAI.CosetEndpoint.shiftCoeff`, `OAI.CosetInduction.baseHom`, `OAI.CosetInduction.cosetRep`, `OAI.CosetInduction.cosetSection`, `OAI.CosetInduction.cosetsToInd`, `OAI.CosetInduction.indToCosets`, `OAI.CoveringCW.BaseCell`, `OAI.CoveringCW.Cell`, `OAI.CoveringCW.Disk`, `OAI.CoveringCW.Fiber`, `OAI.CoveringCW.baseChar`, `OAI.CoveringCW.characteristic`, `OAI.CoveringCellGeometry.Pullback`, `OAI.CoveringCellGeometry.backLift`, `OAI.CoveringCellGeometry.backTransport`, `OAI.CoveringCellGeometry.characteristicLift`, `OAI.CoveringCellGeometry.constantPullback`, `OAI.CoveringCellGeometry.contraction`, `OAI.CoveringCellGeometry.contractionImage`, `OAI.CoveringCellGeometry.contractionPoint`, `OAI.CoveringCellGeometry.deckPullback`, `OAI.CoveringCellGeometry.endpoint`, `OAI.CoveringCellGeometry.familyLift` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_CoreDeck`, `FiniteType_CosetCoordinates`, `FiniteType_CosetInduction`, `FiniteType_CoveringCellGeometry`, `FiniteType_CoveringCellGeometryHausdorff`, `FiniteType_CubeDisk`, `FiniteType_FiberCoreMap`, `FiniteType_HurewiczInverse`, `FiniteType_OrderListChains`, `FiniteType_ProductCoefficientAffineShift`, `FiniteType_Representation`, `FiniteType_SemilinearCoinvariants`, `FiniteType_SingularAction`, `FiniteType_SingularPrism`, `FiniteType_SphereCover`, `FiniteType_StandardShapiro`, `FiniteType_Steinberg`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So011`, `OAIQ66So012`, `OAIQ66So013` and `OAIQ66So014`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.FiniteType_CubeDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval

open Set Topology Metric
open scoped unitInterval
namespace SphereExtension
universe u
variable {Y : Type u} [TopologicalSpace Y]
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def radial (n : ℕ) : C(I × Boundary n,Disk n) :=
  ⟨fun z => ⟨(z.1:ℝ) • z.2.1,by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg z.1.2.1]
      have hn : ‖z.2.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2.2
      simpa only [hn,mul_one] using z.1.2.2⟩,
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

def zeroDisk (n : ℕ) : Disk n := ⟨0,by simp⟩

abbrev ConeData (n : ℕ) := (I × Boundary n) ⊕ Unit

def coneQuot (n : ℕ) : C(ConeData n,Disk n) :=
  ⟨Sum.elim (radial n) (fun _ => zeroDisk n),
    continuous_sum_dom.mpr ⟨(radial n).continuous,continuous_const⟩⟩

@[simp] theorem norm_radial {n : ℕ} (z : I × Boundary n) :
    ‖(radial n z).1‖ = (z.1:ℝ) := by
  change ‖(z.1:ℝ) • z.2.1‖ = _
  rw [norm_smul,Real.norm_of_nonneg z.1.2.1]
  have hn : ‖z.2.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2.2
  rw [hn,mul_one]

theorem coneQuot_surjective (n : ℕ) : Function.Surjective (coneQuot n) := by
  intro v
  by_cases hv : v.1 = 0
  · exact ⟨Sum.inr (),Subtype.ext hv.symm⟩
  have hn : ‖v.1‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let t : I := ⟨‖v.1‖,norm_nonneg _,by simpa only [mem_closedBall,dist_zero_right] using v.2⟩
  let s : Boundary n := ⟨‖v.1‖⁻¹ • v.1,by
    rw [mem_sphere,dist_zero_right,norm_smul,norm_inv,Real.norm_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ hn⟩
  refine ⟨Sum.inl (t,s),?_⟩
  apply Subtype.ext
  change ‖v.1‖ • (‖v.1‖⁻¹ • v.1) = v.1
  rw [smul_smul,mul_inv_cancel₀ hn,one_smul]

theorem coneQuot_isQuotientMap (n : ℕ) : IsQuotientMap (coneQuot n) :=
  IsQuotientMap.of_surjective_continuous (coneQuot_surjective n) (coneQuot n).continuous

def coneMap {n : ℕ} {f : C(Boundary n,Y)} {y : Y}
    (H : f.Homotopy (.const (Boundary n) y)) : C(ConeData n,Y) :=
  ⟨Sum.elim (fun z => H (unitInterval.symm z.1,z.2)) (fun _ => y),
    continuous_sum_dom.mpr ⟨H.continuous.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd),continuous_const⟩⟩

theorem radial_eq {n : ℕ} {a b : I × Boundary n} (hab : radial n a = radial n b) :
    a.1 = b.1 ∧ ((a.1:ℝ) = 0 ∨ a.2 = b.2) := by
  have htime : (a.1:ℝ) = (b.1:ℝ) := by
    simpa only [norm_radial] using congrArg (fun v : Disk n => ‖v.1‖) hab
  refine ⟨Subtype.ext htime,?_⟩
  by_cases hz : (a.1:ℝ) = 0
  · exact Or.inl hz
  · apply Or.inr
    apply Subtype.ext
    have he : (a.1:ℝ) • a.2.1 = (a.1:ℝ) • b.2.1 := by
      simpa only [radial,ContinuousMap.coe_mk,← htime] using congrArg Subtype.val hab
    exact (smul_right_injective _ hz) he

theorem coneMap_factors {n : ℕ} {f : C(Boundary n,Y)} {y : Y}
    (H : f.Homotopy (.const (Boundary n) y)) :
    Function.FactorsThrough (coneMap H) (coneQuot n) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨ht,hs⟩ := radial_eq hab
      rcases hs with hz | hs
      · have ha : a.1 = 0 := Subtype.ext hz
        have hb : b.1 = 0 := ht.symm.trans ha
        simp [coneMap,ha,hb]
      · have he : a = b := Prod.ext ht hs
        exact congrArg (coneMap H ∘ Sum.inl) he
    | inr b =>
      have hz : (a.1:ℝ) = 0 := by
        have he := congrArg (fun v : Disk n => ‖v.1‖) hab
        simpa only [coneQuot,ContinuousMap.coe_mk,Sum.elim_inl,Sum.elim_inr,zeroDisk,norm_zero,norm_radial] using he
      have ha : a.1 = 0 := Subtype.ext hz
      simp [coneMap,ha]
  | inr a =>
    cases b with
    | inl b =>
      have hz : (b.1:ℝ) = 0 := by
        have he := congrArg (fun v : Disk n => ‖v.1‖) hab.symm
        simpa only [coneQuot,ContinuousMap.coe_mk,Sum.elim_inl,Sum.elim_inr,zeroDisk,norm_zero,norm_radial] using he
      have hb : b.1 = 0 := Subtype.ext hz
      simp [coneMap,hb]
    | inr b => rfl

theorem exists_extension {n : ℕ} (f : C(Boundary n,Y)) (hf : f.Nullhomotopic) :
    ∃ g : C(Disk n,Y),∀ v : Boundary n,g ⟨v,sphere_subset_closedBall v.2⟩ = f v := by
  obtain ⟨y,⟨H⟩⟩ := hf
  let g := (coneQuot_isQuotientMap n).lift (coneMap H) (coneMap_factors H)
  refine ⟨g,?_⟩
  intro v
  have he := DFunLike.congr_fun ((coneQuot_isQuotientMap n).lift_comp (coneMap H) (coneMap_factors H)) (Sum.inl (1,v))
  change g (coneQuot n (Sum.inl (1,v))) = coneMap H (Sum.inl (1,v)) at he
  have hp : coneQuot n (Sum.inl (1,v)) = ⟨v,sphere_subset_closedBall v.2⟩ := by
    apply Subtype.ext
    simp [coneQuot,radial]
  rw [hp] at he
  exact he.trans (by simp [coneMap])

end SphereExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SphereCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval

open scoped unitInterval
open Set
namespace DiscreteCoverCharts
variable {ι X Q : Type*} [TopologicalSpace X] [TopologicalSpace Q]
variable (Z : FiberBundleCore ι X Q)

variable [DiscreteTopology Q]

theorem covering : IsCoveringMap Z.proj := FiberBundle.isCoveringMap

end DiscreteCoverCharts

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiberCoreMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set

open Set Topology unitInterval

namespace CoveringCellGeometry
section
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)

abbrev Pullback (f : C(A,X)) := {z : A × E // p z.2 = f z.1}

variable (H : C(I × A,X))

def endpoint (t : I) : C(A,X) := H.comp ⟨fun a => (t,a),continuous_const.prodMk continuous_id⟩

def reverse : C(I × A,X) := H.comp ⟨fun z => (σ z.1,z.2),
  (unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd⟩

@[simp] theorem reverse_apply (t : I) (a : A) : reverse H (t,a) = H (σ t,a) := rfl

@[simp] theorem reverse_reverse : reverse (reverse H) = H := by
  ext ⟨t,a⟩
  simp [reverse,unitInterval.symm_symm]

def familyLift : C(I × Pullback (p := p) (endpoint H 0),E) :=
  cov.liftHomotopy
    (H.comp ⟨fun z => (z.1,z.2.1.1),continuous_fst.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))⟩)
    ⟨fun z => z.1.2,continuous_snd.comp continuous_subtype_val⟩
    (fun z => z.2.symm)

theorem familyLift_proj (t : I) (z : Pullback (p := p) (endpoint H 0)) :
    p (familyLift cov H (t,z)) = H (t,z.1.1) :=
  congr_fun (cov.liftHomotopy_lifts _ _ _) (t,z)

@[simp] theorem familyLift_zero (z : Pullback (p := p) (endpoint H 0)) :
    familyLift cov H (0,z) = z.1.2 := cov.liftHomotopy_zero _ _ _ z

def transport : C(Pullback (p := p) (endpoint H 0),Pullback (p := p) (endpoint H 1)) where
  toFun z := ⟨(z.1.1,familyLift cov H (1,z)),familyLift_proj cov H 1 z⟩
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((familyLift cov H).continuous.comp (continuous_const.prodMk continuous_id)) |>.subtype_mk _

def backLift : C(I × Pullback (p := p) (endpoint H 1),E) :=
  cov.liftHomotopy
    ((reverse H).comp ⟨fun z => (z.1,z.2.1.1),continuous_fst.prodMk
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))⟩)
    ⟨fun z => z.1.2,continuous_snd.comp continuous_subtype_val⟩
    (fun z => by
      change H (σ 0,z.1.1) = p z.1.2
      rw [unitInterval.symm_zero]
      exact z.2.symm)

theorem backLift_proj (t : I) (z : Pullback (p := p) (endpoint H 1)) :
    p (backLift cov H (t,z)) = H (σ t,z.1.1) :=
  congr_fun (cov.liftHomotopy_lifts _ _ _) (t,z)

@[simp] theorem backLift_zero (z : Pullback (p := p) (endpoint H 1)) :
    backLift cov H (0,z) = z.1.2 := cov.liftHomotopy_zero _ _ _ z

theorem backLift_one_proj (z : Pullback (p := p) (endpoint H 1)) :
    p (backLift cov H (1,z)) = endpoint H 0 z.1.1 := by
  exact (backLift_proj cov H 1 z).trans
    (congrArg (fun t => H (t,z.1.1)) unitInterval.symm_one)

def backTransport : C(Pullback (p := p) (endpoint H 1),Pullback (p := p) (endpoint H 0)) where
  toFun z := ⟨(z.1.1,backLift cov H (1,z)),backLift_one_proj cov H z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((backLift cov H).continuous.comp (continuous_const.prodMk continuous_id))

@[simp] theorem back_transport (z : Pullback (p := p) (endpoint H 0)) :
    backTransport cov H (transport cov H z) = z := by
  have heq : (fun t : I => backLift cov H (t,transport cov H z)) =
      (fun t : I => familyLift cov H (σ t,z)) := by
    refine cov.eq_of_comp_eq
      ((backLift cov H).continuous.comp (continuous_id.prodMk continuous_const))
      ((familyLift cov H).continuous.comp (unitInterval.continuous_symm.prodMk continuous_const)) ?_ 0 ?_
    · funext t
      simp only [Function.comp_apply,backLift_proj,familyLift_proj]
      rfl
    · simp [transport]
  apply Subtype.ext
  change (z.1.1,backLift cov H (1,transport cov H z)) = (z.1.1,z.1.2)
  apply Prod.ext
  · rfl
  · have hh := congr_fun heq 1
    simpa only [unitInterval.symm_one,familyLift_zero] using hh

@[simp] theorem transport_back (z : Pullback (p := p) (endpoint H 1)) :
    transport cov H (backTransport cov H z) = z := by
  have heq : (fun t : I => familyLift cov H (t,backTransport cov H z)) =
      (fun t : I => backLift cov H (σ t,z)) := by
    refine cov.eq_of_comp_eq
      ((familyLift cov H).continuous.comp (continuous_id.prodMk continuous_const))
      ((backLift cov H).continuous.comp (unitInterval.continuous_symm.prodMk continuous_const)) ?_ 0 ?_
    · funext t
      simp only [Function.comp_apply,backLift_proj,familyLift_proj,unitInterval.symm_symm]
      rfl
    · simp [backTransport]
  apply Subtype.ext
  change (z.1.1,familyLift cov H (1,backTransport cov H z)) = (z.1.1,z.1.2)
  apply Prod.ext
  · rfl
  · have hh := congr_fun heq 1
    simpa only [unitInterval.symm_one,backLift_zero] using hh

def transportHomeomorph : Pullback (p := p) (endpoint H 0) ≃ₜ
    Pullback (p := p) (endpoint H 1) where
  toFun := transport cov H
  invFun := backTransport cov H
  left_inv := back_transport cov H
  right_inv := transport_back cov H
  continuous_toFun := (transport cov H).continuous
  continuous_invFun := (backTransport cov H).continuous

@[simp] theorem transportHomeomorph_fst (z : Pullback (p := p) (endpoint H 0)) :
    (transportHomeomorph cov H z).1.1 = z.1.1 := rfl

end

section
open Set Topology unitInterval
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)

def pullbackCongr {f g : C(A,X)} (h : f = g) :
    Pullback (p := p) f ≃ₜ Pullback (p := p) g := by
  subst g
  exact Homeomorph.refl _

@[simp] theorem pullbackCongr_val {f g : C(A,X)} (h : f = g) (z : Pullback (p := p) f) :
    (pullbackCongr h z).1 = z.1 := by subst g; rfl

def constantPullback (x : X) : A × (p ⁻¹' {x}) ≃ₜ Pullback (p := p) (.const A x) where
  toFun z := ⟨(z.1,z.2.1),z.2.2⟩
  invFun z := (z.1.1,⟨z.1.2,z.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

variable [ContractibleSpace A]

def contractionPoint (A : Type*) [TopologicalSpace A] [ContractibleSpace A] : A :=
  (id_nullhomotopic A).choose

def contraction (A : Type*) [TopologicalSpace A] [ContractibleSpace A] :
    (ContinuousMap.const A (contractionPoint A)).Homotopy (ContinuousMap.id A) :=
  (id_nullhomotopic A).choose_spec.some.symm

variable (f : C(A,X))

def contractionImage : C(I × A,X) := f.comp (contraction A).toContinuousMap

@[simp] theorem contractionImage_zero : endpoint (contractionImage f) 0 =
    ContinuousMap.const A (f (contractionPoint A)) := by
  ext a
  exact congrArg f ((contraction A).apply_zero a)

@[simp] theorem contractionImage_one : endpoint (contractionImage f) 1 = f := by
  ext a
  exact congrArg f ((contraction A).apply_one a)

def pullbackTrivialization : A × (p ⁻¹' {f (contractionPoint A)}) ≃ₜ Pullback (p := p) f :=
  (constantPullback (p := p) (A := A) (f (contractionPoint A))).trans
    ((pullbackCongr (contractionImage_zero f).symm).trans
      ((transportHomeomorph cov (contractionImage f)).trans
        (pullbackCongr (contractionImage_one f))))

@[simp] theorem pullbackTrivialization_fst (z : A × (p ⁻¹' {f (contractionPoint A)})) :
    (pullbackTrivialization cov f z).1.1 = z.1 := by
  simp only [pullbackTrivialization,Homeomorph.trans_apply,pullbackCongr_val,transportHomeomorph_fst]
  rfl

@[simp] theorem pullbackTrivialization_symm_fst (z : Pullback (p := p) f) :
    ((pullbackTrivialization cov f).symm z).1 = z.1.1 := by
  have h := pullbackTrivialization_fst cov f ((pullbackTrivialization cov f).symm z)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

def characteristicLift (j : p ⁻¹' {f (contractionPoint A)}) : C(A,E) where
  toFun a := (pullbackTrivialization cov f (a,j)).1.2
  continuous_toFun := continuous_snd.comp (continuous_subtype_val.comp
    ((pullbackTrivialization cov f).continuous.comp (continuous_id.prodMk continuous_const)))

theorem characteristicLift_proj (j : p ⁻¹' {f (contractionPoint A)}) (a : A) :
    p (characteristicLift cov f j a) = f a := by
  exact (pullbackTrivialization cov f (a,j)).2.trans
    (congrArg f (pullbackTrivialization_fst cov f (a,j)))

def sheet : C(Pullback (p := p) f,p ⁻¹' {f (contractionPoint A)}) :=
  ⟨fun z => ((pullbackTrivialization cov f).symm z).2,
    continuous_snd.comp (pullbackTrivialization cov f).symm.continuous⟩

@[simp] theorem characteristicLift_sheet (z : Pullback (p := p) f) :
    characteristicLift cov f (sheet cov f z) z.1.1 = z.1.2 := by
  have hpair : (z.1.1,sheet cov f z) = (pullbackTrivialization cov f).symm z := by
    apply Prod.ext
    · exact (pullbackTrivialization_symm_fst cov f z).symm
    · rfl
  change (pullbackTrivialization cov f (z.1.1,sheet cov f z)).1.2 = z.1.2
  rw [hpair,Homeomorph.apply_symm_apply]

@[simp] theorem sheet_characteristicLift (j : p ⁻¹' {f (contractionPoint A)}) (a : A) :
    sheet cov f ⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩ = j := by
  have hpb : (⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩ :
      Pullback (p := p) f) = pullbackTrivialization cov f (a,j) := by
    apply Subtype.ext
    exact Prod.ext (pullbackTrivialization_fst cov f (a,j)).symm rfl
  change ((pullbackTrivialization cov f).symm _).2 = j
  rw [hpb,Homeomorph.symm_apply_apply]

theorem characteristicLift_fiber_injective (a : A) :
    Function.Injective (fun j => characteristicLift cov f j a) := by
  intro j k h
  have he : (⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩ :
      Pullback (p := p) f) =
      ⟨(a,characteristicLift cov f k a),characteristicLift_proj cov f k a⟩ := by
    apply Subtype.ext
    exact Prod.ext rfl h
  have hh := congrArg (sheet cov f) he
  simpa only [sheet_characteristicLift] using hh

end

open Set

end CoveringCellGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoveringCellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology unitInterval
namespace CoveringCellGeometry
open Set Topology
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)
  [ContractibleSpace A] [CompactSpace A] [T2Space X] (f : C(A,X))

theorem characteristicLift_isClosedMap :
    IsClosedMap (fun z : A × (p ⁻¹' {f (contractionPoint A)}) =>
      characteristicLift cov f z.2 z.1) := by
  have hc : IsClosed {z : A × E | p z.2 = f z.1} :=
    isClosed_eq (cov.continuous.comp continuous_snd) (f.continuous.comp continuous_fst)
  exact isClosedMap_snd_of_compactSpace.comp
    (hc.isClosedEmbedding_subtypeVal.isClosedMap.comp (pullbackTrivialization cov f).isClosedMap)

theorem finite_sheets_meeting {K : Set E} (hK : IsCompact K) :
    {j : p ⁻¹' {f (contractionPoint A)} |
      ∃ a : A, characteristicLift cov f j a ∈ K}.Finite := by
  let : DiscreteTopology (p ⁻¹' {f (contractionPoint A)}) :=
    (cov (f (contractionPoint A))).discreteTopology_fiber
  let T : Set (Pullback (p := p) f) := {z | z.1.2 ∈ K}
  have hc : IsClosed {z : A × E | p z.2 = f z.1} :=
    isClosed_eq (cov.continuous.comp continuous_snd) (f.continuous.comp continuous_fst)
  have hT : IsCompact T := by
    rw [Subtype.isCompact_iff]
    have he : Subtype.val '' T = (univ ×ˢ K) ∩ {z : A × E | p z.2 = f z.1} := by
      ext ⟨a,e⟩
      simp only [mem_image,mem_inter_iff,mem_prod,mem_univ,true_and,mem_ofPred_eq,T]
      constructor
      · rintro ⟨⟨⟨a',e'⟩,hp⟩,hz,he⟩
        cases he
        exact ⟨hz,hp⟩
      · rintro ⟨he,hp⟩
        exact ⟨⟨(a,e),hp⟩,he,rfl⟩
    rw [he]
    exact (isCompact_univ.prod hK).inter_right hc
  have he : {j : p ⁻¹' {f (contractionPoint A)} |
      ∃ a : A, characteristicLift cov f j a ∈ K} = sheet cov f '' T := by
    ext j
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩,
        ha,sheet_characteristicLift cov f j a⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.1.1,by simpa only [characteristicLift_sheet] using (show z.1.2 ∈ K from hz)⟩
  rw [he]
  exact (hT.image (sheet cov f).continuous).finite_of_discrete

theorem isClosed_discrete_slices {B J : Type*} [TopologicalSpace B]
    [TopologicalSpace J] [DiscreteTopology J] {S : Set (B × J)}
    (hS : ∀ j, IsClosed ((fun b : B => (b,j)) ⁻¹' S)) : IsClosed S := by
  rw [← isOpen_compl_iff]
  have he : Sᶜ = ⋃ j : J, ((fun b : B => (b,j)) ⁻¹' S)ᶜ ×ˢ {j} := by
    ext ⟨b,j⟩
    simp
  rw [he]
  exact isOpen_iUnion fun j => (hS j).isOpen_compl.prod (isOpen_discrete _)

end CoveringCellGeometry

namespace CoveringCW
section
open Set Topology Metric CoveringCellGeometry
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
  [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
instance disk_contractible (n : ℕ) : ContractibleSpace (Disk n) :=
  Metric.contractibleSpace_closedBall (by norm_num)

abbrev BaseCell (n : ℕ) := RelCWComplex.cell (univ : Set X) n

def baseChar (n : ℕ) (i : BaseCell (X := X) n) : C(Disk n,X) :=
  ⟨fun v => RelCWComplex.map n i v, continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)⟩

abbrev Fiber (n : ℕ) (i : BaseCell (X := X) n) :=
  p ⁻¹' {baseChar n i (contractionPoint (Disk n))}

abbrev Cell (n : ℕ) := Σ i : BaseCell (X := X) n, Fiber (p := p) n i

def characteristic (n : ℕ) (c : Cell (p := p) n) (v : Fin n → ℝ) : E := by
  classical
  exact if h : v ∈ closedBall 0 1 then characteristicLift cov (baseChar n c.1) c.2 ⟨v,h⟩ else c.2.1

end

open Set Topology Metric CoveringCellGeometry
universe u

end CoveringCW

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoveringCellGeometryHausdorff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Topology unitInterval
namespace CoveringCellGeometry
open Set Topology
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [T2Space X] {p : E → X}

theorem hausdorff (cov : IsCoveringMap p) : T2Space E := by
  constructor
  intro e f hef
  by_cases hp : p e = p f
  · exact cov.isSeparatedMap e f hp hef
  · obtain ⟨U,V,hU,hV,he,hf,hUV⟩ := t2_separation hp
    exact ⟨p ⁻¹' U,p ⁻¹' V,hU.preimage cov.continuous,hV.preimage cov.continuous,
      he,hf,hUV.preimage p⟩

end CoveringCellGeometry

end

namespace CoreDeck
open Set Topology DiscreteCoverCharts
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

def right (q : Q) (z : Z.TotalSpace) : Z.TotalSpace := ⟨z.1,@HMul.hMul Q Q Q _ z.2 q⟩

omit [DiscreteTopology Q] in
@[simp] lemma right_proj (q : Q) (z : Z.TotalSpace) : Z.proj (right Z q z) = Z.proj z := rfl

omit [DiscreteTopology Q] in
lemma of_potential (pot : ι → X → Q)
    (hpot : ∀ i j x a, Z.coordChange i j x a = pot j x * (pot i x)⁻¹ * a) :
    ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q := by
  intros; simp only [hpot,mul_assoc]

instance action : MulAction Qᵐᵒᵖ Z.TotalSpace where
  smul q z := right Z q.unop z
  one_smul z := by
    change right Z (1 : Q) z = z
    rcases z with ⟨x,a⟩
    change Q at a
    exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace)) (mul_one (a : Q))
  mul_smul p q z := by
    change right Z (q.unop*p.unop) z = right Z p.unop (right Z q.unop z)
    rcases z with ⟨x,a⟩
    change Q at a
    exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace))
      (mul_assoc (a : Q) q.unop p.unop).symm

omit [DiscreteTopology Q] in
lemma transitive_fiber (a b : Z.TotalSpace) (h : Z.proj a = Z.proj b) :
    ∃ q : Q, right Z q a = b := by
  rcases a with ⟨x,a⟩; rcases b with ⟨y,b⟩
  change x = y at h; subst y
  change Q at a b
  refine ⟨@HMul.hMul Q Q Q _ (@Inv.inv Q _ a) b,?_⟩
  exact congrArg (fun a : Q => (⟨x,a⟩ : Z.TotalSpace))
    (show (a : Q) * (a⁻¹ * b) = b by simp)

end CoreDeck

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularPrism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
namespace SingularPrism
open scoped Simplicial

variable {X Y Z : TopCat} {f g : X ⟶ Y}

open MonoidalCategory Functor.LaxMonoidal

lemma top_h_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X) :
    (H.comp (TopCat.Homotopy.refl p)).h = p ▷ TopCat.I ≫ H.h := by
  ext x
  rfl

lemma sset_h_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X) :
    (H.comp (TopCat.Homotopy.refl p)).toSSet.h =
      (TopCat.toSSet.map p) ▷ Δ[1] ≫ H.toSSet.h := by
  simp only [TopCat.Homotopy.toSSet,top_h_precomp,Functor.map_comp]
  rw [← Category.assoc (μ TopCat.toSSet _ _),← μ_natural_left]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]

theorem component_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X)
    {n : ℕ} (i : Fin (n+1)) :
    ((H.comp (TopCat.Homotopy.refl p)).toSSet.toSimplicialObjectHomotopy).h i =
      (TopCat.toSSet.map p).app _ ≫ H.toSSet.toSimplicialObjectHomotopy.h i := by
  ext x
  simp only [SSet.Homotopy.toSimplicialObjectHomotopy,sset_h_precomp,
    TypeCat.Fun.toFun_apply,types_comp_apply,TypeCat.hom_ofHom,TypeCat.Fun.coe_mk]
  rw [← SSet.yonedaEquiv_symm_comp]
  simp only [comp_whiskerRight,Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem prism_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X) (n : ℕ) :
    ((H.comp (TopCat.Homotopy.refl p)).singularChainComplexFunctorObjMap
      (ModuleCat.of ℤ ℤ)).hom n (n+1) =
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map p).f n ≫
        (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom n (n+1) := by
  change CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
    ((H.comp (TopCat.Homotopy.refl p)).toSSet.toSimplicialObjectHomotopy.whiskerRight
      (sigmaConst.obj (ModuleCat.of ℤ ℤ))) n (n+1) =
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map ((TopCat.toSSet.map p).app (Opposite.op ⦋n⦌)) ≫
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
        (H.toSSet.toSimplicialObjectHomotopy.whiskerRight
          (sigmaConst.obj (ModuleCat.of ℤ ℤ))) n (n+1)
  rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp only [Preadditive.comp_neg,Preadditive.comp_sum,Preadditive.comp_zsmul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map _ =
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map _ ≫ (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map _
  rw [← Functor.map_comp,component_precomp]

end SingularPrism

namespace SingularChains
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def start (F : C(I × X,Y)) : C(X,Y) :=
  F.comp ⟨fun x => (0,x),continuous_const.prodMk continuous_id⟩
def finish (F : C(I × X,Y)) : C(X,Y) :=
  F.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩

def cylinderHom (F : C(I × X,Y)) : ContinuousMap.Homotopy (start F) (finish F) where
  toContinuousMap := F
  map_zero_left _ := rfl
  map_one_left _ := rfl

def precompCylinder (F : C(I × X,Y)) (p : C(Z,X)) : C(I × Z,Y) :=
  F.comp ⟨fun z => (z.1,p z.2),continuous_fst.prodMk (p.continuous.comp continuous_snd)⟩

end SingularChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HurewiczInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval

namespace HurewiczConstruction
section
open SingularChains _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] {n : ℕ}

variable {G : Type} [Group G] [MulAction G X] [ContinuousConstSMul G X]

def actionMap (g : G) : C(X,X) := ⟨(g • ·),continuous_const_smul g⟩

@[simp] lemma actionMap_one : actionMap (X:=X) (1 : G) = ContinuousMap.id X := by ext x; simp [actionMap]
@[simp] lemma actionMap_mul (g h : G) :
    actionMap (X:=X) (g*h) = (actionMap g).comp (actionMap h) := by ext x; simp [actionMap,mul_smul]

end

open CategoryTheory.Limits SingularChains
end HurewiczConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
namespace SingularAction
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

def actionMap (g : G) : C(X,X) := ⟨(g • ·),continuous_const_smul g⟩

def val : C((univ : Set X),X) := ⟨Subtype.val,continuous_subtype_val⟩
def ofVal : C(X,(univ : Set X)) := ⟨fun x => ⟨x,mem_univ x⟩,continuous_id.subtype_mk _⟩

attribute [instance] AddCommGroup.toIntModule
end SingularAction

namespace CoveringCellGeometry
open Set Topology unitInterval
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)
variable (d : E ≃ₜ E) (hd : p ∘ d = p)

def deckPullback (f : C(A,X)) (z : Pullback (p := p) f) : Pullback (p := p) f :=
  ⟨(z.1.1,d z.1.2),(congrFun hd z.1.2).trans z.2⟩

theorem familyLift_deck (H : C(I × A,X)) (z : Pullback (p := p) (endpoint H 0)) (t : I) :
    familyLift cov H (t,deckPullback d hd (endpoint H 0) z) = d (familyLift cov H (t,z)) := by
  have he : (fun t : I => familyLift cov H (t,deckPullback d hd (endpoint H 0) z)) =
      (fun t : I => d (familyLift cov H (t,z))) := by
    apply cov.eq_of_comp_eq
      ((familyLift cov H).continuous.comp (continuous_id.prodMk continuous_const))
      (d.continuous.comp ((familyLift cov H).continuous.comp
        (continuous_id.prodMk continuous_const))) ?_ 0 ?_
    · funext t
      exact (familyLift_proj cov H t _).trans
        ((congrFun hd (familyLift cov H (t,z))).trans (familyLift_proj cov H t z)).symm
    · change familyLift cov H (0,deckPullback d hd (endpoint H 0) z) = d (familyLift cov H (0,z))
      rw [familyLift_zero,familyLift_zero]
      rfl
  exact congrFun he t

end CoveringCellGeometry

namespace EquivariantCoverCells
open Set Topology _root_.CategoryTheory
open CoveringCW
open scoped MonoidAlgebra
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
    [T2Space X] [T2Space E] [CWComplex (univ : Set X)]
    {G : Type u} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    {p : E → X} [hproj : Fact (∀ (g : G) x, p (g • x) = p x)]
    (hfree : ∀ (g h : G) (x : E), g • x = h • x → g = h)
    (htrans : ∀ (a b : E), p a = p b → ∃ g : G, g • a = b)
    (surj : Function.Surjective p)

def actionHomeo (g : G) : E ≃ₜ E where
  toFun := (g • ·)
  invFun := (g⁻¹ • ·)
  left_inv x := inv_smul_smul g x
  right_inv x := smul_inv_smul g x
  continuous_toFun := continuous_const_smul g
  continuous_invFun := continuous_const_smul g⁻¹

end EquivariantCoverCells

end

namespace EquivariantCoverCells
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CoveringCW

attribute [instance] AddCommGroup.toIntModule
end EquivariantCoverCells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoreDeck
open Set Topology DiscreteCoverCharts
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

@[instance_reducible] def leftAction : MulAction Q Z.TotalSpace where
  smul q z := right Z q⁻¹ z
  one_smul z := by
    change right Z ((1:Q)⁻¹) z = z
    obtain ⟨x, a⟩ := z
    simp only [right, inv_one]
    exact congrArg (fun v : Q => (⟨x, v⟩ : Z.TotalSpace)) (@mul_one Q _ a)
  mul_smul p q z := by
    change right Z ((p*q)⁻¹) z = right Z p⁻¹ (right Z q⁻¹ z)
    obtain ⟨x, a⟩ := z
    simp only [right, mul_inv_rev]
    exact congrArg (fun v : Q => (⟨x, v⟩ : Z.TotalSpace)) (@mul_assoc Q _ a q⁻¹ p⁻¹).symm

omit [DiscreteTopology Q] in
lemma left_transitive (a b : Z.TotalSpace) (h : Z.proj a = Z.proj b) :
    ∃ q : Q, @SMul.smul Q Z.TotalSpace (leftAction Z).toSMul q a = b := by
  obtain ⟨q,hq⟩ := transitive_fiber Z a b h
  refine ⟨q⁻¹,?_⟩
  change right Z ((q⁻¹)⁻¹) a = b
  simpa only [inv_inv] using hq

omit [DiscreteTopology Q] in
lemma left_free (g h : Q) (a : Z.TotalSpace)
    (he : @SMul.smul Q Z.TotalSpace (leftAction Z).toSMul g a =
      @SMul.smul Q Z.TotalSpace (leftAction Z).toSMul h a) : g = h := by
  have hh := congrArg (fun z : Z.TotalSpace => (z.2 : Q)) he
  change @HMul.hMul Q Q Q _ a.2 g⁻¹ = @HMul.hMul Q Q Q _ a.2 h⁻¹ at hh
  exact inv_injective (mul_left_cancel hh)

end CoreDeck

namespace CoreDeck
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [instance] AddCommGroup.toIntModule
end CoreDeck

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory

namespace ControlledChains

variable (G : Type) [Group G]

abbrev Simplex (n : ℕ) := Fin (n+1) → G
abbrev Chain (n : ℕ) := Simplex G n →₀ ℤ

def boundary (n : ℕ) : Chain G (n+1) →ₗ[ℤ] Chain G n :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap ∘ₗ
    Rep.standardComplex.d ℤ G (n+1) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap

omit [Group G] in
@[simp] lemma boundary_single (n : ℕ) (c : Simplex G (n+1)) (r : ℤ) :
    boundary G n (Finsupp.single c r) =
      ∑ p : Fin (n+2), Finsupp.single (c ∘ p.succAbove) (r * (-1 : ℤ) ^ p.val) :=
  by
    simp only [boundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    simpa using congrArg (MonoidAlgebra.coeffLinearEquiv ℤ)
      (Rep.standardComplex.d_single (k := ℤ) c r)

def mapChain {K : Type} (f : G → K) (n : ℕ) : Chain G n →ₗ[ℤ] Chain K n :=
  Finsupp.lmapDomain ℤ ℤ (fun c => f ∘ c)

omit [Group G] in
@[simp] lemma mapChain_single {K : Type} (f : G → K) (n : ℕ)
    (c : Simplex G n) (r : ℤ) :
    mapChain G f n (Finsupp.single c r) = Finsupp.single (f ∘ c) r := by
  simp [mapChain]

def cone (g : G) (n : ℕ) : Chain G n →ₗ[ℤ] Chain G (n+1) :=
  Finsupp.lmapDomain ℤ ℤ (fun c : Simplex G n => (Fin.cons g c : Simplex G (n+1)))

omit [Group G] in
@[simp] lemma cone_single (g : G) (n : ℕ) (q : Simplex G n) (r : ℤ) :
    cone G g n (Finsupp.single q r) = Finsupp.single (Fin.cons g q) r := by
  simp [cone]

omit [Group G] in
lemma boundary_cone (g : G) (n : ℕ) (c : Chain G (n+1)) :
    boundary G (n+1) (cone G g (n+1) c) + cone G g n (boundary G n c) = c := by
  have h : boundary G (n+1) ∘ₗ cone G g (n+1) +
      cone G g n ∘ₗ boundary G n = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro q r
    simp only [LinearMap.add_apply, LinearMap.comp_apply, cone_single,
      boundary_single, map_sum, LinearMap.id_apply]
    rw [Fin.sum_univ_succ]
    have hz : Fin.cons g q ∘ (0 : Fin (n+3)).succAbove = q := by
      ext i
      simp [Fin.succAbove_zero]
    rw [hz]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      Fin.cons_comp_succ_succAbove, pow_succ, mul_neg, Finsupp.single_neg]
    have hn : (∑ i : Fin (n+2), -Finsupp.single (Fin.cons g (i.removeNth q))
        (r * (-1 : ℤ) ^ i.val)) =
        -(∑ i : Fin (n+2), Finsupp.single (Fin.cons g (q ∘ i.succAbove) : Simplex G (n+1))
          (r * (-1 : ℤ) ^ i.val)) := by
      rw [← Finset.sum_neg_distrib]
      rfl
    rw [hn]
    abel
  exact LinearMap.congr_fun h c

def augmentation : Chain G 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : Simplex G 0 => (1 : ℤ))

omit [Group G] in
@[simp] lemma augmentation_single (q : Simplex G 0) (r : ℤ) :
    augmentation G (Finsupp.single q r) = r := by
  simp [augmentation]

omit [Group G] in
lemma boundary_cone_zero (g : G) (c : Chain G 0) :
    boundary G 0 (cone G g 0 c) =
      c - Finsupp.single (fun _ : Fin 1 => g) (augmentation G c) := by
  have h : boundary G 0 ∘ₗ cone G g 0 =
      LinearMap.id - Finsupp.lsingle (fun _ : Fin 1 => g) ∘ₗ augmentation G := by
    apply Finsupp.lhom_ext
    intro q r
    simp only [LinearMap.comp_apply, cone_single, boundary_single,
      LinearMap.sub_apply, LinearMap.id_apply, augmentation_single, Finsupp.lsingle_apply]
    rw [Fin.sum_univ_two]
    have h0 : Fin.cons g q ∘ (0 : Fin 2).succAbove = q := by ext i; simp
    have h1 : Fin.cons g q ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 => g) := by
      ext i
      fin_cases i
      rfl
    rw [h0, h1]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, mul_neg_one,
      Finsupp.single_neg, sub_eq_add_neg]
  exact LinearMap.congr_fun h c

end ControlledChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficientAffineShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory

open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct

namespace StandardVertex
open _root_.CategoryTheory _root_.Representation MonoidalCategory TensorProduct
variable {R G H : Type} [CommRing R] [Group G] [Group H]
variable (φ : G →* H) (v : G → H) (hv : ∀ g x, v (g*x) = φ g * v x)

def map (n : ℕ) : Rep.diagonal R G (n+1) ⟶
    Rep.res φ (Rep.diagonal R H (n+1)) :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s),by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s)
        ((Representation.ofMulAction R G (Fin (n+1) → G)) g (MonoidAlgebra.single s 1)) =
      ((Representation.ofMulAction R H (Fin (n+1) → H)) (φ g))
        (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s)
          (MonoidAlgebra.single s 1))
    simp only [Representation.ofMulAction_single,MonoidAlgebra.mapDomainLinearMap_single]
    congr 1
    ext i
    exact hv g (s i)⟩

@[simp] lemma map_single (n : ℕ) (s : Fin (n+1) → G) (r : R) :
    map φ v hv n (MonoidAlgebra.single s r) = MonoidAlgebra.single (v ∘ s) r := by
  exact MonoidAlgebra.mapDomainLinearMap_single _ _ _

lemma comm (n : ℕ) : map φ v hv (n+1) ≫
    (Rep.resFunctor φ).map ((Rep.standardComplex R H).d (n+1) n) =
      (Rep.standardComplex R G).d (n+1) n ≫ map φ v hv n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  change (((Rep.standardComplex R H).d (n+1) n).hom.toLinearMap).comp
      (map φ v hv (n+1)).hom.toLinearMap =
    (map φ v hv n).hom.toLinearMap.comp
      ((Rep.standardComplex R G).d (n+1) n).hom.toLinearMap
  rw [Rep.standardComplex.d_eq,Rep.standardComplex.d_eq]
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply,MonoidAlgebra.lsingle_apply]
  change Rep.standardComplex.d R H (n+1)
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+2) → G => v ∘ s)
        (MonoidAlgebra.single s 1)) =
    MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s)
      (Rep.standardComplex.d R G (n+1) (MonoidAlgebra.single s 1))
  simp only [MonoidAlgebra.mapDomainLinearMap_single,Rep.standardComplex.d_single,map_sum,
    Function.comp_assoc]

def chainMap : Rep.standardComplex R G ⟶
    ((Rep.resFunctor φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.standardComplex R H) :=
  HomologicalComplex.Hom.mk (map φ v hv) (by
    intro i j hij
    obtain rfl : j+1=i := hij
    exact comm φ v hv j)

end StandardVertex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardShapiro
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
namespace StandardShapiro
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G)

abbrev restrictedResolution : ProjectiveResolution (Rep.trivial R S R) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.standardResolution R G)

def inclusion : (Rep.standardResolution R S).complex ⟶ (restrictedResolution (R := R) S).complex :=
  StandardVertex.chainMap S.subtype S.subtype (by intro g x; rfl)

end StandardShapiro

namespace FunctionalTree
section

variable {R V M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def parentMap (p : V → V) : (V →₀ M) →ₗ[R] (V →₀ M) :=
  Finsupp.lmapDomain M R p

def boundary (p : V → V) : (V →₀ M) →ₗ[R] (V →₀ M) :=
  LinearMap.id - parentMap p

def augmentation : (V →₀ M) →ₗ[R] M :=
  Finsupp.lsum R (fun _ => LinearMap.id)

@[simp] lemma parentMap_single (p : V → V) (v : V) (a : M) :
    parentMap (R := R) p (Finsupp.single v a) = Finsupp.single (p v) a := by
  simp [parentMap]

@[simp] lemma augmentation_single (v : V) (a : M) :
    augmentation (R := R) (Finsupp.single v a) = a := by
  simp [augmentation]

lemma augmentation_parentMap (p : V → V) (a : V →₀ M) :
    augmentation (R := R) (parentMap (R := R) p a) = augmentation (R := R) a := by
  have h : (augmentation (R := R) (V := V) (M := M)).comp (parentMap p) = augmentation := by
    apply Finsupp.lhom_ext
    intro v a
    simp
  exact LinearMap.congr_fun h a

@[simp] lemma augmentation_boundary (p : V → V) (a : V →₀ M) :
    augmentation (R := R) (boundary (R := R) p a) = 0 := by
  simp [boundary,augmentation_parentMap]

end

open _root_.CategoryTheory
variable {R G V : Type*} [CommRing R] [Group G] [MulAction G V]
variable (A : Rep R G)

def diagonalAction (g : G) : (V →₀ A) →ₗ[R] (V →₀ A) :=
  Finsupp.lsum R (fun v => (Finsupp.lsingle (g • v)).comp (A.ρ g))

@[simp] lemma diagonalAction_single (g : G) (v : V) (a : A) :
    diagonalAction A g (Finsupp.single v a) = Finsupp.single (g • v) (A.ρ g a) := by
  simp [diagonalAction]

def diagonalRep : Rep R G := Rep.of {
  toFun := diagonalAction (V := V) A
  map_one' := by
    apply Finsupp.lhom_ext
    intro v a
    simp
  map_mul' := by
    intro g h
    apply Finsupp.lhom_ext
    intro v a
    simp [mul_smul] }

@[simp] lemma diagonalRep_single (g : G) (v : V) (a : A) :
    (diagonalRep (V := V) A).ρ g (Finsupp.single v a) =
      Finsupp.single (g • v) (A.ρ g a) := diagonalAction_single A g v a

variable (p : V → V) (peq : ∀ (g : G) (v : V), p (g • v) = g • p v)

def parentHom : diagonalRep (V := V) A ⟶ diagonalRep (V := V) A :=
  Rep.ofHom ⟨parentMap (R := R) p,by
    intro g
    apply Finsupp.lhom_ext
    intro v a
    simp [peq]⟩

def boundaryHom : diagonalRep (V := V) A ⟶ diagonalRep (V := V) A :=
  𝟙 _ - parentHom A p peq

@[simp] lemma boundaryHom_apply (z : V →₀ A) :
    boundaryHom A p peq z = boundary (R := R) p z := rfl

def augmentationHom : diagonalRep (V := V) A ⟶ A :=
  Rep.ofHom ⟨augmentation (R := R),by
    intro g
    apply Finsupp.lhom_ext
    intro v a
    simp⟩

@[simp] lemma augmentationHom_apply (z : V →₀ A) :
    augmentationHom A z = augmentation (R := R) z := rfl

end FunctionalTree

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CosetInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
namespace CosetInduction
open _root_.CategoryTheory _root_.Representation
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)

abbrev cosetRep := FunctionalTree.diagonalRep (V := G ⧸ S) A

lemma subgroup_fixes_base (s : S) :
    (s : G) • (QuotientGroup.mk (1 : G) : G ⧸ S) = QuotientGroup.mk (1 : G) := by
  simp only [MulAction.Quotient.smul_mk,smul_eq_mul,mul_one]
  exact QuotientGroup.eq.mpr (by simp)

def baseHom : Rep.res S.subtype A ⟶ Rep.res S.subtype (cosetRep S A) :=
  Rep.ofHom ⟨Finsupp.lsingle (QuotientGroup.mk (1 : G)),by
    intro s
    apply LinearMap.ext
    intro a
    change Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ s a) =
      (cosetRep S A).ρ s (Finsupp.single (QuotientGroup.mk (1 : G)) a)
    rw [FunctionalTree.diagonalRep_single,subgroup_fixes_base]⟩

def indToCosets : Rep.ind S.subtype (Rep.res S.subtype A) ⟶ cosetRep S A :=
  (Rep.indResHomEquiv S.subtype (Rep.res S.subtype A) (cosetRep S A)).symm (baseHom S A)

lemma indToCosets_mk (h : G) (a : A) :
    indToCosets S A (IndV.mk S.subtype (Rep.res S.subtype A).ρ h a) =
      Finsupp.single (QuotientGroup.mk h⁻¹) (A.ρ h⁻¹ a) := by
  simp [indToCosets,Rep.indResHomEquiv,baseHom]
  change (cosetRep S A).ρ h⁻¹ (Finsupp.single (QuotientGroup.mk (1 : G)) a) = _
  rw [FunctionalTree.diagonalRep_single]
  simp
  rfl

lemma ind_mk_left (s : S) (h : G) (a : A) :
    IndV.mk S.subtype (Rep.res S.subtype A).ρ ((s : G)*h) (A.ρ s a) =
      IndV.mk S.subtype (Rep.res S.subtype A).ρ h a := by
  have H := Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular R G).comp S.subtype) (Rep.res S.subtype A).ρ)
    s (MonoidAlgebra.single h (1 : R) ⊗ₜ[R] a)
  simpa using H

def cosetSection : (G ⧸ S) → A →ₗ[R] Representation.IndV S.subtype (Rep.res S.subtype A).ρ :=
  Quotient.lift (fun h => (IndV.mk S.subtype (Rep.res S.subtype A).ρ h⁻¹).comp (A.ρ h⁻¹)) (by
    intro h k hrel
    let s : S := ⟨h⁻¹*k,QuotientGroup.leftRel_apply.mp hrel⟩
    have hk : k = h*(s : G) := by change k = h*(h⁻¹*k); group
    apply LinearMap.ext
    intro a
    change IndV.mk S.subtype (Rep.res S.subtype A).ρ h⁻¹ (A.ρ h⁻¹ a) =
      IndV.mk S.subtype (Rep.res S.subtype A).ρ k⁻¹ (A.ρ k⁻¹ a)
    rw [hk,mul_inv_rev,map_mul,Module.End.mul_apply]
    exact (ind_mk_left S A s⁻¹ h⁻¹ (A.ρ h⁻¹ a)).symm)

@[simp] lemma cosetSection_mk (h : G) (a : A) :
    cosetSection S A (QuotientGroup.mk h) a =
      IndV.mk S.subtype (Rep.res S.subtype A).ρ h⁻¹ (A.ρ h⁻¹ a) := rfl

def cosetsToInd : ((G ⧸ S) →₀ A) →ₗ[R] Representation.IndV S.subtype (Rep.res S.subtype A).ρ :=
  Finsupp.lsum R (cosetSection S A)

@[simp] lemma cosetsToInd_single (v : G ⧸ S) (a : A) :
    cosetsToInd S A (Finsupp.single v a) = cosetSection S A v a := by
  simp [cosetsToInd]

lemma cosetsToInd_indToCosets :
    (cosetsToInd S A).comp (indToCosets S A).hom.toLinearMap = LinearMap.id := by
  apply IndV.hom_ext
  intro h
  apply LinearMap.ext
  intro a
  change cosetsToInd S A (indToCosets S A (IndV.mk S.subtype (Rep.res S.subtype A).ρ h a)) =
    IndV.mk S.subtype (Rep.res S.subtype A).ρ h a
  rw [indToCosets_mk,cosetsToInd_single,cosetSection_mk,inv_inv]
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
  rfl

lemma indToCosets_cosetsToInd :
    (indToCosets S A).hom.toLinearMap.comp (cosetsToInd S A) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro v a
  induction v using Quotient.inductionOn with
  | h h =>
    change indToCosets S A (cosetsToInd S A (Finsupp.single (QuotientGroup.mk h) a)) =
      Finsupp.single (QuotientGroup.mk h) a
    rw [cosetsToInd_single,cosetSection_mk,indToCosets_mk,inv_inv]
    rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one]
    rfl

end CosetInduction

open _root_.CategoryTheory CategoryTheory.Limits
namespace ExactTargetHomotopy
variable {C : Type*} [Category* C] [Abelian C]
  {P Q : ChainComplex C ℕ} [∀ n, Projective (P.X n)] {Z : C}
variable (ε : Q.X 0 ⟶ Z) (hε : Q.d 1 0 ≫ ε = 0)
  (h0 : (ShortComplex.mk (Q.d 1 0) ε hε).Exact)
  (hs : ∀ n, (ShortComplex.mk (Q.d (n+2) (n+1)) (Q.d (n+1) n)
    (Q.d_comp_d (n+2) (n+1) n)).Exact)
variable (f : P ⟶ Q) (comm : f.f 0 ≫ ε = 0)

def stepZero : P.X 0 ⟶ Q.X 1 := h0.liftFromProjective (f.f 0) comm

@[reassoc (attr := simp)]
lemma stepZero_comp : stepZero ε hε h0 f comm ≫ Q.d 1 0 = f.f 0 :=
  h0.liftFromProjective_comp _ _

def stepOne : P.X 1 ⟶ Q.X 2 :=
  (hs 0).liftFromProjective (f.f 1 - P.d 1 0 ≫ stepZero ε hε h0 f comm)
    (by rw [Preadditive.sub_comp, Category.assoc, HomologicalComplex.Hom.comm,
      stepZero_comp, sub_self])

@[reassoc (attr := simp)]
lemma stepOne_comp : stepOne ε hε h0 hs f comm ≫ Q.d 2 1 =
    f.f 1 - P.d 1 0 ≫ stepZero ε hε h0 f comm :=
  (hs 0).liftFromProjective_comp _ _

omit h0 comm in
def stepSucc (n : ℕ) (g : P.X n ⟶ Q.X (n+1))
    (g' : P.X (n+1) ⟶ Q.X (n+2))
    (w : f.f (n+1) = P.d (n+1) n ≫ g + g' ≫ Q.d (n+2) (n+1)) :
    P.X (n+2) ⟶ Q.X (n+3) :=
  (hs (n+1)).liftFromProjective (f.f (n+2) - P.d (n+2) (n+1) ≫ g') (by simp [w])

omit h0 comm in
@[reassoc (attr := simp)]
lemma stepSucc_comp (n : ℕ) (g : P.X n ⟶ Q.X (n+1))
    (g' : P.X (n+1) ⟶ Q.X (n+2))
    (w : f.f (n+1) = P.d (n+1) n ≫ g + g' ≫ Q.d (n+2) (n+1)) :
    stepSucc hs f n g g' w ≫ Q.d (n+3) (n+2) = f.f (n+2) - P.d (n+2) (n+1) ≫ g' :=
  (hs (n+1)).liftFromProjective_comp _ _

def nullHomotopy : Homotopy f 0 :=
  Homotopy.mkInductive _ (stepZero ε hε h0 f comm) (by simp)
    (stepOne ε hε h0 hs f comm) (by simp)
    fun n ⟨g,g',w⟩ => ⟨stepSucc hs f n g g' w,by simp⟩

omit comm in
def comparison (g : P ⟶ Q) (hg : f.f 0 ≫ ε = g.f 0 ≫ ε) : Homotopy f g :=
  Homotopy.equivSubZero.invFun (nullHomotopy ε hε h0 hs (f-g) (by
    change (f.f 0 - g.f 0) ≫ ε = 0
    rw [Preadditive.sub_comp,hg,sub_self]))

end ExactTargetHomotopy

namespace StandardVertex
open _root_.CategoryTheory
variable {R G H : Type} [CommRing R] [Group G] [Group H]
variable (φ : G →* H) (v : G → H) (hv : ∀ g x, v (g*x) = φ g * v x)
variable (w : G → H) (hw : ∀ g x, w (g*x) = φ g * w x)

lemma augmentation_eq :
    map φ v hv 0 ≫ (Rep.resFunctor φ).map ((Rep.standardResolution R H).π.f 0) =
      map φ w hw 0 ≫ (Rep.resFunctor φ).map ((Rep.standardResolution R H).π.f 0) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change (Rep.standardComplex.ε R H).hom
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin 1 → G => v ∘ s)
        (MonoidAlgebra.single s 1)) =
    (Rep.standardComplex.ε R H).hom
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin 1 → G => w ∘ s)
        (MonoidAlgebra.single s 1))
  simp [Rep.standardComplex.ε]

def homotopy : Homotopy (chainMap (R := R) φ v hv) (chainMap φ w hw) := by
  let F := Rep.resFunctor (k := R) φ
  let P := Rep.standardResolution R H
  apply ExactTargetHomotopy.comparison (F.map (P.π.f 0))
    (by
      change F.map (P.complex.d 1 0) ≫ F.map (P.π.f 0) = 0
      rw [← F.map_comp,P.complex_d_comp_π_f_zero,F.map_zero])
    (P.exact₀.map F)
    (fun n => (P.exact_succ n).map F)
  exact augmentation_eq φ v hv w hw

end StandardVertex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SemilinearCoinvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
namespace SemilinearCoinvariants
variable {R G H : Type} [CommRing R] [Group G] [Group H]
variable (φ : G →* H) {A : Rep R G} {B : Rep R H}

def tensorNatTrans (α : A ⟶ Rep.res φ B) :
    Rep.resFunctor φ ⋙ (Rep.coinvariantsTensor R G).obj A ⟶
      (Rep.coinvariantsTensor R H).obj B :=
  (Rep.coinvariantsTensorIndNatIso φ A).inv ≫
    (Rep.coinvariantsTensor R H).map ((Rep.indResHomEquiv φ A B).symm α)

variable (P : ChainComplex (Rep R G) ℕ) (Q : ChainComplex (Rep R H) ℕ)

def chainMap (α : A ⟶ Rep.res φ B)
    (β : P ⟶ ((Rep.resFunctor φ).mapHomologicalComplex _).obj Q) :
    P.coinvariantsTensorObj A ⟶ Q.coinvariantsTensorObj B :=
  (((Rep.coinvariantsTensor R G).obj A).mapHomologicalComplex _).map β ≫
    (NatTrans.mapHomologicalComplex (tensorNatTrans φ α) _).app Q

def chainMapHomotopy (α : A ⟶ Rep.res φ B)
    {β γ : P ⟶ ((Rep.resFunctor φ).mapHomologicalComplex _).obj Q} (h : Homotopy β γ) :
    Homotopy (chainMap φ P Q α β) (chainMap φ P Q α γ) :=
  ((((Rep.coinvariantsTensor R G).obj A).mapHomotopy h).compRight
    ((NatTrans.mapHomologicalComplex (tensorNatTrans φ α) _).app Q))

end SemilinearCoinvariants

namespace CosetEndpoint
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (A : Rep R G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t = t*(f s : G))

include ht in
lemma inv_mul_subtype (s : S) : t⁻¹*(s : G) = (f s : G)*t⁻¹ := by
  have h := congrArg (fun x : G => t⁻¹*x*t⁻¹) (ht s)
  simpa only [mul_assoc,mul_inv_cancel,mul_one,inv_mul_cancel_left] using h

def shiftCoeff : Rep.res S.subtype A ⟶ Rep.res f (Rep.res S.subtype A) :=
  Rep.ofHom ⟨A.ρ t⁻¹,by
    intro s
    change (A.ρ t⁻¹).comp (A.ρ s) = (A.ρ (f s)).comp (A.ρ t⁻¹)
    change A.ρ t⁻¹ * A.ρ s = A.ρ (f s) * A.ρ t⁻¹
    rw [← map_mul,← map_mul,inv_mul_subtype S f t ht]⟩

def baseShiftCoeff : Rep.res S.subtype A ⟶
    Rep.res (S.subtype.comp f) (CosetInduction.cosetRep S A) :=
  shiftCoeff S A f t ht ≫ (Rep.resFunctor f).map (CosetInduction.baseHom S A)

@[simp] lemma baseShiftCoeff_apply (a : A) :
    baseShiftCoeff S A f t ht a =
      Finsupp.single (QuotientGroup.mk (1 : G)) (A.ρ t⁻¹ a) := rfl

include ht in
lemma leftVertex_equivariant (s u : S) :
    t⁻¹*((s*u : S) : G) = (S.subtype.comp f) s * (t⁻¹*(u : G)) := by
  change t⁻¹*((s : G)*(u : G)) = _
  rw [← mul_assoc, inv_mul_subtype S f t ht, mul_assoc]
  rfl

def leftVertexMap := StandardVertex.chainMap (R := R) (S.subtype.comp f)
  (fun s : S => t⁻¹*(s : G)) (leftVertex_equivariant S f t ht)

def rightVertexMap := StandardVertex.chainMap (R := R) (S.subtype.comp f)
  (S.subtype.comp f) (by intro s u; exact (S.subtype.comp f).map_mul s u)

def leftChain := SemilinearCoinvariants.chainMap (S.subtype.comp f)
  (Rep.standardComplex R S) (Rep.standardComplex R G)
  (baseShiftCoeff S A f t ht) (leftVertexMap (R := R) S f t ht)

def rightChain := SemilinearCoinvariants.chainMap (S.subtype.comp f)
  (Rep.standardComplex R S) (Rep.standardComplex R G)
  (baseShiftCoeff S A f t ht) (rightVertexMap (R := R) S f)

def endpointHomotopy : Homotopy (leftChain S A f t ht) (rightChain S A f t ht) :=
  SemilinearCoinvariants.chainMapHomotopy (S.subtype.comp f) _ _
    (baseShiftCoeff S A f t ht)
    (StandardVertex.homotopy (S.subtype.comp f) _ (leftVertex_equivariant S f t ht)
      _ (by intro s u; exact (S.subtype.comp f).map_mul s u))

end CosetEndpoint

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CosetCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits
namespace CosetCoordinates
variable {G : Type*} [Group G] (S : Subgroup G)

def equiv : G ≃ (G ⧸ S) × S where
  toFun g := (QuotientGroup.mk g,
    ⟨(Quotient.out (QuotientGroup.mk g : G ⧸ S))⁻¹*g,
      QuotientGroup.eq.mp (Quotient.out_eq' (QuotientGroup.mk g : G ⧸ S))⟩)
  invFun v := v.1.out*(v.2 : G)
  left_inv g := by simp
  right_inv v := by
    rcases v with ⟨c,s⟩
    have h : (QuotientGroup.mk (c.out*(s : G)) : G ⧸ S) = c :=
      (QuotientGroup.mk_mul_of_mem c.out s.property).trans (Quotient.out_eq' c)
    apply Prod.ext
    · exact h
    · apply Subtype.ext
      change (Quotient.out (QuotientGroup.mk (c.out*(s : G)) : G ⧸ S))⁻¹ *
        (c.out*(s : G)) = (s : G)
      rw [h,inv_mul_cancel_left]

@[simp] lemma equiv_fst (g : G) : (equiv S g).1 = QuotientGroup.mk g := rfl
@[simp] lemma equiv_snd (g : G) : ((equiv S g).2 : G) =
    (Quotient.out (QuotientGroup.mk g : G ⧸ S))⁻¹*g := rfl
@[simp] lemma equiv_symm_apply (c : G ⧸ S) (s : S) :
    (equiv S).symm (c,s) = c.out*(s : G) := rfl

lemma equiv_mul_subgroup (g : G) (s : S) :
    equiv S (g*(s : G)) = ((equiv S g).1, (equiv S g).2*s) := by
  have h := QuotientGroup.mk_mul_of_mem g s.property
  apply Prod.ext
  · exact h
  · apply Subtype.ext
    change (Quotient.out (QuotientGroup.mk (g*(s : G)) : G ⧸ S))⁻¹*(g*(s : G)) =
      ((Quotient.out (QuotientGroup.mk g : G ⧸ S))⁻¹*g)*(s : G)
    rw [h,mul_assoc]

variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))

def nextCoset (c : G ⧸ S) : G ⧸ S := QuotientGroup.mk (c.out*t)
def correction (c : G ⧸ S) : S := (equiv S (c.out*t)).2

end CosetCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_Steinberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
variable {n R S : Type*} [Ring R] [Ring S]

def orthogonalSum (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0) : R →ₙ+* S where
  toFun a := φ a + ψ a
  map_zero' := by simp
  map_add' a b := by simp [add_comm, add_left_comm]
  map_mul' a b := by simp [map_mul, mul_add, add_mul, hφψ, hψφ]

@[simp] lemma orthogonalSum_apply (φ ψ : R →ₙ+* S) (hφψ hψφ) (a : R) :
    orthogonalSum φ ψ hφψ hψφ a = φ a + ψ a := rfl

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
section

variable (G : Type*)

abbrev Simplex := G × List G

end

end OrderListChains

end

end OAI
end


