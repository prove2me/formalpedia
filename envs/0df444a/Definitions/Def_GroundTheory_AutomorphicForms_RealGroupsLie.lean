-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
-- name    : GroundTheory_AutomorphicForms_RealGroupsLie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:44.848727+00:00
-- url     : https://prove2.me/theorems/985a4db0-4a5b-4396-80c9-e7164183045a
-- title:
--   Real Groups Lie
-- statement:
--   Definitions and structural lemmas for Real Groups Lie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
section ExpChart
variable (𝕂 : Type*) [RCLike 𝕂] (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
theorem contDiff_exp {n : WithTop ℕ∞} : ContDiff 𝕂 n (exp : 𝔸 → 𝔸) :=
  contDiff_iff_contDiffAt.2 fun x => (exp_analytic (𝕂 := 𝕂) x).contDiffAt
variable {𝔸} in
include 𝕂 in

theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := 𝕂) h
    (by rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)
    (by rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)
def expRegularSet : Set 𝔸 := {X | IsUnit (fderiv 𝕂 (exp : 𝔸 → 𝔸) X)}
theorem isOpen_expRegularSet : IsOpen (expRegularSet 𝕂 𝔸) :=
  Units.isOpen.preimage ((contDiff_exp 𝕂 𝔸 (n := 1)).continuous_fderiv one_ne_zero)
theorem zero_mem_expRegularSet : (0 : 𝔸) ∈ expRegularSet 𝕂 𝔸 := by
  simp [expRegularSet, (hasFDerivAt_exp_zero (𝕂 := 𝕂) (𝔸 := 𝔸)).fderiv]
theorem hasStrictFDerivAt_exp_zero_equiv :
    HasStrictFDerivAt (exp : 𝔸 → 𝔸) ((ContinuousLinearEquiv.refl 𝕂 𝔸 : 𝔸 →L[𝕂] 𝔸)) 0 := by
  convert (hasStrictFDerivAt_exp_zero (𝕂 := 𝕂) (𝔸 := 𝔸)) using 1
  exact ContinuousLinearMap.ext fun _ => rfl
noncomputable def expPartialHomeomorph : OpenPartialHomeomorph 𝔸 𝔸 :=
  ((hasStrictFDerivAt_exp_zero_equiv 𝕂 𝔸).toOpenPartialHomeomorph exp).restrOpen
    (expRegularSet 𝕂 𝔸) (isOpen_expRegularSet 𝕂 𝔸)
theorem coe_expPartialHomeomorph : ⇑(expPartialHomeomorph 𝕂 𝔸) = exp := rfl
theorem zero_mem_expPartialHomeomorph_source : (0 : 𝔸) ∈ (expPartialHomeomorph 𝕂 𝔸).source :=
  ⟨(hasStrictFDerivAt_exp_zero_equiv 𝕂 𝔸).mem_toOpenPartialHomeomorph_source,
    zero_mem_expRegularSet 𝕂 𝔸⟩
theorem one_mem_expPartialHomeomorph_target : (1 : 𝔸) ∈ (expPartialHomeomorph 𝕂 𝔸).target := by
  simpa [coe_expPartialHomeomorph] using
    (expPartialHomeomorph 𝕂 𝔸).map_source (zero_mem_expPartialHomeomorph_source 𝕂 𝔸)
theorem expPartialHomeomorph_source_subset :
    (expPartialHomeomorph 𝕂 𝔸).source ⊆ expRegularSet 𝕂 𝔸 := fun _ h => h.2
theorem contDiffOn_expPartialHomeomorph_symm {n : WithTop ℕ∞} :
    ContDiffOn 𝕂 n (expPartialHomeomorph 𝕂 𝔸).symm (expPartialHomeomorph 𝕂 𝔸).target := by
  intro y hy
  set e := expPartialHomeomorph 𝕂 𝔸
  have hs : e.symm y ∈ e.source := e.map_target hy
  have hu : IsUnit (fderiv 𝕂 (exp : 𝔸 → 𝔸) (e.symm y)) :=
    expPartialHomeomorph_source_subset 𝕂 𝔸 hs
  refine (e.contDiffAt_symm (f₀' := ContinuousLinearEquiv.unitsEquiv 𝕂 𝔸 hu.unit) hy ?_
    ?_).contDiffWithinAt
  · have h1 : ((ContinuousLinearEquiv.unitsEquiv 𝕂 𝔸 hu.unit : 𝔸 ≃L[𝕂] 𝔸) : 𝔸 →L[𝕂] 𝔸) =
        fderiv 𝕂 (exp : 𝔸 → 𝔸) (e.symm y) := by
      ext x; simp
    rw [h1]
    exact ((contDiff_exp 𝕂 𝔸 (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  · exact (contDiff_exp 𝕂 𝔸).contDiffAt
include 𝕂 in

noncomputable def expUnit (X : 𝔸) : 𝔸ˣ :=
  ⟨exp X, exp (-X), by
    rw [← exp_add_of_commute' 𝕂 (Commute.neg_right (Commute.refl X)), add_neg_cancel, exp_zero],
   by rw [← exp_add_of_commute' 𝕂 (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]⟩
@[simp] theorem coe_expUnit (X : 𝔸) : (expUnit 𝕂 𝔸 X : 𝔸) = exp X := rfl
@[simp] theorem coe_expUnit_inv (X : 𝔸) : ((expUnit 𝕂 𝔸 X)⁻¹ : 𝔸ˣ) = exp (-X) := rfl
theorem continuous_expUnit : Continuous (expUnit 𝕂 𝔸) :=
  Units.continuous_iff.2 ⟨(contDiff_exp 𝕂 𝔸 (n := 0)).continuous,
    (contDiff_exp 𝕂 𝔸 (n := 0)).continuous.comp continuous_neg⟩
end ExpChart
section UnitsChart
variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
local notation "𝔢" => expPartialHomeomorph 𝕂 𝔸
noncomputable def expChartUnits (g : 𝔸ˣ) : OpenPartialHomeomorph 𝔸ˣ 𝔸 where
  toFun x := (𝔢).symm ((g⁻¹ * x : 𝔸ˣ) : 𝔸)
  invFun X := g * expUnit 𝕂 𝔸 X
  source := {x | ((g⁻¹ * x : 𝔸ˣ) : 𝔸) ∈ (𝔢).target}
  target := (𝔢).source
  map_source' x hx := (𝔢).map_target hx
  map_target' X hX := by
    simp only [mem_ofPred_eq, inv_mul_cancel_left, coe_expUnit]
    exact (𝔢).map_source hX
  left_inv' x hx := by
    have h2 : exp ((𝔢).symm ((g⁻¹ * x : 𝔸ˣ) : 𝔸)) = ((g⁻¹ * x : 𝔸ˣ) : 𝔸) := (𝔢).right_inv hx
    apply Units.ext
    show (g : 𝔸) * exp ((𝔢).symm ((g⁻¹ * x : 𝔸ˣ) : 𝔸)) = x
    rw [h2, ← Units.val_mul, mul_inv_cancel_left]
  right_inv' X hX := by
    simp only [inv_mul_cancel_left, coe_expUnit]
    exact (𝔢).left_inv hX
  open_source := (𝔢).open_target.preimage (Units.continuous_val.comp (continuous_const.mul continuous_id))
  open_target := (𝔢).open_source
  continuousOn_toFun := (𝔢).continuousOn_symm.comp
    (Units.continuous_val.comp (continuous_const.mul continuous_id)).continuousOn (fun _ hx => hx)
  continuousOn_invFun := (continuous_const.mul (continuous_expUnit 𝕂 𝔸)).continuousOn
end UnitsChart
section GeneralLinear
open scoped Matrix.Norms.L2Operator
end GeneralLinear
section LinearLie
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
noncomputable def subspaceProj (𝔤 : Submodule ℝ 𝔸) : 𝔸 →L[ℝ] 𝔤 :=
  LinearMap.toContinuousLinearMap
    (Submodule.projectionOnto 𝔤 _ (Submodule.exists_isCompl 𝔤).choose_spec)
@[simp] theorem subspaceProj_coe (𝔤 : Submodule ℝ 𝔸) (X : 𝔤) : subspaceProj 𝔤 (X : 𝔸) = X :=
  Submodule.projectionOnto_apply_left _ X
theorem subspaceProj_of_mem {𝔤 : Submodule ℝ 𝔸} {X : 𝔸} (hX : X ∈ 𝔤) :
    (subspaceProj 𝔤 X : 𝔸) = X := by
  simpa using congrArg Subtype.val (subspaceProj_coe 𝔤 ⟨X, hX⟩)
structure IsExpLieAlgebra (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) : Prop where
  expUnit_mem : ∀ X ∈ 𝔤, expUnit ℝ 𝔸 X ∈ G
  exists_nhds : ∃ U : Set 𝔸, IsOpen U ∧ (0 : 𝔸) ∈ U ∧
    U ⊆ (expPartialHomeomorph ℝ 𝔸).source ∧ ∀ X ∈ U, expUnit ℝ 𝔸 X ∈ G → X ∈ 𝔤
theorem continuous_val_val (G : Subgroup 𝔸ˣ) : Continuous (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
  Units.continuous_val.comp continuous_subtype_val
namespace IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
local notation "𝔢" => expPartialHomeomorph ℝ 𝔸
def nhd : Set 𝔸 := h.exists_nhds.choose
theorem isOpen_nhd : IsOpen h.nhd := h.exists_nhds.choose_spec.1
theorem zero_mem_nhd : (0 : 𝔸) ∈ h.nhd := h.exists_nhds.choose_spec.2.1
theorem nhd_subset : h.nhd ⊆ (𝔢).source := h.exists_nhds.choose_spec.2.2.1
theorem mem_of_mem_nhd {X : 𝔸} (hX : X ∈ h.nhd) (hG : expUnit ℝ 𝔸 X ∈ G) : X ∈ 𝔤 :=
  h.exists_nhds.choose_spec.2.2.2 X hX hG
def nhdOne : Set 𝔸 := 𝔢 '' h.nhd
theorem isOpen_nhdOne : IsOpen h.nhdOne := (𝔢).isOpen_image_of_subset_source h.isOpen_nhd h.nhd_subset
theorem nhdOne_subset_target : h.nhdOne ⊆ (𝔢).target := by
  rintro _ ⟨X, hX, rfl⟩; exact (𝔢).map_source (h.nhd_subset hX)
theorem symm_mem_nhd {a : 𝔸} (ha : a ∈ h.nhdOne) : (𝔢).symm a ∈ h.nhd := by
  obtain ⟨X, hX, rfl⟩ := ha; rwa [(𝔢).left_inv (h.nhd_subset hX)]
theorem exp_symm {a : 𝔸} (ha : a ∈ h.nhdOne) : exp ((𝔢).symm a) = a :=
  (𝔢).right_inv (h.nhdOne_subset_target ha)
theorem exp_mem_nhdOne {X : 𝔸} (hX : X ∈ h.nhd) : exp X ∈ h.nhdOne := ⟨X, hX, rfl⟩
theorem symm_exp {X : 𝔸} (hX : X ∈ h.nhd) : (𝔢).symm (exp X) = X := (𝔢).left_inv (h.nhd_subset hX)
theorem one_mem_nhdOne : (1 : 𝔸) ∈ h.nhdOne := by
  simpa [exp_zero] using h.exp_mem_nhdOne h.zero_mem_nhd
noncomputable def expG (X : 𝔤) : G := ⟨expUnit ℝ 𝔸 X, h.expUnit_mem X X.2⟩
@[simp] theorem coe_expG (X : 𝔤) : ((h.expG X : 𝔸ˣ) : 𝔸) = exp (X : 𝔸) := rfl
theorem continuous_expG : Continuous h.expG :=
  ((continuous_expUnit ℝ 𝔸).comp continuous_subtype_val).subtype_mk _
theorem symm_mem_lie {x : G} (hx : ((x : 𝔸ˣ) : 𝔸) ∈ h.nhdOne) : (𝔢).symm ((x : 𝔸ˣ) : 𝔸) ∈ 𝔤 := by
  apply h.mem_of_mem_nhd (h.symm_mem_nhd hx)
  have : expUnit ℝ 𝔸 ((𝔢).symm ((x : 𝔸ˣ) : 𝔸)) = (x : 𝔸ˣ) := Units.ext (h.exp_symm hx)
  rw [this]; exact x.2
noncomputable def chart (g : G) : OpenPartialHomeomorph G 𝔤 where
  toFun x := subspaceProj 𝔤 ((𝔢).symm (((g⁻¹ * x : G) : 𝔸ˣ) : 𝔸))
  invFun X := g * h.expG X
  source := {x | (((g⁻¹ * x : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne}
  target := {X | (X : 𝔸) ∈ h.nhd}
  map_source' x hx := by
    simp only [mem_ofPred_eq] at hx ⊢
    rw [subspaceProj_of_mem (h.symm_mem_lie hx)]
    exact h.symm_mem_nhd hx
  map_target' X hX := by
    simp only [mem_ofPred_eq, inv_mul_cancel_left] at hX ⊢
    exact h.exp_mem_nhdOne hX
  left_inv' x hx := by
    have e1 := subspaceProj_of_mem (h.symm_mem_lie hx)
    have e2 := h.exp_symm hx
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_expG, Subgroup.coe_inv] at e1 e2 ⊢
    rw [e1, e2, ← mul_assoc, Units.mul_inv, one_mul]
  right_inv' X hX := by
    simp only [mem_ofPred_eq] at hX
    simp only [inv_mul_cancel_left, coe_expG]
    rw [h.symm_exp hX, subspaceProj_coe]
  open_source := h.isOpen_nhdOne.preimage
    ((continuous_val_val G).comp (continuous_const.mul continuous_id))
  open_target := h.isOpen_nhd.preimage continuous_subtype_val
  continuousOn_toFun := by
    refine (subspaceProj 𝔤).continuous.comp_continuousOn ?_
    refine (𝔢).continuousOn_symm.comp
      ((continuous_val_val G).comp (continuous_const.mul continuous_id)).continuousOn ?_
    intro x hx; exact h.nhdOne_subset_target hx
  continuousOn_invFun := (continuous_const.mul h.continuous_expG).continuousOn
end IsExpLieAlgebra
namespace IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
local notation "𝔢" => expPartialHomeomorph ℝ 𝔸
@[instance_reducible]
noncomputable def chartedSpace : ChartedSpace 𝔤 G where
  atlas := range h.chart
  chartAt := h.chart
  mem_chart_source g := by
    show (((g⁻¹ * g : G) : 𝔸ˣ) : 𝔸) ∈ h.nhdOne
    simpa using h.one_mem_nhdOne
  chart_mem_atlas g := mem_range_self g
theorem contDiffOn_proj_symm_mul_exp {n : WithTop ℕ∞} (c : 𝔸) (s : Set 𝔤)
    (hs : ∀ X ∈ s, c * exp (X : 𝔸) ∈ (𝔢).target) :
    ContDiffOn ℝ n (fun X : 𝔤 => subspaceProj 𝔤 ((𝔢).symm (c * exp (X : 𝔸)))) s :=
  (subspaceProj 𝔤).contDiff.comp_contDiffOn ((contDiffOn_expPartialHomeomorph_symm ℝ 𝔸).comp
    (contDiff_const.mul ((contDiff_exp ℝ 𝔸).comp 𝔤.subtypeL.contDiff)).contDiffOn hs)
theorem isManifold (n : WithTop ℕ∞) : letI := h.chartedSpace; IsManifold 𝓘(ℝ, 𝔤) n G := by
  let := h.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨g, rfl⟩ ⟨g', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, range_id, inter_univ]
  have key : ∀ X : 𝔤, ((((g' : G)⁻¹ * (h.chart g).symm X : G) : 𝔸ˣ) : 𝔸) =
      ((((g'⁻¹ * g : G) : 𝔸ˣ) : 𝔸)) * exp (X : 𝔸) := by
    intro X; show _ = _; simp [chart, expG, mul_assoc]
  refine (contDiffOn_proj_symm_mul_exp ((((g'⁻¹ * g : G) : 𝔸ˣ) : 𝔸)) _ ?_).congr ?_
  · intro X hX
    rw [← key]
    exact h.nhdOne_subset_target hX.2
  · intro X _
    exact congrArg (fun a => subspaceProj 𝔤 ((𝔢).symm a)) (key X)
theorem contMDiff_val (n : WithTop ℕ∞) : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔸) n (fun x : G => ((x : 𝔸ˣ) : 𝔸)) := by
  let := h.chartedSpace
  intro x
  rw [contMDiffAt_iff_source]
  have : (fun x : G => ((x : 𝔸ˣ) : 𝔸)) ∘ (extChartAt 𝓘(ℝ, 𝔤) x).symm =
      fun X : 𝔤 => ((x : 𝔸ˣ) : 𝔸) * exp (X : 𝔸) := rfl
  rw [this]
  exact (contDiff_const.mul ((contDiff_exp ℝ 𝔸).comp 𝔤.subtypeL.contDiff)).contMDiff.contMDiffAt
    |>.contMDiffWithinAt
theorem contMDiffAt_of_val {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {n : WithTop ℕ∞} {f : M → G} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, 𝔸) n (fun y => ((f y : 𝔸ˣ) : 𝔸)) x) :
    letI := h.chartedSpace; ContMDiffAt I 𝓘(ℝ, 𝔤) n f x := by
  let := h.chartedSpace
  rw [contMDiffAt_iff_target]
  refine ⟨?_, ?_⟩
  · have hemb : Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) :=
      Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    exact hemb.continuousAt_iff.2 hf.continuousAt
  · set c : 𝔸 := ((((f x)⁻¹ : G) : 𝔸ˣ) : 𝔸) with hc
    have h1 : c * ((f x : 𝔸ˣ) : 𝔸) = 1 := by simp [c]
    have hF : ContDiffAt ℝ n (fun a : 𝔸 => subspaceProj 𝔤 ((𝔢).symm (c * a)))
        (((f x : 𝔸ˣ) : 𝔸)) := by
      refine (subspaceProj 𝔤).contDiff.contDiffAt.comp _ ?_
      refine ContDiffAt.comp (g := (𝔢).symm) (f := fun a => c * a) _ ?_
        (contDiff_const.mul contDiff_id).contDiffAt
      simp only [h1]
      exact (contDiffOn_expPartialHomeomorph_symm ℝ 𝔸).contDiffAt
        ((𝔢).open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ 𝔸))
    exact ContDiffAt.comp_contMDiffAt (f := fun y => ((f y : 𝔸ˣ) : 𝔸)) hF hf
theorem lieGroup (n : WithTop ℕ∞) : letI := h.chartedSpace; LieGroup 𝓘(ℝ, 𝔤) n G := by
  let := h.chartedSpace
  exact {
    toIsManifold := h.isManifold n
    contMDiff_mul := fun p => by
      refine h.contMDiffAt_of_val ?_
      have : ContMDiff (𝓘(ℝ, 𝔤).prod 𝓘(ℝ, 𝔤)) 𝓘(ℝ, 𝔸 × 𝔸) n
          (fun p : G × G => (((p.1 : 𝔸ˣ) : 𝔸), ((p.2 : 𝔸ˣ) : 𝔸))) :=
        ((h.contMDiff_val n).comp contMDiff_fst).prodMk_space ((h.contMDiff_val n).comp contMDiff_snd)
      exact (contDiff_mul.comp_contMDiff this) p
    contMDiff_inv := fun x => by
      refine h.contMDiffAt_of_val ?_
      have hx : ContDiffAt ℝ n Ring.inverse (((x : 𝔸ˣ) : 𝔸)) := contDiffAt_ringInverse ℝ (x : 𝔸ˣ)
      have := ContDiffAt.comp_contMDiffAt (f := fun x : G => ((x : 𝔸ˣ) : 𝔸)) hx ((h.contMDiff_val n) x)
      convert this using 1
      funext y
      simp }
end IsExpLieAlgebra
end LinearLie
section IndefiniteUnitary
open Matrix
open scoped Matrix.Norms.L2Operator
variable (p q : ℕ)
def indefJ : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
theorem indefJ_mul_self : indefJ p q * indefJ p q = 1 := by
  rw [indefJ, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; cases i <;> simp
theorem isUnit_indefJ : IsUnit (indefJ p q) :=
  ⟨⟨indefJ p q, indefJ p q, indefJ_mul_self p q, indefJ_mul_self p q⟩, rfl⟩
theorem inv_indefJ : (indefJ p q)⁻¹ = indefJ p q :=
  inv_eq_left_inv (indefJ_mul_self p q)
theorem norm_indefJ_le : ‖indefJ p q‖ ≤ 1 := by
  rw [indefJ, l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun i => ?_
  cases i <;> simp
def indefiniteUnitaryGroup : Subgroup (GL (Fin p ⊕ Fin q) ℂ) where
  carrier := {g | g.valᴴ * indefJ p q * g.val = indefJ p q}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [mem_ofPred_eq, Units.val_mul, conjTranspose_mul] at ha hb ⊢
    calc b.valᴴ * a.valᴴ * indefJ p q * (a.val * b.val)
        = b.valᴴ * (a.valᴴ * indefJ p q * a.val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = indefJ p q := by rw [ha, hb]
  inv_mem' {a} ha := by
    simp only [mem_ofPred_eq] at ha ⊢
    calc (a⁻¹).valᴴ * indefJ p q * (a⁻¹).val
        = (a⁻¹).valᴴ * (a.valᴴ * indefJ p q * a.val) * (a⁻¹).val := by rw [ha]
      _ = (a.val * (a⁻¹).val)ᴴ * indefJ p q * (a.val * (a⁻¹).val) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = indefJ p q := by simp
def indefiniteUnitaryLieAlgebra : Submodule ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  carrier := {X | Xᴴ * indefJ p q + indefJ p q * X = 0}
  add_mem' {X Y} hX hY := by
    simp only [mem_ofPred_eq, conjTranspose_add, Matrix.add_mul, Matrix.mul_add] at hX hY ⊢
    calc Xᴴ * indefJ p q + Yᴴ * indefJ p q + (indefJ p q * X + indefJ p q * Y)
        = (Xᴴ * indefJ p q + indefJ p q * X) + (Yᴴ * indefJ p q + indefJ p q * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [mem_ofPred_eq, conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul] at hX ⊢
    rw [← smul_add, hX, smul_zero]
end IndefiniteUnitary
section IndefiniteUnitaryLie
open Matrix
open scoped Matrix.Norms.L2Operator
variable (p q : ℕ)
local notation "𝔐" => Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ
theorem mem_indefiniteUnitaryLieAlgebra_iff {X : 𝔐} :
    X ∈ indefiniteUnitaryLieAlgebra p q ↔ Xᴴ = -(indefJ p q * X * indefJ p q) := by
  change Xᴴ * indefJ p q + indefJ p q * X = 0 ↔ _
  constructor
  · intro h
    have h' : Xᴴ * indefJ p q = -(indefJ p q * X) := eq_neg_of_add_eq_zero_left h
    calc Xᴴ = Xᴴ * indefJ p q * indefJ p q := by rw [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
      _ = -(indefJ p q * X * indefJ p q) := by rw [h', Matrix.neg_mul]
  · intro h
    rw [h, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one,
      neg_add_cancel]
theorem mem_indefiniteUnitaryGroup_iff {g : GL (Fin p ⊕ Fin q) ℂ} :
    g ∈ indefiniteUnitaryGroup p q ↔ g.valᴴ * indefJ p q * g.val = indefJ p q := Iff.rfl
theorem exp_neg_conj_indefJ (X : 𝔐) :
    exp (-(indefJ p q * X * indefJ p q)) = indefJ p q * exp (-X) * indefJ p q := by
  have := Matrix.exp_conj (indefJ p q) (-X) (isUnit_indefJ p q)
  rw [inv_indefJ] at this
  rw [← this, Matrix.mul_neg, Matrix.neg_mul]
theorem exp_mul_exp_neg (X : 𝔐) : exp X * exp (-X) = 1 := (expUnit ℝ 𝔐 X).mul_inv
theorem exp_neg_mul_exp (X : 𝔐) : exp (-X) * exp X = 1 := (expUnit ℝ 𝔐 X).inv_mul
theorem isExpLieAlgebra_indefiniteUnitary :
    IsExpLieAlgebra (indefiniteUnitaryGroup p q) (indefiniteUnitaryLieAlgebra p q) where
  expUnit_mem X hX := by
    rw [mem_indefiniteUnitaryLieAlgebra_iff] at hX
    rw [mem_indefiniteUnitaryGroup_iff, coe_expUnit, ← Matrix.exp_conjTranspose, hX,
      exp_neg_conj_indefJ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (indefJ p q) (indefJ p q), indefJ_mul_self, Matrix.one_mul,
      exp_neg_mul_exp, Matrix.mul_one]
  exists_nhds := by
    obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 (expPartialHomeomorph ℝ 𝔐).open_source 0
      (zero_mem_expPartialHomeomorph_source ℝ 𝔐)
    refine ⟨Metric.ball 0 ε, Metric.isOpen_ball, Metric.mem_ball_self εpos, hε, fun X hX hG => ?_⟩
    rw [mem_indefiniteUnitaryGroup_iff, coe_expUnit] at hG
    rw [mem_indefiniteUnitaryLieAlgebra_iff]
    have h1 : (exp X)ᴴ = indefJ p q * exp (-X) * indefJ p q := by
      calc (exp X)ᴴ = (exp X)ᴴ * indefJ p q * (exp X * exp (-X)) * indefJ p q := by
            rw [exp_mul_exp_neg, Matrix.mul_one, Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
        _ = (exp X)ᴴ * indefJ p q * exp X * exp (-X) * indefJ p q := by
            simp only [Matrix.mul_assoc]
        _ = indefJ p q * exp (-X) * indefJ p q := by rw [hG]
    have h2 : exp Xᴴ = exp (-(indefJ p q * X * indefJ p q)) := by
      rw [Matrix.exp_conjTranspose, h1, exp_neg_conj_indefJ]
    have hX' : ‖X‖ < ε := mem_ball_zero_iff.1 hX
    have hs1 : Xᴴ ∈ (expPartialHomeomorph ℝ 𝔐).source := hε (by
      rw [mem_ball_zero_iff, l2_opNorm_conjTranspose]; exact hX')
    have hs2 : -(indefJ p q * X * indefJ p q) ∈ (expPartialHomeomorph ℝ 𝔐).source := hε (by
      rw [mem_ball_zero_iff, norm_neg]
      calc ‖indefJ p q * X * indefJ p q‖ ≤ ‖indefJ p q‖ * ‖X‖ * ‖indefJ p q‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1 * ‖X‖ * 1 := by
            gcongr
            · exact norm_indefJ_le p q
            · exact norm_indefJ_le p q
        _ < ε := by simpa using hX')
    exact (expPartialHomeomorph ℝ 𝔐).injOn hs1 hs2 h2
noncomputable instance : ChartedSpace (indefiniteUnitaryLieAlgebra p q) (indefiniteUnitaryGroup p q) :=
  (isExpLieAlgebra_indefiniteUnitary p q).chartedSpace
instance lieGroup_indefiniteUnitary (n : WithTop ℕ∞) :
    LieGroup 𝓘(ℝ, indefiniteUnitaryLieAlgebra p q) n (indefiniteUnitaryGroup p q) :=
  (isExpLieAlgebra_indefiniteUnitary p q).lieGroup n
end IndefiniteUnitaryLie
end GroundTheory.Automorphic


