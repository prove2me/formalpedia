-- Prove2me | Definitions.Def_Operator_Dilation_Schaeffer
-- name    : Operator_Dilation_Schaeffer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:30:14.152705+00:00
-- url     : https://prove2.me/theorems/705d5c41-fc0f-5ecc-ac80-30729e2419ec
-- title:
--   Schaeffer
-- statement:
--   Definitions and structural lemmas for Schaeffer, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Dilation/Schaeffer.lean

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Operator_Dilation_Halmos
set_option autoImplicit false
open scoped ENNReal InnerProductSpace
universe u
noncomputable section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
abbrev SchaefferSpace (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  lp (fun _ : ℤ => E) 2
noncomputable def schaefferEmbedding : E →L[ℂ] SchaefferSpace E :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℤ => E) 2 0
omit [CompleteSpace E] in
@[simp]
theorem schaefferEmbedding_apply (x : E) :
    schaefferEmbedding x = lp.single 2 (0 : ℤ) x := rfl
noncomputable def lpReindexForward {ι ι' : Type*} (e : ι ≃ ι')
    (f : lp (fun _ : ι => E) 2) : lp (fun _ : ι' => E) 2 :=
  ⟨fun j => f (e.symm j), by
    change Memℓp (fun j : ι' => f (e.symm j)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact e.symm.summable_iff.mpr
      ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
omit [InnerProductSpace ℂ E] [CompleteSpace E] in
@[simp]
theorem lpReindexForward_apply {ι ι' : Type*} (e : ι ≃ ι')
    (f : lp (fun _ : ι => E) 2) (j : ι') :
    lpReindexForward e f j = f (e.symm j) := rfl
omit [InnerProductSpace ℂ E] [CompleteSpace E] in
theorem norm_lpReindexForward {ι ι' : Type*} (e : ι ≃ ι')
    (f : lp (fun _ : ι => E) 2) : ‖lpReindexForward e f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖lpReindexForward e f‖ ^ 2 = ∑' j : ι', ‖f (e.symm j)‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, lpReindexForward_apply] using
        lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (lpReindexForward e f)
    _ = ∑' i : ι, ‖f i‖ ^ (2 : ℕ) :=
      e.symm.tsum_eq (fun i : ι => ‖f i‖ ^ (2 : ℕ))
    _ = ‖f‖ ^ 2 := by
      symm
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f
noncomputable def lpReindex {ι ι' : Type*} (e : ι ≃ ι') :
    lp (fun _ : ι => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι' => E) 2 where
  toFun := lpReindexForward e
  invFun := lpReindexForward e.symm
  left_inv f := by
    apply lp.ext
    funext i
    simp only [lpReindexForward_apply, Equiv.symm_symm, e.symm_apply_apply]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [lpReindexForward_apply, Equiv.symm_symm, e.apply_symm_apply]
  map_add' _ _ := by
    apply lp.ext
    rfl
  map_smul' _ _ := by
    apply lp.ext
    rfl
  norm_map' := norm_lpReindexForward e
noncomputable def schaefferBilateralShiftEquiv :
    SchaefferSpace E ≃ₗᵢ[ℂ] SchaefferSpace E :=
  lpReindex (Equiv.addRight (1 : ℤ))
omit [CompleteSpace E] in
@[simp]
theorem schaefferBilateralShiftEquiv_apply (f : SchaefferSpace E) (j : ℤ) :
    schaefferBilateralShiftEquiv f j = f (j - 1) := rfl
noncomputable def schaefferBilateralShiftUnitary :
    unitary (SchaefferSpace E →L[ℂ] SchaefferSpace E) :=
  Unitary.linearIsometryEquiv.symm schaefferBilateralShiftEquiv
noncomputable def schaefferBilateralShift :
    SchaefferSpace E →L[ℂ] SchaefferSpace E :=
  schaefferBilateralShiftUnitary (E := E)
@[simp]
theorem schaefferBilateralShift_apply (f : SchaefferSpace E) (j : ℤ) :
    schaefferBilateralShift f j = f (j - 1) := by
  change schaefferBilateralShiftEquiv f j = f (j - 1)
  exact schaefferBilateralShiftEquiv_apply f j
abbrev SchaefferNetworkFiber (E : Type u) [NormedAddCommGroup E] := WithLp 2 (E × E)
abbrev SchaefferNetworkSpace (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] := lp (fun _ : ℤ => SchaefferNetworkFiber E) 2
noncomputable def schaefferFiberEmbedding :
    E →L[ℂ] SchaefferNetworkFiber E :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ E E)
omit [CompleteSpace E] in
@[simp]
theorem schaefferFiberEmbedding_apply (x : E) :
    schaefferFiberEmbedding x = WithLp.toLp 2 (x, 0) := rfl
noncomputable def schaefferNetworkEmbedding :
    E →L[ℂ] SchaefferNetworkSpace E :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => SchaefferNetworkFiber E) 2 0).comp
    schaefferFiberEmbedding
omit [CompleteSpace E] in
@[simp]
theorem schaefferNetworkEmbedding_apply (x : E) :
    schaefferNetworkEmbedding x = lp.single 2 (0 : ℤ) (WithLp.toLp 2 (x, 0)) := rfl
def lpPointwiseForward
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) : SchaefferNetworkSpace E :=
  ⟨fun i => W (f i), by
    change Memℓp (fun i : ℤ => W (f i)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [W.norm_map] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩
omit [CompleteSpace E] in
@[simp]
theorem lpPointwiseForward_apply
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) (i : ℤ) :
    lpPointwiseForward W f i = W (f i) := rfl
omit [CompleteSpace E] in
theorem norm_lpPointwiseForward
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E)
    (f : SchaefferNetworkSpace E) : ‖lpPointwiseForward W f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [show ‖lpPointwiseForward W f‖ ^ 2 =
      ∑' i : ℤ, ‖lpPointwiseForward W f i‖ ^ (2 : ℕ) by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (lpPointwiseForward W f)]
  rw [show ‖f‖ ^ 2 = ∑' i : ℤ, ‖f i‖ ^ (2 : ℕ) by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f]
  simp only [lpPointwiseForward_apply, W.norm_map]
def lpPointwiseEquiv
    (W : SchaefferNetworkFiber E ≃ₗᵢ[ℂ] SchaefferNetworkFiber E) :
    SchaefferNetworkSpace E ≃ₗᵢ[ℂ] SchaefferNetworkSpace E where
  toFun := lpPointwiseForward W
  invFun := lpPointwiseForward W.symm
  left_inv f := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, W.symm_apply_apply]
  right_inv f := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, W.apply_symm_apply]
  map_add' _ _ := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' _ _ := by
    apply lp.ext
    funext i
    simp only [lpPointwiseForward_apply, lp.coeFn_smul, Pi.smul_apply, map_smul,
      RingHom.id_apply]
  norm_map' := norm_lpPointwiseForward W
def schaefferPointwiseUnitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  Unitary.linearIsometryEquiv.symm
    (lpPointwiseEquiv (Unitary.linearIsometryEquiv J))
omit [CompleteSpace E] in
theorem summable_network_fst_sq (f : SchaefferNetworkSpace E) :
    Summable fun i : ℤ => ‖(f i).fst‖ ^ (2 : ℕ) := by
  have hf : Summable fun i : ℤ => ‖f i‖ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine hf.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have h := WithLp.prod_norm_sq_eq_of_L2 (f i)
  nlinarith only [h, sq_nonneg ‖(f i).snd‖]
omit [CompleteSpace E] in
theorem summable_network_snd_sq (f : SchaefferNetworkSpace E) :
    Summable fun i : ℤ => ‖(f i).snd‖ ^ (2 : ℕ) := by
  have hf : Summable fun i : ℤ => ‖f i‖ ^ (2 : ℕ) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  refine hf.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
  have h := WithLp.prod_norm_sq_eq_of_L2 (f i)
  nlinarith only [h, sq_nonneg ‖(f i).fst‖]
def schaefferIntShift : ℤ ≃ ℤ := Equiv.addRight (1 : ℤ)
def schaefferRouteForward (f : SchaefferNetworkSpace E) :
    SchaefferNetworkSpace E :=
  ⟨fun i => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd), by
    change Memℓp
      (fun i : ℤ => WithLp.toLp 2
        ((f i).fst, (f (schaefferIntShift.symm i)).snd)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hs : Summable fun i : ℤ =>
        ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
      schaefferIntShift.symm.summable_iff.mpr (summable_network_snd_sq f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using
      (summable_network_fst_sq f).add hs⟩
omit [CompleteSpace E] in
@[simp]
theorem schaefferRouteForward_apply (f : SchaefferNetworkSpace E) (i : ℤ) :
    schaefferRouteForward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift.symm i)).snd) := rfl
def schaefferRouteBackward (f : SchaefferNetworkSpace E) :
    SchaefferNetworkSpace E :=
  ⟨fun i => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd), by
    change Memℓp
      (fun i : ℤ => WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hs : Summable fun i : ℤ => ‖(f (schaefferIntShift i)).snd‖ ^ (2 : ℕ) :=
      schaefferIntShift.summable_iff.mpr (summable_network_snd_sq f)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using
      (summable_network_fst_sq f).add hs⟩
omit [CompleteSpace E] in
@[simp]
theorem schaefferRouteBackward_apply (f : SchaefferNetworkSpace E) (i : ℤ) :
    schaefferRouteBackward f i =
      WithLp.toLp 2 ((f i).fst, (f (schaefferIntShift i)).snd) := rfl
omit [CompleteSpace E] in
theorem norm_schaefferRouteForward (f : SchaefferNetworkSpace E) :
    ‖schaefferRouteForward f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have ha := summable_network_fst_sq f
  have hb := summable_network_snd_sq f
  have hbShift : Summable fun i : ℤ =>
      ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
    schaefferIntShift.symm.summable_iff.mpr hb
  calc
    ‖schaefferRouteForward f‖ ^ 2 =
        ∑' i : ℤ, (‖(f i).fst‖ ^ (2 : ℕ) +
          ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ)) := by
      rw [show ‖schaefferRouteForward f‖ ^ 2 =
          ∑' i : ℤ, ‖schaefferRouteForward f i‖ ^ (2 : ℕ) by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (schaefferRouteForward f)]
      simp only [schaefferRouteForward_apply, WithLp.prod_norm_sq_eq_of_L2,
        WithLp.toLp_fst, WithLp.toLp_snd]
    _ = (∑' i : ℤ, ‖(f i).fst‖ ^ (2 : ℕ)) +
        ∑' i : ℤ, ‖(f (schaefferIntShift.symm i)).snd‖ ^ (2 : ℕ) :=
      ha.tsum_add hbShift
    _ = (∑' i : ℤ, ‖(f i).fst‖ ^ (2 : ℕ)) +
        ∑' i : ℤ, ‖(f i).snd‖ ^ (2 : ℕ) := by
      rw [schaefferIntShift.symm.tsum_eq
        (fun i : ℤ => ‖(f i).snd‖ ^ (2 : ℕ))]
    _ = ∑' i : ℤ, (‖(f i).fst‖ ^ (2 : ℕ) + ‖(f i).snd‖ ^ (2 : ℕ)) :=
      (ha.tsum_add hb).symm
    _ = ‖f‖ ^ 2 := by
      rw [show ‖f‖ ^ 2 = ∑' i : ℤ, ‖f i‖ ^ (2 : ℕ) by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
            (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f]
      simp only [WithLp.prod_norm_sq_eq_of_L2]
def schaefferRouteEquiv :
    SchaefferNetworkSpace E ≃ₗᵢ[ℂ] SchaefferNetworkSpace E where
  toFun := schaefferRouteForward
  invFun := schaefferRouteBackward
  left_inv f := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    simp only [schaefferRouteBackward_apply, schaefferRouteForward_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_toLp,
      schaefferIntShift.symm_apply_apply]
    exact Prod.eta _
  right_inv f := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    simp only [schaefferRouteBackward_apply, schaefferRouteForward_apply,
      WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_toLp,
      schaefferIntShift.apply_symm_apply]
    exact Prod.eta _
  map_add' _ _ := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    apply Prod.ext <;> rfl
  map_smul' _ _ := by
    apply lp.ext
    funext i
    apply WithLp.ofLp_injective
    apply Prod.ext <;> rfl
  norm_map' := norm_schaefferRouteForward
def schaefferRouteUnitary :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  Unitary.linearIsometryEquiv.symm schaefferRouteEquiv
def schaefferGlobalUnitary
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    unitary (SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E) :=
  schaefferRouteUnitary * schaefferPointwiseUnitary J
noncomputable def schaefferGlobalOperator
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E)) :
    SchaefferNetworkSpace E →L[ℂ] SchaefferNetworkSpace E :=
  schaefferGlobalUnitary J
noncomputable def schaefferOrbit
    (J : unitary (SchaefferNetworkFiber E →L[ℂ] SchaefferNetworkFiber E))
    (n : ℕ) (x : E) : SchaefferNetworkSpace E :=
  (schaefferGlobalOperator J ^ n) (schaefferNetworkEmbedding x)


