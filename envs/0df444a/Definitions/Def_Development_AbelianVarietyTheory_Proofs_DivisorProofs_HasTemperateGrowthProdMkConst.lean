-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:06.418895+00:00
-- url     : https://prove2.me/theorems/705ebe45-9fd4-4fd3-a0f3-c4b741d1102b
-- title:
--   Has Temperate Growth Prod Mk Const
-- statement:
--   Definitions and structural lemmas for Has Temperate Growth Prod Mk Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasTemperateGrowthProdMkConst.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
namespace GlobalTheory.SchwartzFstOp
variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem hasTemperateGrowth_prodMk_const (x' : V') : Function.HasTemperateGrowth (fun x : V => (x, x')) := by
  have h := (ContinuousLinearMap.inl ℝ V V').hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const ((0 : V), x'))
  convert h using 1
  funext x
  simp
theorem antilipschitz_prodMk_const (x' : V') : AntilipschitzWith 1 (fun x : V => (x, x')) :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq, dist_self]
    exact le_max_left _ _
def sliceCLM (x' : V') : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_prodMk_const x') (antilipschitz_prodMk_const x')
@[simp] theorem sliceCLM_apply (x' : V') (f : 𝓢(V × V', ℂ)) (x : V) : sliceCLM x' f x = f (x, x') := rfl
def lineSnd (v' : V') : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V × V', ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V × V', ℂ) ((0 : V), v')
theorem lineSnd_apply (v' : V') (f : 𝓢(V × V', ℂ)) (p : V × V') :
    lineSnd v' f p = fderiv ℝ f p ((0 : V), v') := by
  rw [lineSnd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
theorem lineSnd_add (v₁ v₂ : V') (f : 𝓢(V × V', ℂ)) :
    lineSnd (v₁ + v₂) f = lineSnd v₁ f + lineSnd v₂ f := by
  ext p
  simp only [lineSnd_apply, SchwartzMap.add_apply]
  rw [← map_add]
  simp
theorem lineSnd_smul (c : ℝ) (v : V') (f : 𝓢(V × V', ℂ)) :
    lineSnd (c • v) f = (c : ℂ) • lineSnd v f := by
  ext p
  simp only [lineSnd_apply, SchwartzMap.smul_apply]
  rw [show ((0 : V), c • v) = c • ((0 : V), v) by simp, map_smul]
  simp [Complex.real_smul]
def opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V') : E :=
  T (sliceCLM p.2 f) p.1
def dSndCLM [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V') :
    V' →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v' => opFst T (lineSnd v' f) p
      map_add' := fun v₁ v₂ => by simp [opFst, lineSnd_add]
      map_smul' := fun c v => by
        simp only [opFst, lineSnd_smul, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]
        rw [Complex.coe_smul] }
end GlobalTheory.SchwartzFstOp


