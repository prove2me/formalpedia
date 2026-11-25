-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:56:19.004291+00:00
-- url     : https://prove2.me/theorems/045131a6-29bc-54b0-9c08-394cc7848ed8
-- title:
--   Adjoint Leibniz Expansion
-- statement:
--   Definitions and structural lemmas for Adjoint Leibniz Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_leib
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll


set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section hsadj
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
def hsVecL : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := hsVec
  map_add' A B := by
    unfold hsVec
    ext i
    simp
  map_smul' c A := by
    unfold hsVec
    ext i
    simp
theorem hsVec_injective : Function.Injective (hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  intro A B h
  apply ContinuousLinearMap.coe_injective
  refine (stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => ?_
  have := congrFun (congrArg WithLp.ofLp h) i
  simpa [hsVec] using this
theorem hsVec_surjective :
    Function.Surjective (hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  intro v
  refine ⟨∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ Wq i)).smulRight (WithLp.ofLp v i), ?_⟩
  first
  | (ext j
     simp [hsVec, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, OrthonormalBasis.inner_eq_ite,
       ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq'])
  | (apply WithLp.ofLp_injective
     funext j
     simp [hsVec, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, OrthonormalBasis.inner_eq_ite,
       ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq'])
def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearEquiv.ofBijective hsVecL ⟨hsVec_injective, hsVec_surjective⟩
theorem hsE_apply (A : Wq →L[ℂ] Wp) : hsE A = hsVec A := rfl
def hsAdj (B : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap ((hsE.symm.toLinearMap ∘ₗ
    LinearMap.adjoint (hsE.toLinearMap ∘ₗ B.toLinearMap ∘ₗ hsE.symm.toLinearMap)) ∘ₗ hsE.toLinearMap)
theorem hsAdj_spec (B : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A C : Wq →L[ℂ] Wp) :
    hsInner (B A) C = hsInner A (hsAdj B C) := by
  simp only [hsInner, ← hsE_apply]
  unfold hsAdj
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.adjoint_inner_left, ContinuousLinearMap.coe_coe,
    LinearEquiv.symm_apply_apply]
end hsadj
section calculus1
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end calculus1
def splits {α : Type*} : List α → List (List α × List α)
  | [] => [([], [])]
  | X :: w => (splits w).map (fun uv => (X :: uv.1, uv.2)) ++ (splits w).map (fun uv => (uv.1, X :: uv.2))
section leib
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end leib
section adjop
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
def lieOr (v : List (Mat k r)) : List (Mat k r) := by
  classical exact if ∀ X ∈ v, inLie k r X then v else []
theorem lieOr_lie (v : List (Mat k r)) : ∀ X ∈ lieOr v, inLie k r X := by
  unfold lieOr
  split_ifs with h
  · exact h
  · simp
def adjTerm (T : DTerm k r Wp Wq) (uv : List (Mat k r) × List (Mat k r)) : DTerm k r Wp Wq where
  coef := fun g => ((-1 : ℂ) ^ T.word.length) • Rw uv.1 T.coefAdj g
  coefAdj := fun g => hsAdj (((-1 : ℂ) ^ T.word.length) • Rw uv.1 T.coefAdj g)
  word := lieOr uv.2
  word_lie := lieOr_lie uv.2
  adj_id := fun _ A B => hsAdj_spec _ A B
def adjOp (Θ : DiffOp k r Wp Wq) : DiffOp k r Wp Wq :=
  Θ.flatMap fun T => (splits T.word.reverse).map (adjTerm T)
end adjop
end Formalism.FourierDecayAlt.P.JFxI
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


