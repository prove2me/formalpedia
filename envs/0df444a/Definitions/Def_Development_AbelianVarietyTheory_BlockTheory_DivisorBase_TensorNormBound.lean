-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:28.463556+00:00
-- url     : https://prove2.me/theorems/2975ab64-359d-4164-b232-1ab7256f0d8a
-- title:
--   Tensor Norm Bound
-- statement:
--   Definitions and structural lemmas for Tensor Norm Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TensorNormBound.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds
open Formalism.BasicNotions Formalism.L2.DIV
variable {ι : Type} [Fintype ι] {n n' : ℕ}
def nsqOne (lam : DomWeight n) (f : nablaSq ℂ n lam) : ℝ :=
  (normFock lam (f : MvPolynomial (Fin n × Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ)).re
def nsqAll (lam : ι → DomWeight n) (F : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) F F).re
def NormLeOne {lam : DomWeight n} {lam' : DomWeight n'} (A : nablaSq ℂ n lam →ₗ[ℂ] nablaSq ℂ n' lam') (c : ℝ) :
    Prop :=
  0 ≤ c ∧ ∀ f, nsqOne lam' (A f) ≤ c ^ 2 * nsqOne lam f
def NormLeAll {lam : ι → DomWeight n} {lam' : ι → DomWeight n'} (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ F, nsqAll lam' (T F) ≤ c ^ 2 * nsqAll lam F
def tenV (lam : ι → DomWeight n) (f : ∀ τ, nablaSq ℂ n (lam τ)) : VV ℂ lam :=
  ⟨ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ),
    Submodule.subset_span ⟨fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ), fun τ => (f τ).2, rfl⟩⟩
def IsTensorMap {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') : Prop :=
  ∀ f : ∀ τ, nablaSq ℂ n (lam τ), T (tenV lam f) = tenV lam' fun τ => A τ (f τ)
def TensorNormLe : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)),
    (∃ T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap A T) ∧
    ∀ (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam'), IsTensorMap A T →
      ∀ c : ι → ℝ, (∀ τ, NormLeOne (A τ) (c τ)) → NormLeAll T (∏ τ, c τ)
def TensorNormEq : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam'),
    IsTensorMap A T → ∀ c : ι → ℝ, (∀ τ, IsLeast {d : ℝ | NormLeOne (A τ) d} (c τ)) →
      IsLeast {d : ℝ | NormLeAll T d} (∏ τ, c τ)
example (lam : ι → DomWeight n) : IsTensorMap (lam := lam) (lam' := lam) (fun _ => LinearMap.id) LinearMap.id :=
  fun _ => rfl
example (lam : DomWeight n) : NormLeOne (lam := lam) (lam' := lam) LinearMap.id 1 :=
  ⟨zero_le_one, fun f => by simp⟩
end GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds


