-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:14.397799+00:00
-- url     : https://prove2.me/theorems/fa27f599-20bc-4e1a-8393-642e8d9ae9f8
-- title:
--   Tensor Irr
-- statement:
--   Definitions and structural lemmas for Tensor Irr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/TensorIrr.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute
import Definitions.Def_Formalism_LocalToGlobal_ThetaOperatorCommutation_RealTh
import Definitions.Def_ReciprocityTheory_ThetaSummability_RealCoinvariants_Numbers
import Mathlib.LinearAlgebra.PiTensorProduct
import Theorems.Thm_PositivityTheory_KReal_fockAct1_fockAct2_commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action
namespace PositivityTheory.KReal
abbrev ThV (D : RealData) : Type := ThC D.P D.Q D.R D.S ((D.κ : ℂ) / 2)
abbrev ThV' (D : RealData) : Type := ThC D.P' D.Q' D.R D.S (-((D.κ : ℂ) / 2))
def opV (D : RealData) (W : Mat D.R D.S) : Module.End ℂ (ThV D) :=
  ReciprocityTheory.ThetaSummability.Real.coinvOp (chiTr ((D.κ : ℂ) / 2)) (fockAct2 _ _ _ _ W) fun Z => (fockAct1_fockAct2_commute Z W).symm
def opV' (D : RealData) (W : Mat D.R D.S) : Module.End ℂ (ThV' D) :=
  ReciprocityTheory.ThetaSummability.Real.coinvOp (chiTr (-((D.κ : ℂ) / 2))) (fockAct2 _ _ _ _ W) (fun Z => (fockAct1_fockAct2_commute Z W).symm) +
    ((D.κ : ℂ) / 2 * W.trace) • 1
def CoreLM : Prop :=
  ∀ D : RealData, D.Hyp → ∃ (Pi : Type) (_ : AddCommGroup Pi) (_ : Module ℂ Pi) (act : Mat D.R D.S → Module.End ℂ Pi)
    (π : ThV D →ₗ[ℂ] Pi) (π' : ThV' D →ₗ[ℂ] Pi), Function.Surjective π ∧ Function.Surjective π' ∧
    (∀ W x, π (opV D W x) = act W (π x)) ∧ (∀ W x, π' (opV' D W x) = act W (π' x)) ∧ Nontrivial Pi ∧
    ∀ N : Submodule ℂ Pi, (∀ W, ∀ x ∈ N, act W x ∈ N) → N = ⊥ ∨ N = ⊤
def TensorIrr : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Type) (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (act : ∀ i, A i → Module.End ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (M i)) →
    (∀ i, ∀ N : Submodule ℂ (M i), (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (PiTensorProduct ℂ M),
      (∀ i a, ∀ x ∈ N, PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i (act i a)) x ∈ N) →
      N = ⊥ ∨ N = ⊤
end PositivityTheory.KReal
end


