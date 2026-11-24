-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:46.828937+00:00
-- url     : https://prove2.me/theorems/f9168a94-9177-4af4-b97e-ec808d549c65
-- title:
--   Star Coeff Eisenstein Series Reverse Poly
-- statement:
--   Definitions and structural lemmas for Star Coeff Eisenstein Series Reverse Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StarCoeffEisensteinSeriesReversePoly.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply


set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
namespace GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
section Tensor
variable {ι : Type} {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
def semiMap (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    PiTensorProduct ℂ V →+ PiTensorProduct ℂ W :=
  PiTensorProduct.liftAddHom (fun p => σ p.1 • PiTensorProduct.tprod ℂ fun i => j i (p.2 i))
    (fun r f i hf => by
      rw [MultilinearMap.map_coord_zero _ i (by simp [hf]), smul_zero])
    (fun f => by simp)
    (fun r f i m₁ m₂ => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, map_add, MultilinearMap.map_update_add, smul_add])
    (fun r r' f => by simp [add_smul])
    (fun r f i r' => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, hj, MultilinearMap.map_update_smul, Function.update_eq_self, map_mul, smul_smul, mul_comm])
end Tensor
section Conj
variable {Γ : Type} [Group Γ]
def bcEquiv (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : τ ≃+ bc σ τ :=
  (Module.finBasis ℂ τ).equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
end Conj
section Label
variable {K : Type} [Field K]
variable [Fintype K] [DecidableEq K] {Cv : LabelConv K}
end Label
end GlobalTheory.SerConj


