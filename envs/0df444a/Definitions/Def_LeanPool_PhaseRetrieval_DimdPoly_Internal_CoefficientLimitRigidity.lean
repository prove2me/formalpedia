-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:17:10.722468+00:00
-- url     : https://prove2.me/theorems/114ae91a-980b-4a1f-be5c-8b93f877d112
-- title:
--   Coefficient Limit Rigidity
-- statement:
--   Definitions and structural lemmas for Coefficient Limit Rigidity, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/CoefficientLimitRigidity.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Topology.MetricSpace.Sequences
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
def coefficientControlSet_wip
    {d : Nat} {kappa : MultiIndex d} (E : Finset (Idx d)) (F : Pkappa d kappa) :
    Finset (Idx d) :=
  E ∪ F.support
def orthogonalToSkappa_wip
    {d : Nat} {kappa : MultiIndex d}
    (F : Pkappa d kappa) (U : Skappa d kappa) : Prop :=
  Finset.sum F.support
    (fun alpha => coeffSkappa U alpha * star (coeffPkappa F alpha)) = 0
def skappaOfCoeffBound_wip
    {d : Nat} (kappa : MultiIndex d) (u : Idx d -> ℂ)
    (hpartial :
      ∀ E : Finset (Idx d), Finset.sum E (fun alpha => ‖u alpha‖ ^ 2) <= 1) :
    Skappa d kappa :=
  { coeff := u
    summable_norm_sq := by exact summable_of_sum_le (fun alpha => sq_nonneg (‖u alpha‖)) hpartial }
def defectFunctionPkappa_coeff_wip
    {d : Nat} (kappa : MultiIndex d) (F G : Pkappa d kappa) :
    Cd d -> ℝ :=
  fun z => |‖evalPkappa kappa (F + G) z‖ - ‖evalPkappa kappa F z‖|
def skappaAffinePkappa_wip
    {d : Nat} (kappa : MultiIndex d)
    (F : Pkappa d kappa) (U : Skappa d kappa) (a b : ℂ) :
    Skappa d kappa where
  coeff := fun alpha => a * coeffPkappa F alpha + b * coeffSkappa U alpha
  summable_norm_sq := by
    classical
    let f : Idx d -> ℝ := fun alpha => ‖a * coeffPkappa F alpha‖ ^ 2
    let g : Idx d -> ℝ := fun alpha => ‖b * coeffSkappa U alpha‖ ^ 2
    have hf : Summable f := by
      dsimp [f, coeffPkappa]
      refine summable_of_hasFiniteSupport ?_
      refine Set.Finite.subset F.support.finite_toSet ?_
      intro alpha hnonzero
      simp_all
    have hg : Summable g := by
      have hg_eq :
          g = fun alpha => (‖b‖ ^ 2) * (‖coeffSkappa U alpha‖ ^ 2) := by
        funext alpha
        dsimp [g]
        rw [norm_mul, mul_pow]
      rw [hg_eq]
      exact U.summable_norm_sq.mul_left (‖b‖ ^ 2)
    have hsum : Summable (fun alpha => 2 * f alpha + 2 * g alpha) :=
      (hf.mul_left 2).add (hg.mul_left 2)
    refine hsum.of_nonneg_of_le (fun alpha => sq_nonneg _) ?_
    intro alpha
    dsimp [f, g]
    let x : ℂ := a * coeffPkappa F alpha
    let y : ℂ := b * coeffSkappa U alpha
    have hnorm : ‖x + y‖ <= ‖x‖ + ‖y‖ := norm_add_le x y
    have hsq :
        ‖x + y‖ ^ 2 <= (‖x‖ + ‖y‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    have hquad : (‖x‖ + ‖y‖) ^ 2 <= 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    have hfinal := le_trans hsq hquad
    simpa [x, y] using hfinal
end DimdPolyLEAN


