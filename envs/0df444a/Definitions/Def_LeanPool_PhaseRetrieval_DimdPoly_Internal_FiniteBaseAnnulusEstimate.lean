-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseAnnulusEstimate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:16:33.858808+00:00
-- url     : https://prove2.me/theorems/b0998b41-7909-41d6-81c1-6528fe6dce3f
-- title:
--   Finite Base Annulus Estimate
-- statement:
--   Definitions and structural lemmas for Finite Base Annulus Estimate, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/FiniteBaseAnnulusEstimate.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseCircleEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductAnnulusCircle
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Tactic.NormNum.Parity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MeasureTheory
namespace DimdPolyLEAN
def mulCircleLIE_annulus (ω : _root_.Circle) : ℂ ≃ₗᵢ[ℝ] ℂ := by
  refine LinearIsometryEquiv.mk
    (LinearEquiv.ofBijective
      (LinearMap.mulLeft ℝ ((ω : ℂ)))
      ?_)
    ?_
  · refine ⟨?inj, ?surj⟩
    · intro x y hxy
      exact mul_left_cancel₀ (Circle.coe_ne_zero ω) (by simpa using hxy)
    · intro z
      refine ⟨((ω⁻¹ : _root_.Circle) : ℂ) * z, ?_⟩
      simp
  · intro x
    change ‖(ω : ℂ) * x‖ = ‖x‖
    have hω : ‖(ω : ℂ)‖ = 1 := Circle.norm_coe ω
    rw [norm_mul, hω, one_mul]
theorem exists_maxCoord_annulus
    {d : Nat} (hd : 0 < d) (j : Idx d) :
    ∃ q0 : Fin d, ∀ q : Fin d, j q ≤ j q0 := by
  let q0 : Fin d := ⟨0, hd⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨q0, Finset.mem_univ q0⟩
  rcases Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin d))) hne
      (f := fun q : Fin d => j q) with ⟨qmax, hqmax, hsup⟩
  refine ⟨qmax, ?_⟩
  intro q
  have hq_le : j q ≤ (Finset.univ : Finset (Fin d)).sup (fun r : Fin d => j r) :=
    Finset.le_sup (s := Finset.univ) (f := fun r : Fin d => j r) (by simp)
  simpa [hsup] using hq_le
noncomputable def maxCoordAnnulus
    {d : Nat} (hd : 0 < d) (j : Idx d) : Fin d :=
  Classical.choose (exists_maxCoord_annulus hd j)
def annulusBandStart
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) : Nat :=
  (max (j q) M - M) ^ 2
def annulusBandLength
    {d : Nat} (j : Idx d) (q : Fin d) (M : Nat) : Nat :=
  (j q + M + 1) ^ 2 - annulusBandStart j q M
def localPartPkappa
    {d : Nat} {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (G : Pkappa d kappa) : Pkappa d kappa :=
  (Hermite1DimdLEAN.localPart j M ⟨G⟩).coeff
def remainderPartPkappa
    {d : Nat} {kappa : MultiIndex d}
    (j : Idx d) (M : Nat) (G : Pkappa d kappa) : Pkappa d kappa :=
  (Hermite1DimdLEAN.remainderPart j M ⟨G⟩).coeff
def baseDefectAnnulusMass
    {d : Nat} (kappa : MultiIndex d) (j : Idx d)
    (F G : Pkappa d kappa) : ℝ :=
  ∫ z, Set.indicator (productAnnulus j)
    (fun w => (‖evalPkappa kappa F w + evalPkappa kappa G w‖ -
      ‖evalPkappa kappa F w‖) ^ 2) z ∂ gammaD d
def fiberIndexLow
    {d : Nat} (q0 : Fin d) (D : Nat) (alpha : Idx d) : Fin (D + 1) :=
  if h : alpha q0 ≤ D then ⟨alpha q0, Nat.lt_succ_of_le h⟩ else 0
noncomputable def fiberCoeffLow
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (D : Nat) (F : Pkappa d kappa) (z : Cd d) :
    Fin (D + 1) → ℂ :=
  fun n =>
    ∑ alpha ∈ F.support.filter (fun alpha => fiberIndexLow q0 D alpha = n),
      F alpha * Phi kappa alpha z
noncomputable def baseCoordDegree
    {d : Nat} {kappa : MultiIndex d} (F : Pkappa d kappa) : Nat :=
  F.support.sup fun alpha => (Finset.univ : Finset (Fin d)).sup fun q => alpha q
def fiberIndexBand
    {d : Nat} (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L) (alpha : Idx d) : Fin L :=
  if h : alpha q0 < N + L then
    ⟨alpha q0 - N, by omega⟩
  else
    ⟨0, by omega⟩
noncomputable def fiberCoeffBand
    {d : Nat} {kappa : MultiIndex d}
    (q0 : Fin d) (N L : Nat) (hL : 1 ≤ L) (H : Pkappa d kappa) (z : Cd d) :
    Fin L → ℂ :=
  fun m =>
    ∑ alpha ∈ H.support.filter (fun alpha => fiberIndexBand q0 N L hL alpha = m),
      H alpha * Phi kappa alpha z
end DimdPolyLEAN


