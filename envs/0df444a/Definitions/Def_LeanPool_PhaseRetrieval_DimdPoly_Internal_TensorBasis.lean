-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:15:20.820862+00:00
-- url     : https://prove2.me/theorems/9b7b06d8-f4b5-419a-bfee-f81cb2d401ef
-- title:
--   Tensor Basis
-- statement:
--   Definitions and structural lemmas for Tensor Basis, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/TensorBasis.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Theorems.Thm_Hermite1DimdLEAN_finiteParseval
public import Theorems.Thm_HermitekLEAN_continuous_Phi
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
theorem phi1D_eq_oneDimPhi
    (k n : Nat) (z : ℂ) :
    phi1D k n z = Hermite1DimdLEAN.oneDimPhi k n z := by
  unfold phi1D complexHermite Hermite1DimdLEAN.oneDimPhi
  congr 1
  · simp [one_div, mul_comm]
  · rw [Nat.min_comm k n]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≤ min n k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjn : j ≤ n := le_trans hj' (Nat.min_le_left _ _)
    have hfac_ne : (Nat.factorial (n - j) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - j)
    have hfactor : (Nat.factorial j : ℂ) * (Nat.choose n j : ℂ) =
        (Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ) := by
      apply mul_right_cancel₀ hfac_ne
      calc
        ((Nat.factorial j : ℂ) * (Nat.choose n j : ℂ)) * (Nat.factorial (n - j) : ℂ)
            = (Nat.choose n j : ℂ) * (Nat.factorial j : ℂ) * (Nat.factorial (n - j) : ℂ) := by ring
        _ = (Nat.factorial n : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
        _ = ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
              (Nat.factorial (n - j) : ℂ) := by field_simp [hfac_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      congrArg
        (fun x : ℂ => ((-1 : ℂ) ^ j) * x * (Nat.choose k j : ℂ) * z ^ (n - j) * (star z) ^ (k - j))
        hfactor
theorem Phi_eq_PhiKappaAlpha
    {d : Nat} (kappa alpha : MultiIndex d) (z : Cd d) :
    Phi kappa alpha z = Hermite1DimdLEAN.PhiKappaAlpha kappa alpha z := by
  unfold Phi Hermite1DimdLEAN.PhiKappaAlpha
  refine Finset.prod_congr rfl ?_
  intro q hq
  exact phi1D_eq_oneDimPhi (kappa q) (alpha q) (z q)
theorem evalPkappa_eq_evalHermiteSum
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    evalPkappa kappa F = Hermite1DimdLEAN.evalHermiteSum kappa ⟨F⟩ := by
  ext z
  unfold evalPkappa Hermite1DimdLEAN.evalHermiteSum Hermite1DimdLEAN.FiniteHermiteSum.support
  refine Finset.sum_congr rfl ?_
  intro alpha halpha
  simp [Phi_eq_PhiKappaAlpha]
theorem evalPkappa_total_mass
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    (∫ z, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 := by
  let _ := hd
  have hparseval :
      Hermite1DimdLEAN.hermiteNormSq kappa ⟨F⟩ =
        Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) :=
    Hermite1DimdLEAN.finiteParseval kappa ⟨F⟩
  have hparseval' :
      (∫ z, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) =
        Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) := by
    simp only [Hermite1DimdLEAN.hermiteNormSq, Hermite1DimdLEAN.gaussianL2NormSq] at hparseval
    simp only [evalPkappa_eq_evalHermiteSum kappa F]
    exact hparseval
  rw [hparseval']
  change Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2) =
    (Real.sqrt (Finset.sum F.support (fun alpha => ‖F alpha‖ ^ 2))) ^ 2
  symm
  rw [Real.sq_sqrt]
  positivity
def partialSum
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (J : MultiIndex d) :
    Cd d -> ℂ :=
  fun z => Finset.sum (box J) fun alpha => coeffSkappa U alpha * Phi kappa alpha z
def evalPkappaL2 {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    L2Tensor d :=
  toL2 kappa (ofPkappa kappa F)
def PhiL2 {d : Nat} (kappa : MultiIndex d) (alpha : Idx d) : L2Tensor d :=
  evalPkappaL2 kappa (Finsupp.single alpha 1)
def BoxPartialSumsLocallyUniformTo
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (f : Cd d -> ℂ) : Prop :=
  TendstoLocallyUniformly (fun J : MultiIndex d => partialSum kappa U J) f Filter.atTop
def BoxPartialSumsLocallyUniformCauchy
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) : Prop :=
  (∀ K : Set (Cd d), IsCompact K ->
    UniformCauchySeqOn (fun J : MultiIndex d => partialSum kappa U J) Filter.atTop K) ∧
  BoxPartialSumsLocallyUniformTo kappa U (toFun kappa U)
def IsTensorL2Rep {d : Nat} (F : L2Tensor d) (f : Cd d -> ℂ) : Prop :=
  ∃ hf_mem : MeasureTheory.MemLp f 2 (gammaD d), hf_mem.toLp f = F
def L2BoxPartialSumsTendTo
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (F : L2Tensor d) : Prop :=
  Filter.Tendsto (fun J : MultiIndex d => evalPkappaL2 kappa (truncateFinset (box J) U))
    Filter.atTop (nhds F) ∧
  IsTensorL2Rep F (toFun kappa U)
theorem continuous_Phi
    {d : Nat} (kappa alpha : MultiIndex d) :
    Continuous (Phi kappa alpha) := by
  unfold Phi phi1D complexHermite
  continuity
theorem continuous_evalPkappa
    {d : Nat} (kappa : MultiIndex d) (F : Pkappa d kappa) :
    Continuous (evalPkappa kappa F) := by
  unfold evalPkappa
  refine continuous_finsetSum _ ?_
  intro alpha halpha
  exact continuous_const.mul (continuous_Phi kappa alpha)
theorem integrable_evalPkappa_sq
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.Integrable
      (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2) (gammaD d) := by
  by_cases hF : F = 0
  · subst hF
    simp [evalPkappa]
  · have hmeas :
        MeasureTheory.AEStronglyMeasurable (fun z : Cd d => ‖evalPkappa kappa F z‖ ^ 2)
          (gammaD d) :=
      ((continuous_evalPkappa kappa F).norm.pow 2).stronglyMeasurable.aestronglyMeasurable
    by_contra hInt
    have hundef :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = 0 :=
      MeasureTheory.integral_undef hInt
    have hmass :
        (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d) = ‖F‖ ^ 2 :=
      evalPkappa_total_mass hd kappa F
    have hnorm_ne : ‖F‖ ≠ 0 := by
      intro hnorm
      apply hF
      ext alpha
      by_contra hne
      have hmem : alpha ∈ F.support := Finsupp.mem_support_iff.mpr hne
      have hterm_pos : 0 < ‖F alpha‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
      have hle :
          ‖F alpha‖ ^ 2 <= Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) := Finset.single_le_sum
          (f := fun beta : Idx d => ‖F beta‖ ^ 2) (s := F.support) (a := alpha)
          (fun beta _ => by positivity) hmem
      have hsum_pos : 0 < Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) :=
        lt_of_lt_of_le hterm_pos hle
      change (Real.sqrt (Finset.sum F.support (fun beta => ‖F beta‖ ^ 2))) = 0 at hnorm
      have hsum_zero : Finset.sum F.support (fun beta => ‖F beta‖ ^ 2) = 0 :=
        (Real.sqrt_eq_zero (by positivity)).mp hnorm
      linarith only [hterm_pos, hle, hsum_zero]
    simp_all
theorem memLp_two_evalPkappa
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    MeasureTheory.MemLp (evalPkappa kappa F) 2 (gammaD d) := by
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (evalPkappa kappa F) (gammaD d) :=
    (continuous_evalPkappa kappa F).stronglyMeasurable.aestronglyMeasurable
  exact
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).2
      (integrable_evalPkappa_sq hd kappa F)
def phiMajorant (k n : Nat) (R : ℝ) : ℝ :=
  ((2 : ℝ) ^ k * (n + 1 : ℝ) ^ k * R ^ k * R ^ n) /
    Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))
end DimdPolyLEAN


