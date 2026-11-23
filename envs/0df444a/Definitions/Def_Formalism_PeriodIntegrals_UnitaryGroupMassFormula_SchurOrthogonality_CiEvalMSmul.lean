-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CiEvalMSmul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CiEvalMSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:02.667281+00:00
-- url     : https://prove2.me/theorems/53d1c923-27fd-48fb-9ec3-be400a348ecd
-- title:
--   Ci Eval MSmul
-- statement:
--   Definitions and structural lemmas for Ci Eval MSmul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/CiEvalMSmul.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CrRowActRowAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
noncomputable section
namespace PI.WSF
open MvPolynomial MeasureTheory Matrix
theorem entry_le_lemma {N : ℕ} {x : Matrix (Fin N) (Fin N) ℂ} (hx : x ∈ unitaryGroup (Fin N) ℂ)
    (i j : Fin N) : ‖x i j‖ ≤ 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hx) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h3 : (∑ k, Complex.normSq (x i k) : ℝ) = 1 := by
    have h4 : ((∑ k, Complex.normSq (x i k) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h]
      exact Finset.sum_congr rfl fun k _ => (Complex.mul_conj (x i k)).symm
    exact_mod_cast h4
  have h5 : Complex.normSq (x i j) ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (x i k)) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at h5
  nlinarith [norm_nonneg (x i j)]
theorem ci_compact (N : ℕ) : IsCompact (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hset : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) = {x | x * star x = 1} := by
    ext x
    exact Matrix.mem_unitaryGroup_iff
  have hclosed : IsClosed (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) := by
    rw [hset]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  have hbound : (unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) ⊆
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    intro x hx
    exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
      mem_closedBall_zero_iff.mpr (entry_le_lemma hx i j)
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset
    hclosed hbound
theorem ci_cont {N : ℕ} (p : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p := by
  unfold evalM
  exact (MvPolynomial.continuous_eval p).comp
    (continuous_pi fun v => (continuous_apply v.2).comp (continuous_apply v.1))
theorem ci_cont2 {N : ℕ} (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    Continuous fun x : Matrix (Fin N) (Fin N) ℂ => evalM x p * star (evalM x q) :=
  (ci_cont p).mul (ci_cont q).star
theorem ci_integrable {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    {f : Matrix (Fin N) (Fin N) ℂ → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨hprob, hae, -, -⟩ := hμ
  have h := hf.continuousOn.integrableOn_compact (μ := μ) (ci_compact N)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h
  exact h
theorem ci_evalM_add {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (p q : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (p + q) = evalM x p + evalM x q := by
  simp [evalM]
theorem ci_evalM_smul {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (p : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (c • p) = c * evalM x p := by
  simp [evalM]
def Aform {N : ℕ} (μ : Measure (Matrix (Fin N) (Fin N) ℂ)) (p q : MvPolynomial (Fin N × Fin N) ℂ) : ℂ :=
  ∫ x, evalM x p * star (evalM x q) ∂μ
def Alin {N : ℕ} {μ : Measure (Matrix (Fin N) (Fin N) ℂ)} (hμ : IsHaarU N μ)
    (q : MvPolynomial (Fin N × Fin N) ℂ) : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun p := Aform μ p q
  map_add' p p' := by
    unfold Aform
    rw [← integral_add (ci_integrable hμ (ci_cont2 p q)) (ci_integrable hμ (ci_cont2 p' q))]
    congr 1
    funext x
    rw [ci_evalM_add]
    ring
  map_smul' c p := by
    unfold Aform
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    rw [ci_evalM_smul]
    ring
end PI.WSF


