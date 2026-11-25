-- Prove2me | Definitions.Def_SNumbers_KolmogorovLifting
-- name    : SNumbers_KolmogorovLifting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T02:33:46.457251+00:00
-- url     : https://prove2.me/theorems/cde980dd-51b3-517f-ba7b-20a6c45ce61c
-- title:
--   Kolmogorov Lifting
-- statement:
--   Definitions and structural lemmas for Kolmogorov Lifting, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/KolmogorovLifting.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Kolmogorov
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] Submodule.liftQL_mkQL


set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped Cardinal NNReal ENNReal
open ContinuousLinearMap
namespace SNumbers
namespace Lifting
abbrev Ball (X : Type u) [NormedAddCommGroup X] : Type u :=
  {x : X // ‖x‖ ≤ 1}
abbrev BallLp (𝕜 : Type u) [NontriviallyNormedField 𝕜] (X : Type u)
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Type u :=
  lp (fun _ : Ball X => 𝕜) 1
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
lemma summable_norm_α (α : BallLp 𝕜 X) :
    Summable (fun x : Ball X => ‖α x‖) := by
  have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
  simpa using (lp.memℓp α).summable hp1
lemma summable_norm_smul_val (α : BallLp 𝕜 X) :
    Summable (fun x : Ball X => ‖α x • (x : X)‖) :=
  (summable_norm_α α).of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => by
    rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) x.2)
lemma summable_smul_val [CompleteSpace X] (α : BallLp 𝕜 X) :
    Summable (fun x : Ball X => α x • (x : X)) :=
  (summable_norm_smul_val α).of_norm
noncomputable def Q [CompleteSpace X] : BallLp 𝕜 X →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := fun α => ∑' x : Ball X, α x • (x : X)
      map_add' := fun α β => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul_val α).tsum_add (summable_smul_val β)
      map_smul' := fun c α => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul]
        exact (summable_smul_val α).tsum_const_smul c }
    1 (fun α => by
      rw [one_mul]
      refine (norm_tsum_le_tsum_norm (summable_norm_smul_val α)).trans ?_
      refine (Summable.tsum_le_tsum (fun x => by
        rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) x.2)
        (summable_norm_smul_val α) (summable_norm_α α)).trans_eq ?_
      have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
      rw [lp.norm_eq_tsum_rpow hp1 α, show (1 : ℝ≥0∞).toReal = 1 from by norm_num]
      simp [Real.rpow_one])
variable [CompleteSpace X]
@[simp] lemma Q_apply (α : BallLp 𝕜 X) :
    (Q : BallLp 𝕜 X →L[𝕜] X) α = ∑' x : Ball X, α x • (x : X) := rfl
noncomputable def kolmogorovNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  approximationNumber (S.comp (Q : BallLp 𝕜 X →L[𝕜] X)) n
section S1a
variable {𝕜 : Type u} [DenselyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end S1a
section S3
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
omit [CompleteSpace 𝕜] [CompleteSpace W] [CompleteSpace X] in
/-- For `w ∈ B_W`, `c⁻¹ • A w ∈ B_X` (provided `‖A‖ ≤ ‖c‖`, `c ≠ 0`). -/
lemma Aw_in_ball {A : W →L[𝕜] X} {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (w : Ball W) : ‖c⁻¹ • A (w : W)‖ ≤ 1 := by
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc_ne
  rw [norm_smul, norm_inv, inv_mul_le_iff₀ hc_pos, mul_one]
  refine (A.le_opNorm _).trans ?_
  rw [mul_comm]
  exact (mul_le_of_le_one_left (norm_nonneg _) w.2).trans hc
noncomputable def liftBasis {A : W →L[𝕜] X} {c : 𝕜}
    (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) (w : Ball W) : BallLp 𝕜 X :=
  letI : DecidableEq (Ball X) := Classical.decEq _
  lp.single 1 (⟨c⁻¹ • A (w : W), Aw_in_ball hc hc_ne w⟩ : Ball X) c
omit [CompleteSpace 𝕜] [CompleteSpace W] [CompleteSpace X] in
lemma norm_liftBasis {A : W →L[𝕜] X} {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0)
    (w : Ball W) : ‖liftBasis hc hc_ne w‖ = ‖c‖ := by
  let := Classical.decEq (Ball X)
  exact lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1) _ _
omit [CompleteSpace 𝕜] [CompleteSpace W] [CompleteSpace X] in
lemma summable_norm_smul_liftBasis {A : W →L[𝕜] X} {c : 𝕜}
    (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) (α : BallLp 𝕜 W) :
    Summable (fun w : Ball W => ‖α w • liftBasis hc hc_ne w‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => ?_)
    ((summable_norm_α α).mul_right ‖c‖)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_liftBasis hc hc_ne w).le (norm_nonneg _)
omit [CompleteSpace W] [CompleteSpace X] in
lemma summable_smul_liftBasis {A : W →L[𝕜] X} {c : 𝕜}
    (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) (α : BallLp 𝕜 W) :
    Summable (fun w : Ball W => α w • liftBasis hc hc_ne w) :=
  Summable.of_norm_bounded ((summable_norm_α α).mul_right ‖c‖) (fun w => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_liftBasis hc hc_ne w).le (norm_nonneg _))
noncomputable def liftA (A : W →L[𝕜] X) {c : 𝕜} (hc : ‖A‖ ≤ ‖c‖) (hc_ne : c ≠ 0) :
    BallLp 𝕜 W →L[𝕜] BallLp 𝕜 X :=
  LinearMap.mkContinuous
    { toFun := fun α => ∑' w : Ball W, α w • liftBasis hc hc_ne w
      map_add' := fun α β => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul_liftBasis hc hc_ne α).tsum_add
              (summable_smul_liftBasis hc hc_ne β)
      map_smul' := fun k α => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul]
        exact (summable_smul_liftBasis hc hc_ne α).tsum_const_smul k }
    ‖c‖ (fun α => by
      refine (norm_tsum_le_tsum_norm (summable_norm_smul_liftBasis hc hc_ne α)).trans ?_
      refine (Summable.tsum_le_tsum (fun w => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_liftBasis hc hc_ne w).le (norm_nonneg _))
        (summable_norm_smul_liftBasis hc hc_ne α)
        ((summable_norm_α α).mul_right ‖c‖)).trans_eq ?_
      rw [tsum_mul_right]
      have hp1 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by norm_num
      rw [lp.norm_eq_tsum_rpow hp1 α, show (1 : ℝ≥0∞).toReal = 1 from by norm_num]
      simp [Real.rpow_one, mul_comm])
end S3
section S5
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
end S5
section S5b
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
end S5b
section Pietsch
variable {𝕜 : Type u} [DenselyNormedField 𝕜] [CompleteSpace 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
end Pietsch
end Lifting
end SNumbers


