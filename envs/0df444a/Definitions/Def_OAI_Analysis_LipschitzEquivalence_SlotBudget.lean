-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
-- name    : OAI_Analysis_LipschitzEquivalence_SlotBudget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:33:26.44742+00:00
-- url     : https://prove2.me/theorems/f5cb1300-a0d1-43e2-868d-7383d0535467
-- title:
--   Error terms of slot rotations controlled by the radial budget
-- statement:
--   Estimates for perturbations of the frozen isometry on the slot domain $\mathcal D=\mathcal H\oplus_2\ell^2$, using the radii $\rho_n(x)$ and local energies $a_n(x)^2$.
--
--   1. **Velocity budget.** If vectors $d_n\in E_n$ satisfy $\|d_n\|\le\gamma(\rho_n(x))$ whenever $\rho_n(x)>0$, then
--   $$
--   \sum_na_n(x)^2\|d_n\|^2\le c^2=10^{-4}.
--   $$
--   2. **Square-summable families.** A family $f_n\in E_n$ with $\|f_n\|^2\le b_n$ for a summable $b$ defines an element of $\mathcal H$ of squared norm at most $\sum b_n$.
--   3. **Coefficient estimates.** For unit vectors $w_n$, the interleaved coefficient in slot $n$ has square at most $\|u_{\lfloor n/2\rfloor}\|^2+|v_{\lfloor n/2\rfloor}|^2$, and its difference from $\langle w_n,u_n\rangle$ has square at most $4a_n(x)^2$.
--   4. **Slot error.** The error element combining $(\text{coefficient}-\langle w_n,u_n\rangle)\,d_n$ with the interleaved correction of $(\langle d_n,u_n\rangle)_n$ has norm at most $4c$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/SlotBudget.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SlotBudget.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget

namespace OAI

universe uE

noncomputable section

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
open RadialBudget
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem velocity_budget (x : SlotDomain E) (d : ∀ n, E n)
    (hd : ∀ n, 0 < radius n x → ‖d n‖ ≤ gamma (radius n x)) :
    Summable (fun n => aSq x n * ‖d n‖^2) ∧
      (∑' n, aSq x n * ‖d n‖^2) ≤ c^2 := by
  have hm (n : ℕ) : aSq x n * ‖d n‖^2 ≤ aSq x n * gamma (radius n x)^2 := by
    by_cases hr : 0 < radius n x
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hd n hr) 2) (aSq_nonneg x n)
    · have hz : radius n x = 0 := le_antisymm (le_of_not_gt hr) (radius_nonneg n x)
      have ha := radius_step n x
      have haz : aSq x n = 0 := by rw [hz] at ha; nlinarith [aSq_nonneg x n, sq_nonneg (radius (n+1) x)]
      simp [haz]
  have hb := budget (fun n => radius_nonneg n x) (radius_antitone x)
  simp_rw [← radius_step] at hb
  have hs := Summable.of_nonneg_of_le (fun n => mul_nonneg (aSq_nonneg x n) (sq_nonneg _)) hm hb.1
  exact ⟨hs, (hs.tsum_le_tsum hm hb.1).trans hb.2⟩

def ofSqBound (f : ∀ n, E n) {b : ℕ → ℝ} (hb : Summable b)
    (hf : ∀ n, ‖f n‖^2 ≤ b n) : HilbertSum E :=
  ⟨f, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact Summable.of_nonneg_of_le (fun n => sq_nonneg _) hf hb)⟩

omit [∀ i, InnerProductSpace ℝ (E i)] in
@[simp] theorem ofSqBound_apply (f : ∀ n, E n) {b : ℕ → ℝ} (hb : Summable b)
    (hf : ∀ n, ‖f n‖^2 ≤ b n) (n : ℕ) : ofSqBound f hb hf n = f n := rfl

omit [∀ i, InnerProductSpace ℝ (E i)] in
theorem norm_ofSqBound_sq_le (f : ∀ n, E n) {b : ℕ → ℝ} (hb : Summable b)
    (hf : ∀ n, ‖f n‖^2 ≤ b n) : ‖ofSqBound f hb hf‖^2 ≤ ∑' n, b n := by
  rw [norm_sq_tsum]
  exact (summable_norm_sq (ofSqBound f hb hf)).tsum_le_tsum hf hb

variable (w : ∀ n, E n) (hw : ∀ n, ‖w n‖ = 1)

theorem interleave_coordinate_sq (x : SlotDomain E) (n : ℕ) :
    ‖interleaveRaw x.snd (coeff w hw x.fst) n‖^2 ≤
      ‖x.fst (n/2)‖^2 + ‖x.snd (n/2)‖^2 := by
  rcases Equiv.natSumNatEquivNat.surjective n with ⟨i, rfl⟩
  rcases i with m | m
  · change ‖interleaveRaw x.snd (coeff w hw x.fst) (2*m)‖^2 ≤ _
    rw [interleaveRaw_even]
    change ‖x.snd m‖^2 ≤ ‖x.fst ((2*m)/2)‖^2 + ‖x.snd ((2*m)/2)‖^2
    rw [Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    nlinarith [sq_nonneg ‖x.fst m‖]
  · change ‖interleaveRaw x.snd (coeff w hw x.fst) (2*m+1)‖^2 ≤ _
    rw [interleaveRaw_odd]
    have hd : (2*m+1)/2 = m := by omega
    change ‖⟪w m, x.fst m⟫_ℝ‖^2 ≤ ‖x.fst ((2*m+1)/2)‖^2 + ‖x.snd ((2*m+1)/2)‖^2
    rw [hd]
    have hn : ‖⟪w m, x.fst m⟫_ℝ‖ ≤ ‖x.fst m‖ := by
      simpa [hw] using norm_inner_le_norm (𝕜 := ℝ) (w m) (x.fst m)
    have := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg ‖x.snd m‖]

theorem residual_coefficient_sq (x : SlotDomain E) (n : ℕ) :
    ‖interleaveRaw x.snd (coeff w hw x.fst) n - ⟪w n, x.fst n⟫_ℝ‖^2 ≤ 4 * aSq x n := by
  have hC := interleave_coordinate_sq w hw x n
  have ha : ‖⟪w n, x.fst n⟫_ℝ‖ ≤ ‖x.fst n‖ := by
    simpa [hw] using norm_inner_le_norm (𝕜 := ℝ) (w n) (x.fst n)
  have ha2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hdiff := norm_sub_le (interleaveRaw x.snd (coeff w hw x.fst) n) ⟪w n, x.fst n⟫_ℝ
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hdiff 2
  unfold aSq
  nlinarith [sq_nonneg (‖interleaveRaw x.snd (coeff w hw x.fst) n‖ - ‖⟪w n, x.fst n⟫_ℝ‖),
    sq_nonneg ‖x.fst n‖, sq_nonneg ‖x.fst (n/2)‖, sq_nonneg ‖x.snd (n/2)‖]

theorem first_error_sq (x : SlotDomain E) (d : ∀ n, E n) (n : ℕ) :
    ‖(interleaveRaw x.snd (coeff w hw x.fst) n - ⟪w n, x.fst n⟫_ℝ) • d n‖^2 ≤
      4 * (aSq x n * ‖d n‖^2) := by
  rw [norm_smul, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_right (residual_coefficient_sq w hw x n) (sq_nonneg ‖d n‖)]

omit w hw in
theorem inner_error_sq (x : SlotDomain E) (d : ∀ n, E n) (n : ℕ) :
    ‖⟪d n, x.fst n⟫_ℝ‖^2 ≤ aSq x n * ‖d n‖^2 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (d n) (x.fst n)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at h2
  have ha : ‖x.fst n‖^2 ≤ aSq x n := by
    unfold aSq
    nlinarith [sq_nonneg ‖x.fst (n/2)‖, sq_nonneg ‖x.snd (n/2)‖]
  nlinarith [mul_le_mul_of_nonneg_left ha (sq_nonneg ‖d n‖)]

def slotError (x : SlotDomain E) (d : ∀ n, E n)
    (hd : ∀ n, 0 < radius n x → ‖d n‖ ≤ gamma (radius n x)) : HilbertSum E :=
  let hb := (velocity_budget x d hd).1
  let f := ofSqBound (fun n =>
    (interleaveRaw x.snd (coeff w hw x.fst) n - ⟪w n, x.fst n⟫_ℝ) • d n)
    (hb.mul_left 4) (first_error_sq w hw x d)
  let a := ofSqBound (E := fun _ => ℝ) (fun n => ⟪d n, x.fst n⟫_ℝ) hb (inner_error_sq x d)
  f + embed w hw (interleave (WithLp.toLp 2 (0, a)) - a)

theorem norm_slotError (x : SlotDomain E) (d : ∀ n, E n)
    (hd : ∀ n, 0 < radius n x → ‖d n‖ ≤ gamma (radius n x)) : ‖slotError w hw x d hd‖ ≤ 4*c := by
  let hb := (velocity_budget x d hd).1
  let f := ofSqBound (fun n =>
    (interleaveRaw x.snd (coeff w hw x.fst) n - ⟪w n, x.fst n⟫_ℝ) • d n)
    (hb.mul_left 4) (first_error_sq w hw x d)
  let a := ofSqBound (E := fun _ => ℝ) (fun n => ⟪d n, x.fst n⟫_ℝ) hb (inner_error_sq x d)
  have hf : ‖f‖ ≤ 2*c := by
    have h := norm_ofSqBound_sq_le _ (hb.mul_left 4) (first_error_sq w hw x d)
    rw [tsum_mul_left] at h
    have hh := (velocity_budget x d hd).2
    change ‖f‖^2 ≤ _ at h
    nlinarith [norm_nonneg f, c_pos]
  have ha : ‖a‖ ≤ c := by
    have h := norm_ofSqBound_sq_le _ hb (inner_error_sq x d)
    have hh := (velocity_budget x d hd).2
    change ‖a‖^2 ≤ _ at h
    nlinarith [norm_nonneg a, c_pos]
  have hi : ‖interleave (WithLp.toLp 2 (0, a))‖ = ‖a‖ := by
    rw [interleave.norm_map]
    simp
  change ‖f + embed w hw (interleave (WithLp.toLp 2 (0, a)) - a)‖ ≤ _
  calc
    _ ≤ ‖f‖ + ‖embed w hw (interleave (WithLp.toLp 2 (0, a)) - a)‖ := norm_add_le _ _
    _ ≤ ‖f‖ + (‖interleave (WithLp.toLp 2 (0, a))‖ + ‖a‖) := by
      rw [(embed w hw).norm_map]
      exact add_le_add_right (norm_sub_le _ _) _
    _ ≤ 4*c := by rw [hi]; linarith

end LipschitzCounterexample.HilbertSlots

end

end OAI


