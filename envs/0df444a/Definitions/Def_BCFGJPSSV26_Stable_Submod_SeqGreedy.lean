-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy
-- name    : BCFGJPSSV26_Stable_Submod_SeqGreedy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:28.343208+00:00
-- url     : https://prove2.me/theorems/33eb7de3-121e-4a2e-8928-2fbc30ad8536
-- title:
--   BCFGJPSSV26.Stable.Submod.SeqGreedy — A sequential discrete continuous greedy
-- statement:
--   This is module `BCFGJPSSV26.Stable.Submod.SeqGreedy` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The submodular step of [BCFGJPSSV26b, Lemma 5.1] uses, instead of the continuous greedy of
--   Calinescu–Chekuri–Pál–Vondrák, a deterministic sequential greedy: maximize a monotone submodular
--   `f` with `f ∅ = 0` subject to one element from each of `ρ` parts `P_j`.
--
--   The algorithm keeps a list `L_j` per part. In each of `T` rounds `t`, for `j = 1, …, ρ` in turn,
--   it appends to `L_j` an element `e ∈ P_j` maximizing the total marginal gain
--   `∑_{U ∈ [T]^ρ} (f(Q⁻ʲ(U) ∪ {e}) - f(Q⁻ʲ(U)))`, where
--   `Q⁻ʲ(U) = {L_{j'}[U_{j'}] : j' < j, U_{j'} ≤ t} ∪ {L_{j'}[U_{j'}] : j' > j, U_{j'} < t}`
--   (`BCFGJPSSV26.Stable.greedyQ`, `BCFGJPSSV26.Stable.IsSeqGreedy`). Then for every choice
--   `o_j ∈ P_j`, the average over `U ∈ [T]^ρ` of `f({L_j[U_j]})` is at least
--   `(1 - (T/(T + 1))^T) f({o_j})` (`BCFGJPSSV26.Stable.seqGreedy_bound`), and
--   `(T/(T+1))^T ≤ (1 + 1/T)/e` (`BCFGJPSSV26.Stable.pow_le_one_add_div_exp`).
--
--   Proof: with `a_t` the average of `f` on the sets `{L_j[U_j] : U_j < t}`, the rule and
--   submodularity give `a_{t+1} - a_t ≥ (f(O) - a_{t+1})/T`.
--
--   **Contents.** The module is published as a whole: 18 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.seqGreedy_bound` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Submod/SeqGreedy.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Supermodular
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Submod.SeqGreedy` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# A sequential discrete continuous greedy

The submodular step of [BCFGJPSSV26b, Lemma 5.1] uses, instead of the continuous greedy of
Calinescu–Chekuri–Pál–Vondrák, a deterministic sequential greedy: maximize a monotone submodular
`f` with `f ∅ = 0` subject to one element from each of `ρ` parts `P_j`.

The algorithm keeps a list `L_j` per part. In each of `T` rounds `t`, for `j = 1, …, ρ` in turn,
it appends to `L_j` an element `e ∈ P_j` maximizing the total marginal gain
`∑_{U ∈ [T]^ρ} (f(Q⁻ʲ(U) ∪ {e}) - f(Q⁻ʲ(U)))`, where
`Q⁻ʲ(U) = {L_{j'}[U_{j'}] : j' < j, U_{j'} ≤ t} ∪ {L_{j'}[U_{j'}] : j' > j, U_{j'} < t}`
(`BCFGJPSSV26.Stable.greedyQ`, `BCFGJPSSV26.Stable.IsSeqGreedy`). Then for every choice
`o_j ∈ P_j`, the average over `U ∈ [T]^ρ` of `f({L_j[U_j]})` is at least
`(1 - (T/(T + 1))^T) f({o_j})` (`BCFGJPSSV26.Stable.seqGreedy_bound`), and
`(T/(T+1))^T ≤ (1 + 1/T)/e` (`BCFGJPSSV26.Stable.pow_le_one_add_div_exp`).

Proof: with `a_t` the average of `f` on the sets `{L_j[U_j] : U_j < t}`, the rule and
submodularity give `a_{t+1} - a_t ≥ (f(O) - a_{t+1})/T`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {U : Type*} [DecidableEq U] {ρ T : ℕ}

/-- `Q⁻ʲ_t(V)`: the elements chosen by the other parts at round `t`, as seen by part `j`. -/
def greedyQ (Lst : Fin ρ → Fin T → U) (j : Fin ρ) (t : Fin T) (V : Fin ρ → Fin T) : Finset U :=
  ((univ.filter fun j' ↦ j' < j ∧ V j' ≤ t) ∪ (univ.filter fun j' ↦ j < j' ∧ V j' < t)).image
    fun j' ↦ Lst j' (V j')

/-- **The greedy rule**: every `L_j[t]` is in `P_j` and maximizes the total marginal gain. -/
def IsSeqGreedy (f : Finset U → ℝ) (P : Fin ρ → Finset U) (Lst : Fin ρ → Fin T → U) : Prop :=
  ∀ j t, Lst j t ∈ P j ∧ ∀ e ∈ P j,
    ∑ V : Fin ρ → Fin T, (f (insert e (greedyQ Lst j t V)) - f (greedyQ Lst j t V)) ≤
      ∑ V : Fin ρ → Fin T, (f (insert (Lst j t) (greedyQ Lst j t V)) - f (greedyQ Lst j t V))

/-! ### The proof of the guarantee -/

/-- The elements chosen at the rounds below `t`. -/
private def roundSet (Lst : Fin ρ → Fin T → U) (V : Fin ρ → Fin T) (t : ℕ) : Finset U :=
  (univ.filter fun j' ↦ (V j' : ℕ) < t).image fun j' ↦ Lst j' (V j')

/-- The parts below `j` at rounds up to `t`, the others at rounds below `t`. -/
private def midIdx (V : Fin ρ → Fin T) (t j : ℕ) : Finset (Fin ρ) :=
  univ.filter fun j' ↦ ((j' : ℕ) < j ∧ (V j' : ℕ) ≤ t) ∨ (j ≤ (j' : ℕ) ∧ (V j' : ℕ) < t)

/-- The elements of the intermediate state `(t, j)`. -/
private def midSet (Lst : Fin ρ → Fin T → U) (V : Fin ρ → Fin T) (t j : ℕ) : Finset U :=
  (midIdx V t j).image fun j' ↦ Lst j' (V j')

private theorem midSet_zero (Lst : Fin ρ → Fin T → U) (V : Fin ρ → Fin T) (t : ℕ) :
    midSet Lst V t 0 = roundSet Lst V t := by
  unfold midSet midIdx roundSet
  simp

private theorem midSet_rho (Lst : Fin ρ → Fin T → U) (V : Fin ρ → Fin T) (t : ℕ) :
    midSet Lst V t ρ = roundSet Lst V (t + 1) := by
  unfold midSet midIdx roundSet
  congr 1
  ext j'
  simp only [mem_filter, mem_univ, true_and]
  have := j'.2
  omega

private theorem midIdx_succ_of_ne (V : Fin ρ → Fin T) {t j : ℕ} (hj : j < ρ)
    (hV : (V ⟨j, hj⟩ : ℕ) ≠ t) : midIdx V t (j + 1) = midIdx V t j := by
  unfold midIdx
  ext j'
  simp only [mem_filter, mem_univ, true_and]
  rcases eq_or_ne j' ⟨j, hj⟩ with rfl | hne
  · simp only
    omega
  · have : (j' : ℕ) ≠ j := fun h ↦ hne (Fin.ext h)
    omega

private theorem midIdx_eq (V : Fin ρ → Fin T) {t j : ℕ} (hj : j < ρ) (ht : t < T)
    (hV : V ⟨j, hj⟩ = ⟨t, ht⟩) :
    midIdx V t j = (univ.filter fun j' ↦ j' < ⟨j, hj⟩ ∧ V j' ≤ ⟨t, ht⟩) ∪
      (univ.filter fun j' ↦ ⟨j, hj⟩ < j' ∧ V j' < ⟨t, ht⟩) := by
  have hV' : (V ⟨j, hj⟩ : ℕ) = t := by rw [hV]
  unfold midIdx
  ext j'
  simp only [mem_filter, mem_univ, true_and, mem_union, Fin.lt_def, Fin.le_def]
  rcases eq_or_ne j' ⟨j, hj⟩ with rfl | hne
  · simp only
    omega
  · have : (j' : ℕ) ≠ j := fun h ↦ hne (Fin.ext h)
    omega

private theorem midIdx_succ_eq (V : Fin ρ → Fin T) {t j : ℕ} (hj : j < ρ) (ht : t < T)
    (hV : V ⟨j, hj⟩ = ⟨t, ht⟩) :
    midIdx V t (j + 1) = insert ⟨j, hj⟩ ((univ.filter fun j' ↦ j' < ⟨j, hj⟩ ∧ V j' ≤ ⟨t, ht⟩) ∪
      (univ.filter fun j' ↦ ⟨j, hj⟩ < j' ∧ V j' < ⟨t, ht⟩)) := by
  have hV' : (V ⟨j, hj⟩ : ℕ) = t := by rw [hV]
  unfold midIdx
  ext j'
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_insert, Fin.lt_def, Fin.le_def]
  rcases eq_or_ne j' ⟨j, hj⟩ with rfl | hne
  · simp only [true_or, iff_true]
    omega
  · have : (j' : ℕ) ≠ j := fun h ↦ hne (Fin.ext h)
    have : j' ≠ ⟨j, hj⟩ := hne
    simp only [this, false_or]
    omega

/-- Between the states `(t, j)` and `(t, j + 1)` only the tuples with `V j = t` change. -/
private theorem midSet_step (f : Finset U → ℝ) (Lst : Fin ρ → Fin T → U) (V : Fin ρ → Fin T)
    {t j : ℕ} (hj : j < ρ) (ht : t < T) :
    f (midSet Lst V t (j + 1)) - f (midSet Lst V t j) =
      if V ⟨j, hj⟩ = ⟨t, ht⟩ then
        f (insert (Lst ⟨j, hj⟩ ⟨t, ht⟩) (greedyQ Lst ⟨j, hj⟩ ⟨t, ht⟩ V)) -
          f (greedyQ Lst ⟨j, hj⟩ ⟨t, ht⟩ V)
      else 0 := by
  split_ifs with hV
  · unfold midSet greedyQ
    rw [midIdx_succ_eq V hj ht hV, midIdx_eq V hj ht hV, image_insert, hV]
  · have hV' : (V ⟨j, hj⟩ : ℕ) ≠ t := fun h ↦ hV (Fin.ext h)
    unfold midSet
    rw [midIdx_succ_of_ne V hj hV', sub_self]

/-- `greedyQ` does not depend on the coordinate `j`. -/
private theorem greedyQ_update (Lst : Fin ρ → Fin T → U) (j : Fin ρ) (t : Fin T) (V : Fin ρ → Fin T)
    (a : Fin T) : greedyQ Lst j t (Function.update V j a) = greedyQ Lst j t V := by
  unfold greedyQ
  have key : ∀ V' : Fin ρ → Fin T, (∀ j', j' ≠ j → V' j' = V j') →
      ((univ.filter fun j' ↦ j' < j ∧ V' j' ≤ t) ∪ (univ.filter fun j' ↦ j < j' ∧ V' j' < t)).image
        (fun j' ↦ Lst j' (V' j')) =
      ((univ.filter fun j' ↦ j' < j ∧ V j' ≤ t) ∪ (univ.filter fun j' ↦ j < j' ∧ V j' < t)).image
        (fun j' ↦ Lst j' (V j')) := by
    intro V' hV'
    have hs : ((univ.filter fun j' ↦ j' < j ∧ V' j' ≤ t) ∪
        (univ.filter fun j' ↦ j < j' ∧ V' j' < t)) =
        ((univ.filter fun j' ↦ j' < j ∧ V j' ≤ t) ∪
        (univ.filter fun j' ↦ j < j' ∧ V j' < t)) := by
      ext j'
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases eq_or_ne j' j with rfl | hne
      · simp
      · rw [hV' j' hne]
    rw [hs]
    refine image_congr fun j' hj' ↦ ?_
    simp only [coe_union, coe_filter, mem_univ, true_and, Set.mem_union,
      Set.mem_ofPred_eq] at hj'
    have hne : j' ≠ j := by
      rcases hj' with h | h
      · exact ne_of_lt h.1
      · exact ne_of_gt h.1
    simp only [hV' j' hne]
  exact key _ fun j' hj' ↦ Function.update_of_ne hj' a V

/-- Summing over the tuples with `V j = t` gives a `1/T` fraction of the full sum, for a
function not depending on `V j`. -/
private theorem sum_ite_coord (jj : Fin ρ) (tt : Fin T) (h : (Fin ρ → Fin T) → ℝ)
    (hh : ∀ V a, h (Function.update V jj a) = h V) :
    (T : ℝ) * ∑ V : Fin ρ → Fin T, (if V jj = tt then h V else 0) =
      ∑ V : Fin ρ → Fin T, h V := by
  have h1 : ∑ V : Fin ρ → Fin T, h V =
      ∑ s : Fin T, ∑ V : Fin ρ → Fin T, (if V jj = s then h V else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun V _ ↦ ?_
    rw [sum_ite_eq]
    simp
  have h2 : ∀ s : Fin T, ∑ V : Fin ρ → Fin T, (if V jj = s then h V else 0) =
      ∑ V : Fin ρ → Fin T, (if V jj = tt then h V else 0) := by
    intro s
    have hinv : Function.Involutive
        (fun V : Fin ρ → Fin T ↦ Function.update V jj (Equiv.swap s tt (V jj))) := by
      intro V
      simp
    rw [← Equiv.sum_comp (hinv.toPerm _)]
    refine sum_congr rfl fun V _ ↦ ?_
    simp only [Function.Involutive.coe_toPerm, Function.update_self, hh]
    congr 1
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  rw [h1, sum_congr rfl fun s _ ↦ h2 s, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Telescoping submodularity. -/
private theorem submod_union_le {f : Finset U → ℝ} (hsub : IsSubmod f) (R : Finset U)
    (o : Fin ρ → U) (B : Finset (Fin ρ)) :
    f (R ∪ B.image o) - f R ≤ ∑ j ∈ B, (f (insert (o j) R) - f R) := by
  induction B using Finset.induction_on with
  | empty => simp
  | insert b B hb ih =>
    rw [image_insert, union_insert, sum_insert hb]
    have := hsub R (R ∪ B.image o) subset_union_left (o b)
    linarith

/-- The sum of `f` over the tuples, on the elements of the rounds below `t`. -/
private noncomputable def roundSum (f : Finset U → ℝ) (Lst : Fin ρ → Fin T → U) (t : ℕ) : ℝ :=
  ∑ V : Fin ρ → Fin T, f (roundSet Lst V t)

/-- **One round of the greedy**: `T (a_{t+1} - a_t) ≥ T^ρ f(O) - a_{t+1}`. -/
private theorem round_step {f : Finset U → ℝ} (hmono : IsMonoF f) (hsub : IsSubmod f)
    {P : Fin ρ → Finset U} {Lst : Fin ρ → Fin T → U}
    (hG : IsSeqGreedy f P Lst) (o : Fin ρ → U) (ho : ∀ j, o j ∈ P j) {t : ℕ} (ht : t < T) :
    (T : ℝ) ^ ρ * f (univ.image o) - roundSum f Lst (t + 1) ≤
      (T : ℝ) * (roundSum f Lst (t + 1) - roundSum f Lst t) := by
  set D : ℕ → ℝ := fun j ↦ ∑ V : Fin ρ → Fin T, f (midSet Lst V t j) with hD
  have hdiff : roundSum f Lst (t + 1) - roundSum f Lst t = ∑ j : Fin ρ, (D (j + 1) - D j) := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ D (j + 1) - D j), sum_range_sub]
    simp only [hD, midSet_zero, midSet_rho, roundSum]
  set R : (Fin ρ → Fin T) → Finset U := fun V ↦ roundSet Lst V (t + 1) with hR
  have hj : ∀ jj : Fin ρ, ∑ V : Fin ρ → Fin T, (f (insert (o jj) (R V)) - f (R V)) ≤
      (T : ℝ) * (D (jj + 1) - D jj) := by
    intro jj
    obtain ⟨j, hj⟩ := jj
    have hstep : D (j + 1) - D j = ∑ V : Fin ρ → Fin T,
        (if V ⟨j, hj⟩ = ⟨t, ht⟩ then
          f (insert (Lst ⟨j, hj⟩ ⟨t, ht⟩) (greedyQ Lst ⟨j, hj⟩ ⟨t, ht⟩ V)) -
            f (greedyQ Lst ⟨j, hj⟩ ⟨t, ht⟩ V) else 0) := by
      simp only [hD]
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun V _ ↦ midSet_step f Lst V hj ht
    simp only
    rw [hstep, sum_ite_coord ⟨j, hj⟩ ⟨t, ht⟩ _ (fun V a ↦ by rw [greedyQ_update])]
    refine le_trans ?_ ((hG ⟨j, hj⟩ ⟨t, ht⟩).2 (o ⟨j, hj⟩) (ho _))
    refine sum_le_sum fun V _ ↦ hsub _ _ ?_ _
    unfold greedyQ
    simp only [hR, roundSet]
    refine image_subset_image fun j' hj' ↦ ?_
    simp only [mem_union, mem_filter, mem_univ, true_and, Fin.le_def, Fin.lt_def] at hj' ⊢
    omega
  have hsum : ∑ V : Fin ρ → Fin T, (f (univ.image o) - f (R V)) ≤
      ∑ V : Fin ρ → Fin T, ∑ jj : Fin ρ, (f (insert (o jj) (R V)) - f (R V)) := by
    refine sum_le_sum fun V _ ↦ ?_
    have h1 := submod_union_le hsub (R V) o univ
    have h2 := hmono (univ.image o) (R V ∪ univ.image o) subset_union_right
    linarith
  have hconst : ∑ V : Fin ρ → Fin T, (f (univ.image o) - f (R V)) =
      (T : ℝ) ^ ρ * f (univ.image o) - roundSum f Lst (t + 1) := by
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rfl
  rw [hdiff, mul_sum, ← hconst]
  refine hsum.trans ?_
  rw [sum_comm]
  exact sum_le_sum fun jj _ ↦ hj jj

/-- `(T/(T + 1))^T ≤ (1 + 1/T)/e`, since `(1 + 1/T)^(T + 1) ≥ e`. -/
theorem pow_le_one_add_div_exp {T : ℕ} (hT : 0 < T) :
    ((T : ℝ) / (T + 1)) ^ T ≤ (1 + 1 / T) / Real.exp 1 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : Real.exp (1 / (T + 1)) ≤ 1 + 1 / T := by
    have h := Real.add_one_le_exp (-(1 / ((T : ℝ) + 1)))
    have hpos : (0 : ℝ) < -(1 / ((T : ℝ) + 1)) + 1 := by
      rw [neg_add_eq_sub, sub_pos, div_lt_one (by linarith)]
      linarith
    have he : Real.exp (1 / (T + 1)) = 1 / Real.exp (-(1 / ((T : ℝ) + 1))) := by
      rw [Real.exp_neg]
      simp
    rw [he, div_le_iff₀ (Real.exp_pos _)]
    calc (1 : ℝ) = (1 + 1 / T) * (-(1 / ((T : ℝ) + 1)) + 1) := by field_simp; ring
      _ ≤ (1 + 1 / T) * Real.exp (-(1 / ((T : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left h; positivity
  have h2 : Real.exp 1 ≤ (1 + 1 / T) ^ (T + 1) := by
    have : Real.exp 1 = Real.exp (1 / (T + 1)) ^ (T + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 _
  rw [le_div_iff₀ (Real.exp_pos _)]
  calc ((T : ℝ) / (T + 1)) ^ T * Real.exp 1 ≤ ((T : ℝ) / (T + 1)) ^ T * (1 + 1 / T) ^ (T + 1) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((T : ℝ) / (T + 1) * (1 + 1 / T)) ^ T * (1 + 1 / T) := by rw [pow_succ, mul_pow]; ring
    _ = 1 + 1 / T := by
        have : (T : ℝ) / (T + 1) * (1 + 1 / T) = 1 := by field_simp
        rw [this, one_pow, one_mul]

/-- `(T/(T + 1))^T ≥ 1/e`, since `(1 + 1/T)^T ≤ e`. -/
theorem exp_inv_le_pow {T : ℕ} (hT : 0 < T) : 1 / Real.exp 1 ≤ ((T : ℝ) / (T + 1)) ^ T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : (1 + 1 / (T : ℝ)) ^ T ≤ Real.exp 1 := by
    have : Real.exp 1 = Real.exp (1 / T) ^ T := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [this]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have := Real.add_one_le_exp (1 / (T : ℝ))
    linarith
  have h2 : ((T : ℝ) / (T + 1)) ^ T = 1 / (1 + 1 / (T : ℝ)) ^ T := by
    rw [one_div, ← inv_pow]; congr 1; field_simp
  rw [h2]
  exact one_div_le_one_div_of_le (by positivity) h1

end BCFGJPSSV26.Stable


