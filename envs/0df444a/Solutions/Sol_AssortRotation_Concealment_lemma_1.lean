-- Prove2me | solution 1 for AssortRotation.Concealment.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:09:44.980095+00:00
-- url     : https://prove2.me/submissions/4108ad85-4485-48fe-a0d8-7666d0bfe890

import Mathlib
import Definitions.Def_AssortRotation_Concealment_Model

set_option autoImplicit false

open AssortRotation.Concealment

namespace FixedUtilityProof

noncomputable def prefixSet (M k : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun i => (i : ℕ) < k)

lemma card_prefix {M k : ℕ} (hk : k ≤ M) : (prefixSet M k).card = k := by
  simp only [prefixSet, Fin.card_filter_val_lt, Nat.min_eq_right hk]

/-- Selecting every nonnegative term and no negative term dominates any selection. -/
lemma sum_le_of_signs {α : Type*} [Fintype α] (f : α → ℝ)
    (S T : Finset α) (hpos : ∀ i ∈ T, 0 ≤ f i)
    (hneg : ∀ i, i ∉ T → f i ≤ 0) :
    ∑ i ∈ S, f i ≤ ∑ i ∈ T, f i := by
  classical
  rw [← Finset.sum_ite_mem_eq S f, ← Finset.sum_ite_mem_eq T f]
  apply Finset.sum_le_sum
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
  · simp only [if_pos hS, if_pos hT, le_refl]
  · simpa only [if_pos hS, if_neg hT] using hneg i hT
  · simpa only [if_neg hS, if_pos hT] using hpos i hT
  · simp only [if_neg hS, if_neg hT, le_refl]

/-- The first `|T|` terms of an antitone sequence dominate every `T` of that size. -/
lemma sum_le_prefix {M : ℕ} (w : Fin M → ℝ) (hw : Antitone w)
    (T : Finset (Fin M)) :
    ∑ i ∈ T, w i ≤ ∑ i ∈ prefixSet M T.card, w i := by
  classical
  have hk : T.card ≤ M := by simpa using T.card_le_univ
  by_cases hlt : T.card < M
  · let b : Fin M := ⟨T.card, hlt⟩
    have hshift := sum_le_of_signs (fun i => w i - w b) T (prefixSet M T.card)
      (by
        intro i hi
        have hi' : (i : ℕ) < T.card := by simpa [prefixSet] using hi
        exact sub_nonneg.mpr (hw (show i ≤ b from le_of_lt hi')))
      (by
        intro i hi
        have hi' : T.card ≤ (i : ℕ) := by
          have : ¬ (i : ℕ) < T.card := by simpa [prefixSet] using hi
          omega
        exact sub_nonpos.mpr (hw (show b ≤ i from hi')))
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      card_prefix hk] at hshift
    linarith
  · have heq : T.card = M := by omega
    have hT : T = Finset.univ := T.eq_univ_of_card (by simpa using heq)
    have hP : prefixSet M T.card = Finset.univ := by
      ext i
      simp [prefixSet, heq, i.isLt]
    rw [hP, hT]

lemma sum_prefix_eq_sum_range {M k : ℕ} (v : ℕ → ℝ) (hk : k ≤ M) :
    ∑ i ∈ prefixSet M k, v i = ∑ j ∈ Finset.range k, v j := by
  classical
  refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    simpa [prefixSet] using hi
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    refine ⟨⟨j, lt_of_lt_of_le hjk hk⟩, ?_, rfl⟩
    simpa [prefixSet] using hjk
  · intro i hi
    rfl

lemma utility_prefix {M k : ℕ} (v : ℕ → ℝ) (p x : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (hk : k ≤ M) :
    utility v p x ((prefixSet M k).map σ.toEmbedding) =
      ∑ i ∈ prefixSet M k, (v i + x (σ i) - p (σ i)) := by
  classical
  rw [utility, Finset.card_map, card_prefix hk, Finset.sum_map,
    ← sum_prefix_eq_sum_range v hk, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.toEmbedding_apply]
  ring

end FixedUtilityProof

open FixedUtilityProof

theorem solution {M : ℕ} (v : ℕ → ℝ) (hv : MarginalUtility v) (p x : Fin M → ℝ)
    (σ : Equiv.Perm (Fin M)) (hσ : Antitone (fun i => x (σ i) - p (σ i))) (S : Finset (Fin M)) :
    utility v p x S ≤
      utility v p x
        ((Finset.univ.filter (fun j : Fin M =>
            (j : ℕ) < (Finset.univ.filter (fun i : Fin M =>
              0 ≤ v i + x (σ i) - p (σ i))).card)).map σ.toEmbedding) := by
  classical
  let w : Fin M → ℝ := fun i => x (σ i) - p (σ i)
  let a : Fin M → ℝ := fun i => v i + x (σ i) - p (σ i)
  let T : Finset (Fin M) := S.map σ.symm.toEmbedding
  let D := (Finset.univ.filter (fun i : Fin M => 0 ≤ a i)).card
  have hk : T.card ≤ M := by simpa using T.card_le_univ
  have hD : D ≤ M := by
    simpa [D] using (Finset.univ.filter (fun i : Fin M => 0 ≤ a i)).card_le_univ
  have ha : Antitone a := by
    intro i j hij
    have hvij := hv.2 (show (i : ℕ) ≤ (j : ℕ) from hij)
    have hwij := hσ hij
    dsimp [a]
    linarith
  have hmem (i : Fin M) : i ∈ prefixSet M D ↔ 0 ≤ a i := by
    simpa only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, D] using
      (Fin.lt_card_filter_univ_iff_apply_of_imp (j := i) (fun j : Fin M => 0 ≤ a j)
        (fun i j hji hi => le_trans hi (ha hji)))
  have hmax : ∑ i ∈ prefixSet M T.card, a i ≤ ∑ i ∈ prefixSet M D, a i :=
    sum_le_of_signs a _ _ (fun i hi => (hmem i).mp hi)
      (fun i hi => le_of_lt (lt_of_not_ge (fun h => hi ((hmem i).mpr h))))
  calc
    utility v p x S = (∑ i ∈ T, w i) + ∑ j ∈ Finset.range T.card, v j := by
      simp [utility, T, w]
    _ ≤ (∑ i ∈ prefixSet M T.card, w i) + ∑ j ∈ Finset.range T.card, v j :=
      add_le_add (sum_le_prefix w hσ T) le_rfl
    _ = ∑ i ∈ prefixSet M T.card, a i := by
      rw [← sum_prefix_eq_sum_range v hk, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [w, a]
      ring
    _ ≤ ∑ i ∈ prefixSet M D, a i := hmax
    _ = utility v p x ((prefixSet M D).map σ.toEmbedding) :=
      (utility_prefix v p x σ hD).symm

