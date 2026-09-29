-- Prove2me | Definitions.Def_Devaney_sigma2
-- name    : Devaney_sigma2
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T10:09:47.205253+00:00
-- url     : https://prove2.me/theorems/14e4632b-2604-4339-8056-ea2ed9afd16a
-- title:
--   The sequence space $\Sigma_2$ with Devaney's metric, and the shift map
-- statement:
--   **The sequence space (Definition 6.1).** $\Sigma_2$ is the set of one-sided infinite sequences $s = (s_0 s_1 s_2 \dots)$ with every entry $s_i \in \{0,1\}$.
--
--   **The metric (Proposition 6.2).** $\Sigma_2$ is metrized by
--
--   $$d[s,t] = \sum_{i=0}^{\infty} \frac{|s_i - t_i|}{2^{i}} .$$
--
--   The series converges, being dominated by $\sum_i 2^{-i} = 2$, and the file establishes that $d$ is a genuine metric, so Proposition 6.2 of the book is part of this definitional layer rather than a separate milestone. Two sequences are close in this metric exactly when they agree on a long initial block.
--
--   **The shift (Definition 6.4).** The shift map $\sigma : \Sigma_2 \to \Sigma_2$ forgets the first entry, $\sigma(s_0 s_1 s_2 \dots) = (s_1 s_2 s_3 \dots)$. It is a two-to-one map, and it is the model against which the quadratic family will be compared.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.6, pp. 40–41, Definition 6.1, Proposition 6.2, Definition 6.4

import Mathlib

namespace Devaney

/-- Devaney, Definition 6.1: the sequence space `Σ₂` of one-sided infinite sequences of
`0`'s and `1`'s. -/
def Sigma2 : Type := ℕ → Fin 2

namespace Sigma2

/-- The `i`-th entry of a sequence in `Σ₂`, as a real number. -/
def entry (s : Sigma2) (i : ℕ) : ℝ := ((s i : ℕ) : ℝ)

lemma entry_mem (s : Sigma2) (i : ℕ) : s.entry i = 0 ∨ s.entry i = 1 := by
  have h := (s i).isLt
  interval_cases h' : (s i : ℕ)
  · exact Or.inl (by simp [entry, h'])
  · exact Or.inr (by simp [entry, h'])

lemma abs_entry_sub_le_one (s t : Sigma2) (i : ℕ) : |s.entry i - t.entry i| ≤ 1 := by
  rcases entry_mem s i with hs | hs <;> rcases entry_mem t i with ht | ht <;>
    simp [hs, ht]

/-- Devaney, §1.6: the term `|sᵢ - tᵢ| / 2ⁱ` of the defining series of the metric on `Σ₂`. -/
noncomputable def distTerm (s t : Sigma2) (i : ℕ) : ℝ := |s.entry i - t.entry i| / 2 ^ i

lemma distTerm_nonneg (s t : Sigma2) (i : ℕ) : 0 ≤ distTerm s t i := by
  unfold distTerm
  positivity

lemma distTerm_le (s t : Sigma2) (i : ℕ) : distTerm s t i ≤ (1 / 2 : ℝ) ^ i := by
  unfold distTerm
  rw [div_pow, one_pow]
  have hpow : (0 : ℝ) < 2 ^ i := by positivity
  gcongr
  exact abs_entry_sub_le_one s t i

lemma summable_distTerm (s t : Sigma2) : Summable (distTerm s t) := by
  refine Summable.of_nonneg_of_le (distTerm_nonneg s t) (distTerm_le s t) ?_
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

/-- Devaney, §1.6: the distance `d[s,t] = ∑ᵢ |sᵢ - tᵢ| / 2ⁱ` on the sequence space. -/
noncomputable def dist' (s t : Sigma2) : ℝ := ∑' i, distTerm s t i

end Sigma2

open Sigma2 in
/-- `Σ₂` with Devaney's metric `d[s,t] = ∑ᵢ |sᵢ - tᵢ| / 2ⁱ` (Proposition 6.2). -/
noncomputable instance : MetricSpace Sigma2 where
  dist := dist'
  dist_self s := by
    simp [dist', distTerm, entry]
  dist_comm s t := by
    simp only [dist', distTerm]
    exact tsum_congr fun i => by rw [abs_sub_comm]
  dist_triangle s t u := by
    have hsum := (summable_distTerm s t).add (summable_distTerm t u)
    calc dist' s u ≤ ∑' i, (distTerm s t i + distTerm t u i) := by
          refine Summable.tsum_le_tsum ?_ (summable_distTerm s u) hsum
          intro i
          unfold distTerm
          rw [← add_div]
          have hpow : (0 : ℝ) < 2 ^ i := by positivity
          gcongr
          exact abs_sub_le _ _ _
      _ = dist' s t + dist' t u := (summable_distTerm s t).tsum_add (summable_distTerm t u)
  eq_of_dist_eq_zero := by
    intro s t h
    have hterm : ∀ i, distTerm s t i = 0 := by
      intro i
      have h1 : distTerm s t i ≤ ∑' j, distTerm s t j :=
        (summable_distTerm s t).le_tsum i fun j _ => distTerm_nonneg s t j
      have h2 : (0 : ℝ) ≤ distTerm s t i := distTerm_nonneg s t i
      have : distTerm s t i ≤ 0 := by
        rw [show (∑' j, distTerm s t j) = dist' s t from rfl, h] at h1
        exact h1
      linarith
    funext i
    have := hterm i
    unfold distTerm at this
    have h2 : |s.entry i - t.entry i| = 0 := by
      have hpow : (2 : ℝ) ^ i ≠ 0 := by positivity
      rcases div_eq_zero_iff.mp this with h | h
      · exact h
      · exact absurd h hpow
    have h3 : s.entry i = t.entry i := by
      have := abs_eq_zero.mp h2
      linarith
    have : ((s i : ℕ) : ℝ) = ((t i : ℕ) : ℝ) := h3
    exact Fin.ext (Nat.cast_injective this)

/-- Devaney, Definition 6.4: the shift map `σ(s₀s₁s₂…) = (s₁s₂s₃…)` on `Σ₂`. -/
def shift : Sigma2 → Sigma2 := fun s n => s (n + 1)

end Devaney


