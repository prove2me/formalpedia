-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_jumpMatrix
-- name    : ProcessingNetworks_MArP_jumpMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:10.993821+00:00
-- url     : https://prove2.me/theorems/84a6cb33-d57e-4dee-b9b1-6be0e26b7097
-- title:
--   The jump matrix $G$ of a generator (eq. (D.3))
-- statement:
--   The **jump matrix** $G$ of a generator $\Lambda$ with exit rates $\lambda$ is
--   $$
--   G_{ij}=\begin{cases}\Lambda_{ij}/\lambda(i)&j\ne i,\\ 0&j=i.\end{cases}
--   $$
--   It is a stochastic matrix, the transition matrix of the embedded jump chain of the continuous-time Markov chain with generator $\Lambda$.
--
--   **Formalization Note** Each row is a `PMF`, and the definition carries the proof that the row sums to $1$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), eq. (D.3), p.288 (PDF p.304)

import Mathlib
import Definitions.Def_ProcessingNetworks_MArP_IsGenerator
import Definitions.Def_ProcessingNetworks_MArP_exitRate

open Classical

namespace ProcessingNetworks.MArP

/-- The jump matrix `G` of a generator `Λ`, eq. (D.3) (Dai & Harrison, Processing Networks,
pre-publication draft 2020-4-2, p.288, PDF p.304): `G_ij = Λ_ij / λ(i)` for `j ≠ i` and `G_ii = 0`.
"This is a stochastic matrix", so row `i` is a `PMF`; the proof is the book's (D.1) and (D.2). -/
noncomputable def jumpMatrix {S : Type*} {Λ : S → S → ℝ} (hΛ : IsGenerator Λ) (i : S) : PMF S :=
  ⟨fun j => ENNReal.ofReal (if j = i then 0 else Λ i j / exitRate Λ i), by
    have hpos : 0 < exitRate Λ i := hΛ.exit_pos i
    have hs : HasSum (fun j : {j // j ≠ i} => Λ i j) (exitRate Λ i) := by
      have h := (hΛ.summable_offDiag i).hasSum
      have e : ∑' j : {j // j ≠ i}, Λ i j = exitRate Λ i := by
        simp [exitRate, hΛ.diag_eq i]
      rwa [e] at h
    have hs2 : HasSum (({j | j ≠ i} : Set S).indicator (fun j => Λ i j)) (exitRate Λ i) :=
      hasSum_subtype_iff_indicator.1 hs
    have hfun : (fun j => ({j | j ≠ i} : Set S).indicator (fun j => Λ i j) j / exitRate Λ i) =
        fun j => if j = i then 0 else Λ i j / exitRate Λ i := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    have hs3 : HasSum (fun j => if j = i then 0 else Λ i j / exitRate Λ i) 1 := by
      have h := hs2.div_const (exitRate Λ i)
      rwa [div_self hpos.ne', hfun] at h
    have hnn : ∀ j, 0 ≤ (if j = i then 0 else Λ i j / exitRate Λ i) := by
      intro j
      by_cases hj : j = i
      · simp [hj]
      · simpa [hj] using div_nonneg (hΛ.offDiag_nonneg i j (Ne.symm hj)) hpos.le
    have ht := ENNReal.ofReal_tsum_of_nonneg hnn hs3.summable
    rw [hs3.tsum_eq, ENNReal.ofReal_one] at ht
    rw [ht]
    exact ENNReal.summable.hasSum⟩

end ProcessingNetworks.MArP


