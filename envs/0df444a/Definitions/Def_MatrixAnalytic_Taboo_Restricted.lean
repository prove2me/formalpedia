-- Prove2me | Definitions.Def_MatrixAnalytic_Taboo_Restricted
-- name    : MatrixAnalytic_Taboo_Restricted
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:30.360143+00:00
-- url     : https://prove2.me/theorems/fc6934cc-e5c6-457d-8260-5ac2326ce3ed
-- title:
--   The restricted (censored) process $X^T_n = X_{\tau_n}$ and the matrix $P(T) = P_T + P_{TT^c}(I - P_{T^c})^{-1}P_{T^cT}$
-- statement:
--   Let $P$ be a transition matrix on a countable state space $S$ and $T \subseteq S$, with complement $T^c = S \setminus T$. The **epochs of visits** to $T$ are
--   $$\tau_0 = \inf\{i \ge 0 : X_i \in T\}, \qquad \tau_{n+1} = \inf\{i \ge \tau_n + 1 : X_i \in T\},$$
--   and the **restricted process** is $X^T_n = X_{\tau_n}$, the state visited when the chain is for the $n$-th time in $T$ (p. 118).
--
--   1. The **law of the restricted process**: for a starting state $i$ and states $j_0, \dots, j_k$,
--   $$\mathrm P[\tau_k < \infty \;\&\; X^T_0 = j_0 \;\&\; \cdots \;\&\; X^T_k = j_k \mid X_0 = i],$$
--   the sum of the weights of the trajectories from $i$ that end in $T$ and whose successive states in $T$ (times $0$ to the end included) are exactly $j_0, \dots, j_k$.
--   2. The matrix
--   $$P(T) = P_T + P_{TT^c}(I - P_{T^c})^{-1}P_{T^cT}, \qquad P(T)_{ij} = P_{ij} + \sum_{k, l \in T^c} P_{ik}\,[(I - P_{T^c})^{-1}]_{kl}\,P_{lj} \quad (i, j \in T),$$
--   with $(I - P_{T^c})^{-1} = \sum_{\nu \ge 0} P_{T^c}^\nu$ (the convention of p. 109), and the same matrix as a real matrix indexed by the states of $T$.
--   3. For a matrix $M$ and states $j_0, j_1, \dots, j_k$, the product $M_{j_0j_1}M_{j_1j_2}\cdots M_{j_{k-1}j_k}$ (equal to $1$ when $k = 0$).
--
--   Theorem 5.3.1 says that the restricted process is a Markov chain on $T$ with transition matrix $P(T)$; the law in item 1 is what that statement is about, and the matrix in item 2 is defined by the formula only.
--
--   **Formalization Note** The law and $P(T)$ take values in `ℝ≥0∞`; `censoredKernel` reads $P(T)$ as a real matrix on the subtype of states of $T$ (via `toReal`), on which the chain notions of the mission (irreducibility, positive recurrence, stationary vector) are stated. The successive states of a trajectory in $T$ are obtained by filtering the list of its states.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 118 (epochs τ_n and the restricted process; P(T) in Theorem 5.3.1); p. 109 (convention (I − M)⁻¹ = Σ M^n)

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

namespace MatrixAnalytic.Taboo

noncomputable section

open scoped BigOperators ENNReal

/-!
The restricted (censored) process of §5.3 of Latouche & Ramaswami (p. 118) and the matrix
`P(T) = P_T + P_{TTᶜ}(I − P_{Tᶜ})⁻¹P_{TᶜT}` of Theorem 5.3.1.
-/

variable {S : Type*} [Countable S] [DecidableEq S]

/-- The matrix `P(T) = P_T + P_{TTᶜ}(I − P_{Tᶜ})⁻¹P_{TᶜT}` (p. 118), with `(I − P_{Tᶜ})⁻¹` read
by the convention of p. 109 as the series `Σ_{ν ≥ 0} P_{Tᶜ}^ν` (`seriesInv`):
`P(T)_{ij} = P_{ij} + Σ_{k, l ∈ Tᶜ} P_{ik} [(I − P_{Tᶜ})⁻¹]_{kl} P_{lj}`, entrywise in `ℝ≥0∞`.
Only entries with `i, j ∈ T` are meant. -/
def censoredMatrix (P : S → S → ℝ) (T : Set S) (i j : S) : ℝ≥0∞ :=
  ennP P i j +
    ∑' k : (Tᶜ : Set S), ∑' l : (Tᶜ : Set S),
      ennP P i k * seriesInv (ennP P) Tᶜ k l * ennP P l j

/-- The real matrix `P(T)` on the state space `T` (the subtype of states in `T`). -/
def censoredKernel (P : S → S → ℝ) (T : Set S) : T → T → ℝ :=
  fun i j => (censoredMatrix P T i j).toReal

/-- The product `M_{j₀j₁} M_{j₁j₂} ⋯ M_{j_{k-1}j_k}` of the entries of `M` along the sequence
`j₀, j₁, …, j_k` (the list `js` is `[j₁, …, j_k]`; the empty product is `1`). -/
def chainWeight (M : S → S → ℝ≥0∞) : S → List S → ℝ≥0∞
  | _, [] => 1
  | j₀, j₁ :: js => M j₀ j₁ * chainWeight M j₁ js

open Classical in
/-- The finite-dimensional law of the restricted process (p. 118). With the epochs of visits to
`T`, `τ₀ = inf{i ≥ 0 : X_i ∈ T}` and `τ_{n+1} = inf{i ≥ τ_n + 1 : X_i ∈ T}`, and the restricted
process `X^T_n = X_{τ_n}`,
`restrictedLaw P T i [j₀, …, j_k] = P[τ_k < ∞ & X^T_0 = j₀ & ⋯ & X^T_k = j_k | X_0 = i]`.
It is the sum, over the trajectories `ω_0 = i, ω_1, …, ω_n` that are in `T` at time `n` (so
`n = τ_k`) and whose successive states in `T` at times `0, …, n` are exactly `j₀, …, j_k`, of
their probabilities. -/
def restrictedLaw (P : S → S → ℝ) (T : Set S) (i : S) (js : List S) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑' ω : Fin (n + 1) → S,
    if ω 0 = i ∧ ω (Fin.last n) ∈ T ∧ (List.ofFn ω).filter (fun s => decide (s ∈ T)) = js
    then pathWeightE P ω else 0

end

end MatrixAnalytic.Taboo


