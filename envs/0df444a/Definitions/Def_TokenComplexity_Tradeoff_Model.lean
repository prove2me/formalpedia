-- Prove2me | Definitions.Def_TokenComplexity_Tradeoff_Model
-- name    : TokenComplexity_Tradeoff_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:29.494126+00:00
-- url     : https://prove2.me/theorems/716fbe06-0a44-4581-9108-01f9e1dd76cd
-- title:
--   §3–§4, pp. 5–7, 14 — n questions under a prompt family: token counts, correctness, accuracy, average length, α*(T), T*(α), F_n, E_n, A*, Assumption 1, t_T, q_α
-- statement:
--   Fix one large language model and a dataset of $n$ questions, indexed by $i \in \{1,\dots,n\}$, together with a family of chain-of-thought prompts $P$. Under prompt $P$ the model produces, for question $i$, a chain of thought $X_i$ of **token length** $t_i(P) = t(X_i) \in \mathbb N$, and a **correctness indicator** $a_i(P) \in \{0,1\}$.
--
--   1. The **accuracy** and the **average token length** of a prompt are
--   $$\mathrm{Acc}(P) = \frac1n \sum_{i=1}^n a_i(P), \qquad \bar t(P) = \frac1n \sum_{i=1}^n t_i(P).$$
--   2. The **optimal accuracy at average budget $T$** and the **minimal average length for accuracy $\alpha$** are
--   $$\alpha^*(T) = \max_P \{\mathrm{Acc}(P) : \bar t(P) \le T\}, \qquad T^*(\alpha) = \min_P \{\bar t(P) : \mathrm{Acc}(P) \ge \alpha\},$$
--   understood as attained maxima and minima: "$\alpha^*(T) = v$" means that $v$ is the accuracy of some prompt of average length at most $T$ and no such prompt does better, and dually for $T^*$.
--   3. **Assumption 1 (token complexity hypothesis).** There are **token complexities** $\tau_i \in \mathbb N \cup \{\infty\}$ such that for every prompt $P$ and question $i$,
--   $$a_i(P) = \mathbf 1\{t_i(P) \ge \tau_i\}.$$
--   The value $\tau_i = \infty$ means that question $i$ is never solved.
--   4. **Rich prompts** (the second hypothesis of Theorem 1): for every vector of token counts $(t_i)_{i=1}^n \in \mathbb N^n$ some prompt $P$ has $t_i(P) = t_i$ for all $i$.
--   5. The empirical quantities of the token complexities, counting finite $\tau_i$ only:
--   $$F_n(t) = \frac1n \sum_{i=1}^n \mathbf 1\{\tau_i \le t\}, \qquad E_n(t) = \frac1n \sum_{i=1}^n \tau_i \mathbf 1\{\tau_i \le t\}, \qquad A^* = \frac1n \sum_{i=1}^n \mathbf 1\{\tau_i < \infty\}.$$
--   6. The finite token complexities sorted increasingly, $\tau_{(1)} \le \tau_{(2)} \le \cdots$, and the sum of the $m$ smallest of them.
--   7. The thresholds of Theorem 1 in corrected form: $t_T$ is the largest finite $\tau_j$ with $E_n(\tau_j) \le T$ (no question lies below $t_T$ if there is none), and $q_\alpha$ is the smallest finite $\tau_j$ with $F_n(\tau_j) \ge \alpha$ (no question lies below $q_\alpha$ if there is none). The two right-hand sides of Theorem 1 are then
--   $$\frac1n \sum_{i=1}^n \mathbf 1\{\tau_i \le t_T\}, \qquad \frac1n \sum_{i=1}^n \tau_i \mathbf 1\{\tau_i \le q_\alpha\},$$
--   both summing over finite $\tau_i$ only.
--
--   These objects carry every statement of the mission: Assumption 1 and richness link the prompt-level optima $\alpha^*$, $T^*$ to the token complexities, and $F_n$, $E_n$, $t_T$, $q_\alpha$ express the answer.
--
--   **Formalization Note** The paper indexes everything by the LLM $\pi$; one LLM is fixed and the superscript dropped, as the proof in Appendix D does. Questions are `Fin n`; prompts form an arbitrary type, and each (prompt, question) pair yields one deterministic chain of thought. Token complexities take values in `ℕ∞` (Assumption 1 says $\tau_i \in \mathbb N$, but p. 6 and Corollary 1 use $\tau_i = \infty$); $\tau_i \le t$ with $\tau_i = \infty$ is false for every finite $t$, and all sums and counts over $\tau$ filter on $\tau_i \neq \infty$ before converting to a natural number. Correctness is `Bool`. Averages are real numbers with division by $n$. The optima are `IsGreatest`/`IsLeast` predicates, not `sSup`/`sInf`, so an empty or unbounded feasible set never yields a junk value. The page's $t_T \equiv \inf\{t : E_n(t) = t\}$ does not involve $T$, and its $q_\alpha = \sup\{t : F_n(t) \le \alpha\}$ is not the α-quantile; the definitions here follow the proof's description of $t_T$ ("the highest value of τ that the LLM puts into the knapsack", p. 14) and the text's description of $q_\alpha$ ("the α-quantile of the empirical distribution", p. 7). They are given as membership predicates "$\tau_i \le t_T$" and "$\tau_i \le q_\alpha$", so the empty cases have no junk value.
-- source:
--   Lee, Che, Peng, How Well do LLMs Compress Their Own Chain-of-Thought? A Token Complexity Approach, arXiv:2503.01141v2, pp. 5–7 and 14, §3 (notation, Assumption 1), eq. (2), §4 eqs. (3)–(4), definitions of F_n, E_n, t_T, q_α (p. 7), A* (p. 8, Corollary 1), sorted order τ_(1) < … < τ_(n) (Appendix D, p. 14)

import Mathlib

namespace TokenComplexity.Tradeoff

open Finset

/-- One LLM answering `n` questions under a family of chain-of-thought prompts (§3, p. 5):
`len P i` is the token length `t(X_{i,P}) ∈ ℕ` of the chain of thought produced for question `i`
under prompt `P`, and `correct P i` is the correctness indicator `a_i(X_{i,P}) ∈ {0, 1}`. -/
structure Benchmark (n : ℕ) (Prompt : Type) where
  len : Prompt → Fin n → ℕ
  correct : Prompt → Fin n → Bool

variable {n : ℕ} {Prompt : Type}

/-- Accuracy `Acc(P) = (1/n) ∑ᵢ aᵢ(Xᵢ)` of prompt `P` (eq. (2), p. 6). -/
noncomputable def accuracy (B : Benchmark n Prompt) (P : Prompt) : ℝ :=
  ((univ.filter (fun i => B.correct P i = true)).card : ℝ) / n

/-- Average token length `t̄(P) = (1/n) ∑ᵢ t(Xᵢ)` of prompt `P` (p. 7). -/
noncomputable def avgLen (B : Benchmark n Prompt) (P : Prompt) : ℝ :=
  (∑ i, (B.len P i : ℝ)) / n

/-- Assumption 1 (token complexity hypothesis, p. 5): for every prompt `P` and question `i`, the
answer is correct iff the token length is at least the token complexity `τ i`.
`τ i = ⊤` encodes `τ_i = ∞` (p. 6): the question is never solved. -/
def TokenComplexityHyp (B : Benchmark n Prompt) (τ : Fin n → ℕ∞) : Prop :=
  ∀ P i, B.correct P i = true ↔ τ i ≤ (B.len P i : ℕ∞)

/-- The second hypothesis of Theorem 1 (p. 7): every vector of token counts is realized by some
prompt. -/
def Rich (B : Benchmark n Prompt) : Prop :=
  ∀ t : Fin n → ℕ, ∃ P, ∀ i, B.len P i = t i

/-- `α*(T) = v` (eq. (3), p. 7): `v` is the maximum accuracy over prompts with average token
length at most `T` (an attained maximum). -/
def IsOptAccuracy (B : Benchmark n Prompt) (T v : ℝ) : Prop :=
  IsGreatest {a | ∃ P, avgLen B P ≤ T ∧ accuracy B P = a} v

/-- `T*(α) = v` (eq. (4), p. 7): `v` is the minimum average token length over prompts with
accuracy at least `α` (an attained minimum). -/
def IsMinAvgLen (B : Benchmark n Prompt) (α v : ℝ) : Prop :=
  IsLeast {L | ∃ P, α ≤ accuracy B P ∧ avgLen B P = L} v

/-- Empirical CDF of the token complexities, `F_n(t) = (1/n) ∑ᵢ 1{τᵢ ≤ t}` (p. 7);
infinite token complexities never count. -/
noncomputable def Fn (τ : Fin n → ℕ∞) (t : ℝ) : ℝ :=
  ((univ.filter (fun i => τ i ≠ ⊤ ∧ ((τ i).toNat : ℝ) ≤ t)).card : ℝ) / n

/-- `E_n(t) = (1/n) ∑ᵢ τᵢ 1{τᵢ ≤ t}` (p. 7); infinite token complexities never count. -/
noncomputable def En (τ : Fin n → ℕ∞) (t : ℝ) : ℝ :=
  (∑ i ∈ univ.filter (fun i => τ i ≠ ⊤ ∧ ((τ i).toNat : ℝ) ≤ t), ((τ i).toNat : ℝ)) / n

/-- `A* = (1/n) ∑ᵢ 1{τᵢ < ∞}`, the maximum possible accuracy (p. 8). -/
noncomputable def Astar (τ : Fin n → ℕ∞) : ℝ :=
  ((univ.filter (fun i => τ i ≠ ⊤)).card : ℝ) / n

/-- The finite token complexities, sorted increasingly: `τ_(1) ≤ τ_(2) ≤ …` (Appendix D, p. 14). -/
def sortedFinite (τ : Fin n → ℕ∞) : List ℕ :=
  ((univ.filter (fun i => τ i ≠ ⊤)).val.map (fun i => (τ i).toNat)).sort (· ≤ ·)

/-- The sum of the `m` smallest finite token complexities. -/
def prefixCost (τ : Fin n → ℕ∞) (m : ℕ) : ℕ :=
  ((sortedFinite τ).take m).sum

/-- "`τ_i ≤ t_T`" for the corrected threshold `t_T` = the largest finite token complexity `τ_j` with
`E_n(τ_j) ≤ T` (the proof's "highest value of τ that the LLM puts into the knapsack", p. 14). False
for every `i` when no finite `τ_j` has `E_n(τ_j) ≤ T`. -/
def BelowTT (τ : Fin n → ℕ∞) (T : ℝ) (i : Fin n) : Prop :=
  ∃ j, τ j ≠ ⊤ ∧ En τ ((τ j).toNat : ℝ) ≤ T ∧ τ i ≤ τ j

/-- "`τ_i ≤ q_α`" for the corrected quantile `q_α` = the smallest finite token complexity `τ_j` with
`F_n(τ_j) ≥ α` (the α-quantile of the empirical distribution, p. 7). False for every `i` when no
finite `τ_j` has `F_n(τ_j) ≥ α`. -/
def BelowQα (τ : Fin n → ℕ∞) (α : ℝ) (i : Fin n) : Prop :=
  ∃ j, τ j ≠ ⊤ ∧ α ≤ Fn τ ((τ j).toNat : ℝ) ∧
    (∀ k, τ k ≠ ⊤ → α ≤ Fn τ ((τ k).toNat : ℝ) → τ j ≤ τ k) ∧ τ i ≤ τ j

open Classical in
/-- Right-hand side of eq. (5), corrected: `(1/n) ∑ᵢ 1{τᵢ ≤ t_T}`, finite `τᵢ` only. -/
noncomputable def alphaClosed (τ : Fin n → ℕ∞) (T : ℝ) : ℝ :=
  ((univ.filter (fun i => τ i ≠ ⊤ ∧ BelowTT τ T i)).card : ℝ) / n

open Classical in
/-- Right-hand side of eq. (6), corrected: `(1/n) ∑ᵢ τᵢ 1{τᵢ ≤ q_α}`, finite `τᵢ` only. -/
noncomputable def TClosed (τ : Fin n → ℕ∞) (α : ℝ) : ℝ :=
  (∑ i ∈ univ.filter (fun i => τ i ≠ ⊤ ∧ BelowQα τ α i), ((τ i).toNat : ℝ)) / n

end TokenComplexity.Tradeoff


