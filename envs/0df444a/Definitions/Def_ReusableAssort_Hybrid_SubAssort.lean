-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_SubAssort
-- name    : ReusableAssort_Hybrid_SubAssort
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:39.847009+00:00
-- url     : https://prove2.me/theorems/7ff7f404-47b7-4a88-969e-cdeec3369655
-- title:
--   Procedure 1, p. 13 — sub-assortment sampling as a finite distribution on subsets
-- statement:
--   Procedure 1 (Sub-assortment Sampling) takes a choice model $\phi$, an assortment $S$ with $m = |S|$ products, and target probabilities $\{p_i\}_{i \in S}$, and returns a random subset $\tilde S \subseteq S$.
--
--   For $j \in S$ let $\rho_j = p_j / \phi(S, j)$, with the convention $\rho_j = 1$ when $\phi(S, j) = 0$. Order the products as $\sigma(1), \dots, \sigma(m)$ so that $\rho_{\sigma(1)} \ge \dots \ge \rho_{\sigma(m)}$, and set
--   $$q_0 = 1 - \rho_{\sigma(1)}, \qquad q_j = \rho_{\sigma(j)} - \rho_{\sigma(j+1)} \ (1 \le j < m), \qquad q_m = \rho_{\sigma(m)} .$$
--   Sample $j^* \sim \{q_j\}_{j=0}^m$. If $j^* = 0$ return $\emptyset$; if $j^* = m$ return $S$; otherwise run the procedure again on $(\phi, S', \{\phi(S, i)\}_{i \in S'})$ with $S' = \{\sigma(1), \dots, \sigma(j^*)\}$, the $j^*$ products of largest ratio, and return its output. On $S = \emptyset$ the procedure returns $\emptyset$.
--
--   The definition records the law of the output: `subAssort φ S p U` is the probability that the procedure returns $U$. The procedure is the post-processing step of all the algorithms of the mission: it restores the choice probabilities of the products that survived discarding to their target values (Proposition 3).
--
--   **Formalization Note** The recursion is unfolded with a budget equal to $|S|$ (each recursive call is on fewer products). Ties among equal ratios are broken by increasing product index (a stable sort of $S$ listed in increasing order); the page leaves $\sigma$ arbitrary among such orders. Line 11 of the page writes $S' = \{\sigma^{-1}(j)\}_{j=1}^{j^*}$; it is read as $\{\sigma(j)\}_{j=1}^{j^*}$, which agrees with the page's proof (where $\sigma$ is the identity) and is what the induction needs. Lines 2–3 ("if $\rho_{\sigma(m)} = 1$ return $S$") are the case $q_m = 1$ of the general formula and need no separate branch.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 13, Procedure 1 (Sub-assortment Sampling)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Model

namespace ReusableAssort.Hybrid

variable {n : ℕ}

/-- The ratio `p_j / ϕ(S, j)` of Procedure 1, with the page's convention that it is `1`
when `ϕ(S, j) = 0`. -/
noncomputable def ratio (φ : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n))
    (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  if φ S j = 0 then 1 else p j / φ S j

/-- The permutation `σ` of line 1 of Procedure 1, as a list: the elements of `S` sorted by
decreasing ratio, ties broken by increasing index (a stable sort of `S` listed in
increasing order). -/
noncomputable def sortedList (φ : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n))
    (p : Fin n → ℝ) : List (Fin n) :=
  (S.sort (· ≤ ·)).mergeSort (fun a b => decide (ratio φ S p b ≤ ratio φ S p a))

/-- The probabilities `q_0, …, q_m` of line 5 of Procedure 1, with `m = |S|`:
`q_0 = 1 - ρ_{σ(1)}`, `q_j = ρ_{σ(j)} - ρ_{σ(j+1)}` (`1 ≤ j < m`), `q_m = ρ_{σ(m)}`. -/
noncomputable def qprob (φ : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n))
    (p : Fin n → ℝ) (j : ℕ) : ℝ :=
  let R := (sortedList φ S p).map (ratio φ S p)
  let m := S.card
  if j = 0 then 1 - R.getD 0 0
  else if j = m then R.getD (m - 1) 0
  else R.getD (j - 1) 0 - R.getD j 0

/-- Procedure 1 with a recursion budget `k` (any `k ≥ |S|` gives the same result): the
probability that Sub-assortment Sampling on `(φ, S, p)` returns `U`. -/
noncomputable def subAssortAux : ℕ → (Finset (Fin n) → Fin n → ℝ) → Finset (Fin n) →
    (Fin n → ℝ) → Finset (Fin n) → ℝ
  | 0, _, _, _, U => if U = ∅ then 1 else 0
  | k + 1, φ, S, p, U =>
    if S = ∅ then (if U = ∅ then 1 else 0) else
    qprob φ S p 0 * (if U = ∅ then 1 else 0)
      + qprob φ S p S.card * (if U = S then 1 else 0)
      + ∑ j ∈ Finset.Ico 1 S.card,
          qprob φ S p j * subAssortAux k φ ((sortedList φ S p).take j).toFinset (φ S) U

/-- Procedure 1 (Sub-assortment Sampling, p. 13) as a finite distribution on subsets:
`subAssort φ S p U` is the probability that the procedure, run on choice model `φ`,
assortment `S` and targets `p`, returns `U`. With probability `q_0` it returns `∅`, with
probability `q_m` it returns `S`, and with probability `q_j` (`1 ≤ j < m`) it recurses on the
`j` products of largest ratio with targets `φ(S, ·)`. -/
noncomputable def subAssort (φ : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n))
    (p : Fin n → ℝ) (U : Finset (Fin n)) : ℝ :=
  subAssortAux S.card φ S p U

end ReusableAssort.Hybrid


