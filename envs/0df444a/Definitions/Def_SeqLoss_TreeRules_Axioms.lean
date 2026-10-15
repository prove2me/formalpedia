-- Prove2me | Definitions.Def_SeqLoss_TreeRules_Axioms
-- name    : SeqLoss_TreeRules_Axioms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:31.803469+00:00
-- url     : https://prove2.me/theorems/7a3d23b6-e796-4c3d-880f-e264da73e2a1
-- title:
--   pp. 11–12, 16–17 — tree additivity (Axiom 5), tree zero truncation (Axiom 6), population monotonicity and merging proofness on e_n
-- statement:
--   The four axioms of Theorem 4, for a rule $\varphi$ on loss trees (notation of the Setting file).
--
--   1. **Tree additivity** (Axiom 5). For each tree $T$ and losses $\ell,\ell'$,
--   $$\varphi_i(T,\ell)+\varphi_i(T,\ell')=\varphi_i(T,\ell+\ell')\qquad\text{for each } i\in N(T).$$
--
--   2. **Tree zero truncation** (Axiom 6). For each tree $T$, loss $\ell$ and edge $e$ such that $T\cup\{e\}$ is a tree, $e$ runs from a vertex of $T$ to a new leaf (its head is not a vertex of $T$), and $\ell(e)=0$,
--   $$\varphi_i(T,\ell)=\varphi_i(T\cup\{e\},\ell)\qquad\text{for each } i\in N(T).$$
--
--   3. **Population monotonicity** (Axiom 3, on the elementary tree problems $e_n=(T_n,\ell_n)$). For each $n$, each $1\le j<n$ and each $1\le i\le j<k\le n$,
--   $$\varphi_i(e_n)\ge\varphi_i(e_{n+1})\quad\text{and}\quad\varphi_k(e_n)\ge\varphi_{k+1}(e_{n+1}).$$
--
--   4. **Merging proofness** (Axiom 4). For each $i\in\{1,2\}$,
--   $$\varphi_i(e_3)+\varphi_{i+1}(e_3)\le\varphi_i(e_2).$$
--
--   The paper states Axioms 3 and 4 for the linear model and notes (p. 17) that, with $e_n\equiv(T_n,\ell_n)$, they "extend immediately to the new setting".
--
--   **Formalization Note** Two readings differ from the printed text, both following the paper's own intent. (a) Axiom 6 is stated with the extra condition that the head of $e$ is not a vertex of $T$: the sentence before the axiom says "the zero-loss edge $e$ is from a vertex of $T$ to a leaf of $T\cup\{e\}$". Read literally, the axiom would also allow an edge from a new vertex into the old root, which moves the root; the fixed-fraction rules with $\lambda<1$ violate that literal version, so Theorem 4 would fail. (b) Axiom 3 is printed with "$1<j<n$"; the range $1\le j<n$ is used, as the paper's own consequences and proofs require (with $1<j$, Theorem 1 is false). Every axiom quantifies only over trees, non-negative losses and agents in $N(T)$.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), p. 11 (Axiom 3), p. 12 (Axiom 4), p. 16 (Axioms 5–6), p. 17 (e_n ≡ (T_n, ℓ_n))

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting

namespace SeqLoss.TreeRules

/-- Axiom 5 (Tree additivity, p. 16): for each tree `T` and losses `ℓ, ℓ'`,
`φ(T, ℓ) + φ(T, ℓ') = φ(T, ℓ + ℓ')`, coordinatewise on the agents `N(T)`. -/
def TreeAdditive (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) : Prop :=
  ∀ T, IsTree T → ∀ ℓ ℓ', IsTreeLoss ℓ → IsTreeLoss ℓ' →
    ∀ i ∈ N T, φ T ℓ i + φ T ℓ' i = φ T (ℓ + ℓ') i

/-- Axiom 6 (Tree zero truncation, p. 16), in the reading of the sentence before it: the zero-loss
edge `e` runs from a vertex of `T` to a leaf of `T ∪ {e}` (so `e.2 ∉ V(T)`). For each tree `T`,
loss `ℓ`, edge `e` with `T ∪ {e}` a tree, `e.2 ∉ V(T)` and `ℓ(e) = 0`, and `i ∈ N(T)`,
`φ_i(T, ℓ) = φ_i(T ∪ {e}, ℓ)`. -/
def TreeZeroTruncation (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) : Prop :=
  ∀ T, IsTree T → ∀ ℓ, IsTreeLoss ℓ → ∀ e : ℕ × ℕ, IsTree (insert e T) → e.2 ∉ V T →
    ℓ e = 0 → ∀ i ∈ N T, φ T ℓ i = φ (insert e T) ℓ i

/-- Axiom 3 (Population monotonicity, p. 11) on the elementary tree problems
`e_n ≡ (T_n, ℓ_n)` (p. 17), with the range `1 ≤ j < n` (the page prints `1 < j < n`): for each `n`,
`1 ≤ j < n` and `1 ≤ i ≤ j < k ≤ n`, `φ_i(e_n) ≥ φ_i(e_{n+1})` and `φ_k(e_n) ≥ φ_{k+1}(e_{n+1})`. -/
def TreePopulationMonotone (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) : Prop :=
  ∀ n j i k : ℕ, 1 ≤ j → j < n → 1 ≤ i → i ≤ j → j < k → k ≤ n →
    φ (treeChain (n + 1)) (chainLoss (n + 1)) i ≤ φ (treeChain n) (chainLoss n) i ∧
    φ (treeChain (n + 1)) (chainLoss (n + 1)) (k + 1) ≤ φ (treeChain n) (chainLoss n) k

/-- Axiom 4 (Merging proofness, p. 12) on the elementary tree problems (p. 17): for each
`i ∈ {1, 2}`, `φ_i(e_3) + φ_{i+1}(e_3) ≤ φ_i(e_2)`. -/
def TreeMergingProof (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) : Prop :=
  ∀ i ∈ ({1, 2} : Finset ℕ),
    φ (treeChain 3) (chainLoss 3) i + φ (treeChain 3) (chainLoss 3) (i + 1) ≤
      φ (treeChain 2) (chainLoss 2) i

end SeqLoss.TreeRules


