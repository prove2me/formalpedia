-- Prove2me | Definitions.Def_CompOT_Auction_Defs
-- name    : CompOT_Auction_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:21.949001+00:00
-- url     : https://prove2.me/theorems/05cb9ad8-4cfe-4ccc-89f6-8c179faf1b4c
-- title:
--   §3.7, pp. 419–420 — the auction algorithm: states (S, ξ, g), ε-complementary slackness, the update (3.9) and terminated runs
-- statement:
--   This module fixes the objects of the auction algorithm for the optimal assignment problem (§3.7 of Peyré and Cuturi).
--
--   Let $n\ge 1$, write $[\![n]\!]=\{1,\dots,n\}$, and let $\mathbf C\in\mathbb R^{n\times n}$ be a cost matrix; $\mathbf C_{i,j}$ is the cost of assigning point $i$ to object $j$.
--
--   1. **Assignment cost.** For a map $\sigma:[\![n]\!]\to[\![n]\!]$, $\sum_i \mathbf C_{i,\sigma_i}$.
--   2. **$\bar{\mathbf C}$-transform** (§3.2, p. 403). For a dual vector $\mathbf g\in\mathbb R^n$, $(\mathbf g^{\bar{\mathbf C}})_i=\min_j \mathbf C_{i,j}-\mathbf g_j$.
--   3. **Dual feasibility** (2.21). $(\mathbf f,\mathbf g)\in R(\mathbf C)$ iff $\mathbf f_i+\mathbf g_j\le \mathbf C_{i,j}$ for all $i,j$.
--   4. **Sup norm.** $\|\mathbf C\|_\infty=\max_{i,j}|\mathbf C_{i,j}|$.
--   5. **State.** A triplet $(S,\xi,\mathbf g)$: a set $S\subseteq[\![n]\!]$ of assigned points, a partial assignment vector $\xi$ (only its values on $S$ matter) and a dual vector (price vector) $\mathbf g$ indexed by the objects.
--   6. **ε-complementary slackness** (property (a), p. 419). For $\varepsilon\in\mathbb R$,
--   $$
--   \forall i\in S,\qquad \mathbf C_{i,\xi_i}-\mathbf g_{\xi_i}\le \varepsilon+\min_j\big(\mathbf C_{i,j}-\mathbf g_j\big).
--   $$
--   7. **One iteration** ((3.9) and step 2, p. 420). Pick a point $i\notin S$, an index $j^1_i\in\operatorname{argmin}_j \mathbf C_{i,j}-\mathbf g_j$ and an index $j^2_i\ne j^1_i$ in $\operatorname{argmin}_{j\ne j^1_i}\mathbf C_{i,j}-\mathbf g_j$. Then
--   $$
--   \mathbf g_{j^1_i}\leftarrow \mathbf C_{i,j^1_i}-\big(\mathbf C_{i,j^2_i}-\mathbf g_{j^2_i}\big)-\varepsilon,
--   $$
--   the other entries of $\mathbf g$ are unchanged; the point $i'\in S$ with $\xi_{i'}=j^1_i$, if any, is removed from $S$; finally $\xi_i=j^1_i$ and $i$ is added to $S$.
--   8. **Runs.** A run of $T$ iterations starts from $S=\emptyset$ and $\mathbf g=0_n$, and each of its first $T$ transitions is an iteration as in item 7. It is **terminated** if $S=[\![n]\!]$ after the $T$-th iteration.
--
--   These definitions are the vocabulary of Propositions 3.7–3.9: the algorithm maintains ε-complementary slackness, and on termination $\xi$ is an assignment whose cost is within $n\varepsilon$ of the optimum.
--
--   **Formalization Note** $[\![n]\!]$ is `Fin n` (0-based). The book's argmin and second argmin may have ties; an iteration allows any admissible choice of $i$, $j^1_i$ and $j^2_i$, so a run is a predicate on a sequence of states rather than a function. Since an iteration needs a point $i\notin S$, no iteration follows a state with $S=[\![n]\!]$, matching "terminates when $S=[\![n]\!]$". In the initial state $\xi$ is arbitrary (the book's "empty partial assignment vector"): it is never read before being set. $\min_j$ is Lean's infimum over the finite nonempty index set. The assignment cost is the unnormalized sum used in the proof of Proposition 3.9, not the $\frac1n$-normalized objective (2.2).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.7, pp. 419–420 (properties (a)–(c), (3.9), Algorithmic properties); §3.2, p. 403 (C̄-transform); (2.21), p. 382

import Mathlib

namespace CompOT.Auction

/-- The (unnormalized) cost `∑ᵢ C_{i,σ_i}` of an assignment `σ`, as in the proof of
Proposition 3.9, p. 422 (`t⋆ = ∑ C_{i,σ_i}`). The objective (2.2) is this sum divided by `n`. -/
def assignmentCost {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → Fin n) : ℝ :=
  ∑ i, C i (σ i)

/-- The `C̄`-transform of §3.2, p. 403: `(g^{C̄})_i = min_j C_{i,j} − g_j`. -/
noncomputable def cbarTransform {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ⨅ j, (C i j - g j)

/-- Dual feasibility `(f, g) ∈ R(C)` of (2.21), p. 382, for a square cost matrix:
`f_i + g_j ≤ C_{i,j}` for all `i, j`. -/
def DualFeasible {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (f g : Fin n → ℝ) : Prop :=
  ∀ i j, f i + g j ≤ C i j

/-- The sup norm `‖C‖∞ = max_{i,j} |C_{i,j}|` used in Proposition 3.8, p. 421. -/
noncomputable def supNorm {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ i, ⨆ j, |C i j|

/-- The triplet `(S, ξ, g)` of the auction algorithm, p. 419: the set `S ⊆ ⟦n⟧` of assigned
points, the partial assignment vector `ξ` (meaningful on `S` only) and the dual vector `g`
(indexed by the objects `j`). -/
structure AuctionState (n : ℕ) where
  S : Finset (Fin n)
  ξ : Fin n → Fin n
  g : Fin n → ℝ

/-- ε-complementary slackness, property (a), p. 419:
`∀ i ∈ S, C_{i,ξ_i} − g_{ξ_i} ≤ ε + min_j (C_{i,j} − g_j)`. -/
noncomputable def EpsCS {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (s : AuctionState n) :
    Prop :=
  ∀ i ∈ s.S, C i (s.ξ i) - s.g (s.ξ i) ≤ ε + ⨅ j, (C i j - s.g j)

/-- One iteration of the auction algorithm, (3.9) and step 2, p. 420: some unassigned
`i ∉ S` with a lowest adjusted cost index `j¹ ∈ argmin_j C_{i,j} − g_j` and a second lowest
`j² ∈ argmin_{j ≠ j¹} C_{i,j} − g_j` (ties: any such choice) updates
`g_{j¹} ← C_{i,j¹} − (C_{i,j²} − g_{j²}) − ε`, removes from `S` the index `i'` with
`ξ_{i'} = j¹` (if any), sets `ξ_i = j¹` and adds `i` to `S`. -/
def AuctionStep {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (s s' : AuctionState n) :
    Prop :=
  ∃ i, i ∉ s.S ∧ ∃ j₁ j₂ : Fin n, j₂ ≠ j₁ ∧
    (∀ j, C i j₁ - s.g j₁ ≤ C i j - s.g j) ∧
    (∀ j, j ≠ j₁ → C i j₂ - s.g j₂ ≤ C i j - s.g j) ∧
    s'.g = Function.update s.g j₁ (C i j₁ - (C i j₂ - s.g j₂) - ε) ∧
    s'.S = insert i (s.S.filter (fun i' => s.ξ i' ≠ j₁)) ∧
    s'.ξ = Function.update s.ξ i j₁

/-- The first `T` iterations of the auction algorithm, p. 420: the algorithm starts from
`S = ∅` (no assignment; `ξ` is then irrelevant) and `g = 0ₙ`, and every iteration `t < T` is an
`AuctionStep`. A step requires an unassigned index, so no step follows a state with `S = ⟦n⟧`. -/
def IsAuctionPrefix {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (s : ℕ → AuctionState n)
    (T : ℕ) : Prop :=
  (s 0).S = ∅ ∧ (s 0).g = 0 ∧ ∀ t < T, AuctionStep C ε (s t) (s (t + 1))

/-- A terminated run of the auction algorithm, p. 420: a run of `T` iterations that has reached
`S = ⟦n⟧` at iteration `T` (the algorithm "terminates when `S = ⟦n⟧`"). -/
def IsAuctionRun {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (s : ℕ → AuctionState n)
    (T : ℕ) : Prop :=
  IsAuctionPrefix C ε s T ∧ (s T).S = Finset.univ

end CompOT.Auction


