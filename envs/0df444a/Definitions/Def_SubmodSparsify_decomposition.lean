-- Prove2me | Definitions.Def_SubmodSparsify_decomposition
-- name    : SubmodSparsify_decomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:18.799371+00:00
-- url     : https://prove2.me/theorems/a1ee1d66-4fa1-4a9b-962b-642b22d4c1f8
-- title:
--   Algorithm 2 — Decomposition, Recover and FindMinimizer, with a call counter
-- statement:
--   A model of **Algorithm 2** of the paper, which computes the decomposition (14)–(15) by submodular minimization.
--
--   - **FindMinimizer$(h, t)$** computes $\mu := \min_{C \subseteq E}\{h(C) - t|C|\}$, starts from $Q = \emptyset$ and, for each $v \in E$ in turn, adds $v$ to $Q$ whenever $\min_{Q \cup \{v\} \subseteq C \subseteq E}\{h(C) - t|C|\} = \mu$; it returns $Q$.
--   - **Recover$(h, A, B)$** returns $(A)$ if $A = B$; otherwise it sets $t := \frac{h(B) - h(A)}{|B| - |A|}$ and $C := $ FindMinimizer$(h, t)$, returns $(A, B)$ if $C = B$, and otherwise concatenates Recover$(h, A, C)$ and Recover$(h, C, B)$, keeping one copy of $C$.
--   - **Decomposition$(E, (h_i))$** sets $h := \sum_i h_i$, $P_0 :=$ FindMinimizer$(h, 0)$, $(P_0, \dots, P_L) :=$ Recover$(h, P_0, E)$, and for $j = 1, \dots, L$, $B_j := P_j \setminus P_{j-1}$, $\tau_j := \frac{h(P_j) - h(P_{j-1})}{|B_j|}$; it returns $s_i := \sum_{j=1}^L \frac{h_i(P_j) - h_i(P_{j-1})}{\tau_j}$.
--
--   The model returns the chain it computed, the shares, and the number of calls to FindMinimizer, so that Claim 4.3 can be stated about it.
--
--   **Formalization Note** The loop order of FindMinimizer, which the paper leaves open, is an argument: a list `ord` enumerating $E$. Minima are infima over the finite types $\{C : Q \subseteq C \subseteq E\}$, and the test $\mu' = \mu$ is exact equality of reals. Recover carries a fuel argument (Decomposition passes $|E| + 1$, more than the recursion depth $L \le |E|$ of the paper's analysis); with fuel $0$ it returns the junk pair $([A, B], 0)$.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Algorithm 2, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SubmodSparsify_chain

namespace SubmodSparsify

/-!
# Algorithm 2 (Decomposition, Recover, FindMinimizer), p.22

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Algorithm 2, p.22.

A Lean model of the three procedures of Algorithm 2, with a counter of the calls to
FindMinimizer.

**Formalization Note.**
* FindMinimizer (lines 23–33) loops over `v ∈ E` in an order the paper leaves open; the model
  takes the order as a list `ord` (the claims quantify over every duplicate-free enumeration of
  `E`). The minima of lines 24 and 27 are infima over the finite subtypes
  `{C | Q ⊆ C ⊆ E}` (nonempty whenever `Q ⊆ E`); the test `µ′ = µ` is exact real equality.
* Recover (lines 12–22) is a recursion whose termination the paper derives from Lemma 4.2; the
  model carries a fuel argument (`Decomposition` passes `|E| + 1`, more than the recursion depth
  `L ≤ |E|` of the paper's analysis). With fuel `0` it returns the junk pair `([A, B], 0)`.
  Line 21's "concatenate chains, keeping one copy of C" is `r₁ ++ r₂.tail`. The second
  component of the result counts the calls to FindMinimizer made by the call.
* Decomposition (lines 1–11): `P₀` by one call of FindMinimizer at `t = 0`, the chain by
  `Recover(h, P₀, E)`, then `B_j`, `τ_j`, `s_i` by lines 6, 7, 9 from consecutive chain entries.
-/

variable {α : Type} [DecidableEq α]

/-- `min_{C : Q ⊆ C ⊆ E} {h(C) − t|C|}` (lines 24 and 27 of Algorithm 2). -/
noncomputable def constrainedMin (h : Finset α → ℝ) (E : Finset α) (t : ℝ) (Q : Finset α) :
    ℝ :=
  ⨅ C : {C : Finset α // Q ⊆ C ∧ C ⊆ E}, (h C.1 - t * (C.1.card : ℝ))

/-- FindMinimizer(h, t) (lines 23–33), looping over `E` in the order `ord`: start from `Q = ∅`
and add `v` whenever `min_{Q∪{v} ⊆ C ⊆ E} {h(C) − t|C|} = min_{C ⊆ E} {h(C) − t|C|}`. -/
noncomputable def findMinimizer (ord : List α) (h : Finset α → ℝ) (E : Finset α) (t : ℝ) :
    Finset α := by
  classical exact
    ord.foldl (fun Q v =>
      if constrainedMin h E t (insert v Q) = constrainedMin h E t ∅ then insert v Q else Q) ∅

/-- Recover(h, A, B) (lines 12–22) with fuel `k`: returns the subchain of prefixes from `A` to
`B` and the number of calls to FindMinimizer. -/
noncomputable def recover (ord : List α) (h : Finset α → ℝ) (E : Finset α) :
    ℕ → Finset α → Finset α → List (Finset α) × ℕ
  | 0, A, B => ([A, B], 0)
  | k + 1, A, B =>
    if A = B then ([A], 0) else
      let C := findMinimizer ord h E ((h B - h A) / ((B.card : ℝ) - (A.card : ℝ)))
      if C = B then ([A, B], 1) else
        let r₁ := recover ord h E k A C
        let r₂ := recover ord h E k C B
        (r₁.1 ++ r₂.1.tail, 1 + r₁.2 + r₂.2)

/-- The shares of lines 5–9 computed from a chain `(P₀, …, P_L)` given as a list:
`s_i = Σ_j (h_i(P_j) − h_i(P_{j−1}))/τ_j` with `τ_j = (h(P_j) − h(P_{j−1}))/|P_j \ P_{j−1}|`. -/
noncomputable def chainShares {ι : Type} [Fintype ι] (hs : ι → Finset α → ℝ)
    (l : List (Finset α)) (i : ι) : ℝ :=
  ((l.zip l.tail).map (fun p => (hs i p.2 - hs i p.1) /
    ((sumFn hs p.2 - sumFn hs p.1) / ((p.2 \ p.1).card : ℝ)))).sum

/-- The output of Decomposition: the chain it computes, the shares it returns, and the number of
calls to FindMinimizer it made. -/
structure DecompositionOutput (α ι : Type) where
  chain : List (Finset α)
  shares : ι → ℝ
  calls : ℕ

/-- Decomposition(E, (h_i)) (lines 1–11 of Algorithm 2), with FindMinimizer looping in the
order `ord`. -/
noncomputable def decomposition {ι : Type} [Fintype ι] (ord : List α)
    (hs : ι → Finset α → ℝ) (E : Finset α) : DecompositionOutput α ι :=
  let P₀ := findMinimizer ord (sumFn hs) E 0
  let r := recover ord (sumFn hs) E (E.card + 1) P₀ E
  ⟨r.1, chainShares hs r.1, 1 + r.2⟩

end SubmodSparsify


