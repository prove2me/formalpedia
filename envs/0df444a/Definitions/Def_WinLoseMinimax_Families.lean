-- Prove2me | Definitions.Def_WinLoseMinimax_Families
-- name    : WinLoseMinimax_Families
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:53.320564+00:00
-- url     : https://prove2.me/theorems/6414630f-b018-474e-89ff-6a82b760d824
-- title:
--   §2 — the row and column families $B^1$, $B^1_{down}$, $B^2$, $B^2_{down}$, ascending-union closed, truncated games
-- statement:
--   Let $G=(S,T,\pi)$ be a win-lose game.
--
--   1. For $s\in S$, $B_s=\{t\in T:\pi(s,t)=1\}$ is the set of player 2's strategies that $s$ beats; $\mathcal B^1(G)=\{B_s:s\in S\}$, and its downward closure is $\mathcal B^1_{\mathrm{down}}(G)=\{A\subseteq T:\exists s\in S,\ A\subseteq B_s\}$ (p.5).
--   2. For $t\in T$, $B_t=\{s\in S:\pi(s,t)=0\}$; $\mathcal B^2(G)=\{B_t:t\in T\}$ and $\mathcal B^2_{\mathrm{down}}(G)=\{A\subseteq S:\exists t\in T,\ A\subseteq B_t\}$ (pp.10–11).
--   3. A family $\mathcal F$ of sets is **ascending-union closed** (Definition 2.1, p.6) if
--
--   $$A_i\in\mathcal F\ (i=1,2,\dots),\quad A_1\subset A_2\subset\cdots\subset A_i\subset\cdots\ \Longrightarrow\ \bigcup_{i=1}^\infty A_i\in\mathcal F.$$
--
--   4. For an enumeration $t_1,t_2,\dots$ of a countable $T$, the **truncated game** $G_n=(S,T_n,\pi_n)$ restricts player 2 to the first $n$ pure strategies (proof of Theorem 2.2, Step 2, p.6).
--
--   These families carry the combinatorial conditions of Theorem 2.2, Proposition 2.9, Theorem 2.11 and Corollaries 2.10, 2.12; the truncated games are the finite approximations used in the proofs of Theorems 2.2 and 3.1.
--
--   **Formalization Note** The paper assumes w.l.o.g. that rows (columns) are distinct; the families as sets of subsets do not need it and it is not imposed. In Definition 2.1 the chain is indexed by $\mathbb N$ and $\subset$ is strict (`StrictMono`); the non-strict reading gives the same notion. The enumeration is `e : ℕ ≃ T` and the first $n$ strategies are $e(0),\dots,e(n-1)$.
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, §2 pp.5, 10–11 (B_s, B¹(G), B¹_down(G), B_t, B²(G), B²_down(G)); Definition 2.1 p.6; proof of Theorem 2.2, Step 2, p.6 (Gₙ)

import Mathlib
import Definitions.Def_WinLoseMinimax_Game

namespace WinLoseMinimax

universe u v w

/-- **The set `B_s`.** Holzman, arXiv:2310.19314v1, §2, p.5: for a strategy `s` of player 1,
`B_s = {t ∈ T : π(s, t) = 1}`, the set of player 2's strategies that `s` beats. -/
def rowSet {S : Type u} {T : Type v} (π : S → T → Bool) (s : S) : Set T :=
  {t | π s t = true}

/-- **The family `B¹(G)`.** Holzman, arXiv:2310.19314v1, §2, p.5: `B¹(G) = {B_s : s ∈ S}`.

**Formalization Note.** The paper first assumes w.l.o.g. that the rows of `M_G` are distinct; the
family of sets does not depend on that assumption, which is not imposed. -/
def B1 {S : Type u} {T : Type v} (π : S → T → Bool) : Set (Set T) :=
  Set.range (rowSet π)

/-- **The downward closure `B¹_down(G)`.** Holzman, arXiv:2310.19314v1, §2, p.5:
`B¹_down(G) = {A ⊆ T : ∃ s ∈ S such that A ⊆ B_s}`. -/
def B1down {S : Type u} {T : Type v} (π : S → T → Bool) : Set (Set T) :=
  {A | ∃ s, A ⊆ rowSet π s}

/-- **The set `B_t`.** Holzman, arXiv:2310.19314v1, §2, p.10: for a strategy `t` of player 2,
`B_t = {s ∈ S : π(s, t) = 0}`, the set of player 1's strategies that `t` beats. -/
def colSet {S : Type u} {T : Type v} (π : S → T → Bool) (t : T) : Set S :=
  {s | π s t = false}

/-- **The family `B²(G)`.** Holzman, arXiv:2310.19314v1, §2, p.10: `B²(G) = {B_t : t ∈ T}`.

**Formalization Note.** The w.l.o.g. assumption that the columns are distinct is not imposed. -/
def B2 {S : Type u} {T : Type v} (π : S → T → Bool) : Set (Set S) :=
  Set.range (colSet π)

/-- **The downward closure `B²_down(G)`.** Holzman, arXiv:2310.19314v1, §2, p.11:
`B²_down(G) = {A ⊆ S : ∃ t ∈ T such that A ⊆ B_t}`. -/
def B2down {S : Type u} {T : Type v} (π : S → T → Bool) : Set (Set S) :=
  {A | ∃ t, A ⊆ colSet π t}

/-- **Ascending-union closed.** Holzman, arXiv:2310.19314v1, Definition 2.1, p.6: a family `F`
of sets is ascending-union closed if `Aᵢ ∈ F, i = 1, 2, …` and `A₁ ⊂ A₂ ⊂ ⋯ ⊂ Aᵢ ⊂ ⋯` imply
`⋃_{i=1}^∞ Aᵢ ∈ F`.

**Formalization Note.** Chains are indexed by `ℕ` (the paper's `i = 1, 2, …`) and `⊂` is read as
strict inclusion (`StrictMono`), the reading forced in Proposition 2.9(2). For this definition the
non-strict reading (`Monotone`) gives the same notion: a non-strict chain is either eventually
constant (its union is one of its members) or has a strictly increasing subsequence with the
same union. -/
def AscendingUnionClosed {α : Type w} (F : Set (Set α)) : Prop :=
  ∀ A : ℕ → Set α, (∀ i, A i ∈ F) → StrictMono A → (⋃ i, A i) ∈ F

/-- **First `n` strategies of player 2.** Holzman, arXiv:2310.19314v1, proof of Theorem 2.2,
Step 2, p.6 (and proof of Theorem 3.1, Step 2, p.12): with `T` identified with the positive
integers, `Tₙ` is the set of the first `n` pure strategies of player 2.

**Formalization Note.** The identification is an enumeration `e : ℕ ≃ T`, and the first `n`
strategies are `e 0, …, e (n-1)` (`e '' Set.Iio n`), the paper's `1, …, n`. -/
def truncSet {T : Type v} (e : ℕ ≃ T) (n : ℕ) : Set T :=
  e '' Set.Iio n

/-- **The truncated game `Gₙ = (S, Tₙ, πₙ)`.** Holzman, arXiv:2310.19314v1, proof of Theorem 2.2,
Step 2, p.6: the subgame of `G` obtained by restricting player 2 to the first `n` pure strategies.

**Formalization Note.** Player 1 keeps all of `S`; player 2's strategy set is the subtype of
`truncSet e n`, non-empty exactly when `1 ≤ n`. -/
def trunc {S : Type u} {T : Type v} (π : S → T → Bool) (e : ℕ ≃ T) (n : ℕ) :
    S → truncSet e n → Bool :=
  fun s t => π s t

end WinLoseMinimax


