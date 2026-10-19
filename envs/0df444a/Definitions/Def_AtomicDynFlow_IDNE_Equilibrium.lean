-- Prove2me | Definitions.Def_AtomicDynFlow_IDNE_Equilibrium
-- name    : AtomicDynFlow_IDNE_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:23.506046+00:00
-- url     : https://prove2.me/theorems/f843d631-604d-4412-9603-d129833e50de
-- title:
--   Definitions 1–2, pp. 11–12 — Nash equilibrium and iteratively dominant NE (IDNE) of Γ^N
-- statement:
--   Let $\Gamma^N$ be the game of nonadaptive agents on a network instance of the flow model: each agent $i\in\Delta$ picks a path $P_i\in\mathcal P_i$ at time $0$ and wants to reach $d$ as early as possible. A *path profile* $p=(P_i)_{i\in\Delta}$ assigns a strategy to every agent; $t^v_i(p)$ is the arrival time of $i$ at $v$.
--
--   **Definition 1 (NE).** $p$ is a Nash equilibrium if no agent gains by a unilateral deviation:
--   $$t^d_i(p)\le t^d_i(P'_i,p_{-i})\qquad\text{for all } i\in\Delta,\ P'_i\in\mathcal P_i .$$
--
--   **Definition 2 (IDNE).** For $k\ge 0$ let $[k]=\{1,\dots,k\}$. $p$ is an *iteratively dominant NE* if the agents can be reindexed as $1,2,\dots$ such that for every index $k\ge1$, every vertex $v$ on agent $k$'s path in $p$ (his starting vertex included) and every path profile $q$ of the agents outside $[k]$,
--   $$t^v_k(p_{[k]},q)=\min\bigl\{t^v_j(p_{[k-1]},r): j\in\Delta\setminus[k-1],\ r \text{ a path profile of } \Delta\setminus[k-1]\bigr\}.$$
--   In words: once agents $1,\dots,k-1$ are fixed on their paths in $p$, agent $k$ on his path in $p$ reaches every vertex of it at the earliest time any remaining agent could reach that vertex, whatever the agents after him do.
--
--   These are the two solution concepts of §4; Theorem 1 asserts that an IDNE always exists.
--
--   **Formalization Note.** Both equilibrium predicates require $p$ to be a valid path profile. The reindexing is a map $\sigma:\Delta\to\mathbb N$, injective with range an initial segment of $\mathbb N$; agent $a$ receives index $k=\sigma(a)+1$, so $[k]=\{b:\sigma b\le\sigma a\}$ and $[k-1]=\{b:\sigma b<\sigma a\}$. Profiles $q$ and $r$ are full path profiles (every agent present on a strategy) agreeing with $p$ on $[k]$, resp. $[k-1]$; the minimum is written as an infimum in `ℕ∞` (it is attained, at $j=k$, $r=q$). A vertex "on agent $a$'s path" is his starting vertex or the head of an edge of the path.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. 11 (PDF 12), Definition 1; p. 12 (PDF 13), Definition 2

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model

namespace AtomicDynFlow.IDNE

namespace Instance

variable {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [DecidableEq A]
variable (G : Instance V E A)

/-- Definition 1 (NE), p. 11: the path profile `p` (every agent present, `p a ∈ 𝒫_a`) is a Nash
equilibrium of `Γᴺ`: no agent `i` arrives at `d` strictly earlier by switching unilaterally to
another strategy `P' ∈ 𝒫_i`. Validity of `p` is part of the predicate. -/
def IsNE (p : A → List E) : Prop :=
  (∀ a, G.IsStrategy a (p a)) ∧
  ∀ (i : A) (P' : List E), G.IsStrategy i P' →
    G.arrival (fun b => some (p b)) i G.d ≤
      G.arrival (fun b => some (Function.update p i P' b)) i G.d

/-- Definition 2 (IDNE), p. 12, with the reindexing `σ` fixed. The agent `a` gets index
`k = σ a + 1`; `[k] = {b | σ b ≤ σ a}` and `[k - 1] = {b | σ b < σ a}`. `σ` is injective and its
range is an initial segment of `ℕ`, so the agents are reindexed as `1, 2, …`. The predicate
requires `p` to be a valid path profile. For every agent `a`,
every vertex `v` on `a`'s path `p a` (his starting vertex included) and every path profile `q` that
agrees with `p` on `[k]`,
`t^v_a(q) = min { t^v_j(r) : j ∉ [k-1], r a path profile agreeing with p on [k-1] }`. -/
def IsIDNEWith (σ : A → ℕ) (p : A → List E) : Prop :=
  (∀ a, G.IsStrategy a (p a)) ∧
  Function.Injective σ ∧ (∀ (a : A) (n : ℕ), n < σ a → ∃ b, σ b = n) ∧
  ∀ (a : A) (v : V), G.OnPath a (p a) v →
    ∀ q : A → List E, (∀ b, G.IsStrategy b (q b)) → (∀ b, σ b ≤ σ a → q b = p b) →
      G.arrival (fun b => some (q b)) a v =
        ⨅ (j : A) (_ : σ a ≤ σ j) (r : A → List E)
          (_ : (∀ b, G.IsStrategy b (r b)) ∧ ∀ b, σ b < σ a → r b = p b),
          G.arrival (fun b => some (r b)) j v

/-- Definition 2 (IDNE), p. 12: `p` is an iteratively dominant NE of `Γᴺ` if the agents can be
reindexed as `1, 2, …` so that the sequential optimality of `IsIDNEWith` holds. -/
def IsIDNE (p : A → List E) : Prop :=
  ∃ σ : A → ℕ, G.IsIDNEWith σ p

end Instance

end AtomicDynFlow.IDNE


