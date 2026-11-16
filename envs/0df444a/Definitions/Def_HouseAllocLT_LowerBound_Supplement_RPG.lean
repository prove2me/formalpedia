-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG
-- name    : HouseAllocLT_LowerBound_Supplement_RPG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:13:47.889673+00:00
-- url     : https://prove2.me/theorems/44710927-ba2b-449f-8c22-60525d442043
-- title:
--   Rank-priority greedy on whole classes, class vectors, key orders and Pareto optimality
-- statement:
--   A **maximum-matching routine** is a fixed deterministic map sending each edge set $F\subseteq N\times A$ to one maximum-cardinality matching of the bipartite graph $(N\cup A,F)$.
--
--   **Rank-priority greedy** (RPG, Algorithm 1) on a profile $P$ with agent order $\pi$ ($\pi(i)$ the position of agent $i$) starts from $D=F=M=\emptyset$. For ranks $j=1,\ldots,r(P)$ and, within a rank, agents in increasing position: if $i\notin D$ and $C_j^i\neq\emptyset$, it puts $B=\{(i,a):a\in C_j^i\}$, computes $M'=\mathrm{MM}(F\cup B)$, and if $|M'|=|D|+1$ it sets $D\leftarrow D\cup\{i\}$, $F\leftarrow F\cup B$, $M\leftarrow M'$ (agent $i$ is *accepted at rank $j$*). The output is $M_\pi(P)$. As a randomized mechanism, RPG draws $\pi$ uniformly from the $n!$ orders, so a matching $\mu$ has probability $\#\{\pi:M_\pi(P)=\mu\}/n!$.
--
--   For a matching $M$, $z_{i,j}(M)=1$ iff $M(i)\in C_j^i$; the **class vector** lists these entries ordered by rank $j$ first and then by the agent's position. A matching has the **best class vector** if it is feasible and its class vector is lexicographically largest among all feasible matchings. With pairwise distinct **keys** $u\in(0,1)^N$, the induced order processes smaller keys first; $M(u)$ is the RPG output for that order, and for $t$ different from every key, $F_t(u)=\{i: i\text{ is unmatched in }M(u^{i,t})\}$, where $u^{i,t}$ replaces only $u_i$ by $t$.
--
--   Agent $i$'s **rank** in $\mu$ is the index of the class of $P_i$ containing its object, and $+\infty$ if it is unmatched. A feasible $\mu$ is **Pareto optimal** if no feasible $\nu$ gives every agent a rank at most its rank in $\mu$ and some agent a strictly smaller rank. $P^{\le h}$ ends every list after its $h$-th class.
--
--   **Formalization Note.** Ranks and classes are numbered from $0$ in Lean. The class-vector entry $(i,j)$ sits at index $j\cdot n+\mathrm{pos}(i)$. The RPG lottery counts orders whose output, projected onto feasible matchings, equals $\mu$; RPG outputs are feasible, so the projection is the identity on them.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), §4.1 and Algorithm 1, PDF pp. 10–11 (printed pp. 8–9); §4.4 keys and (11), PDF p. 12 (printed p. 10); Pareto optimality, §2, PDF p. 7 (printed p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Mechanism

open scoped BigOperators
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

noncomputable section

/-! # Rank-priority greedy (RPG) on whole classes

Zhang, Zhao, Xu, Xi, Zhao, STOC 2027 submission #174 (October 2026), §4.1, PDF pp. 10–11
(printed pp. 8–9), Algorithm 1; Pareto optimality from §2, PDF p. 7 (printed p. 5).

Profiles, matchings, feasibility and mechanisms are the published base definitions of
`HouseAllocLT.LowerBound`. Classes are 0-based: the paper's rank `j` is `classes (j - 1)`. -/

variable {n m : ℕ}

/-- `M` is a maximum matching of the bipartite graph `(N ∪ A, F)`: a matching using only edges
of `F`, of largest size among all such matchings (§2: "maximum means largest size"). -/
def IsMaxMatchingOf (F M : Assignment n m) : Prop :=
  TwoStageMatch.IsMatching (fun i a => (i, a) ∈ F) Finset.univ Finset.univ M ∧
    ∀ M' : Assignment n m,
      TwoStageMatch.IsMatching (fun i a => (i, a) ∈ F) Finset.univ Finset.univ M' →
        M'.card ≤ M.card

/-- A fixed deterministic maximum-matching routine (Algorithm 1, "Require"): a function from
edge sets to one maximum matching of that edge set. -/
structure MaxMatchingRoutine (n m : ℕ) where
  mm : Assignment n m → Assignment n m
  isMax : ∀ F, IsMaxMatchingOf F (mm F)

/-- The working state of Algorithm 1: accepted agents `D`, kept edges `F`, current matching `M`,
and the (0-based) rank at which each agent was accepted (`none` if never accepted). -/
structure RPGState (n m : ℕ) where
  D : Finset (Fin n)
  F : Assignment n m
  M : Assignment n m
  acc : Fin n → Option ℕ

/-- Line 2 of Algorithm 1: `D ← ∅; F ← ∅; M ← ∅`. -/
def RPGState.init : RPGState n m := ⟨∅, ∅, ∅, fun _ => none⟩

/-- `B = {(i, a) : a ∈ C_j^i}`, every edge of agent `i`'s whole class `j`. -/
def classEdges (P : Profile n m) (i : Fin n) (j : ℕ) : Assignment n m :=
  ((P i).classes j).image (fun a => (i, a))

/-- Lines 5–11 of Algorithm 1 for the pair `(j, i)`: if `i ∉ D` and `C_j^i ≠ ∅`, compute
`M' = MM(F ∪ B)`; if `|M'| = |D| + 1`, accept `i` at rank `j` and keep all of `B`. -/
def rpgStep (MM : MaxMatchingRoutine n m) (P : Profile n m) (s : RPGState n m)
    (ji : ℕ × Fin n) : RPGState n m :=
  if ji.2 ∉ s.D ∧ ((P ji.2).classes ji.1).Nonempty then
    if (MM.mm (s.F ∪ classEdges P ji.2 ji.1)).card = s.D.card + 1 then
      ⟨insert ji.2 s.D, s.F ∪ classEdges P ji.2 ji.1, MM.mm (s.F ∪ classEdges P ji.2 ji.1),
        Function.update s.acc ji.2 (some ji.1)⟩
    else s
  else s

/-- The pairs `(j, i)` in the order of Algorithm 1: ranks `j = 0, …, r(P) − 1` (the paper's
`1, …, r(P)`), and within a rank the agents in the processing order `ord`. -/
def rpgSchedule (P : Profile n m) (ord : List (Fin n)) : List (ℕ × Fin n) :=
  (List.range (rankLength P)).flatMap (fun j => ord.map (fun i => (j, i)))

/-- A complete RPG run with agents processed in the list order `ord`. -/
def rpgRunList (MM : MaxMatchingRoutine n m) (P : Profile n m) (ord : List (Fin n)) :
    RPGState n m :=
  (rpgSchedule P ord).foldl (rpgStep MM P) RPGState.init

/-- The processing order of a priority order `π`, where `π i` is the position of agent `i`:
agents in increasing position. -/
def permOrder (π : Equiv.Perm (Fin n)) : List (Fin n) :=
  (List.finRange n).map π.symm

/-- The run of Algorithm 1 for the fixed order `π`. -/
def rpgRun (MM : MaxMatchingRoutine n m) (P : Profile n m) (π : Equiv.Perm (Fin n)) :
    RPGState n m :=
  rpgRunList MM P (permOrder π)

/-- `M_π(P)`, the output of Algorithm 1 for the fixed order `π` (line 14). -/
def rpgOut (MM : MaxMatchingRoutine n m) (P : Profile n m) (π : Equiv.Perm (Fin n)) :
    Assignment n m :=
  (rpgRun MM P π).M

/-- Projection onto feasible matchings: the identity on feasible matchings, `∅` otherwise.
Used only to make the lottery below a `Mechanism` without proving feasibility of every RPG
output inside a definition (RPG outputs are feasible; Lemma 4.1 asserts it). -/
def feasibleOrEmpty (P : Profile n m) (μ : Assignment n m) : Assignment n m :=
  if Feasible P μ then μ else ∅

theorem feasible_empty (P : Profile n m) : Feasible P (∅ : Assignment n m) :=
  TwoStageMatch.isMatching_empty _ _ _

theorem feasible_feasibleOrEmpty (P : Profile n m) (μ : Assignment n m) :
    Feasible P (feasibleOrEmpty P μ) := by
  unfold feasibleOrEmpty
  split_ifs with h
  · exact h
  · exact feasible_empty P

/-- The lottery of a rule that runs a deterministic procedure `f P π` on a uniformly random
order `π` of the `n` agents: `μ` has probability `#{π : f P π = μ} / n!`. -/
def uniformOrderLottery (f : Profile n m → Equiv.Perm (Fin n) → Assignment n m) :
    Mechanism n m where
  prob P μ :=
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => feasibleOrEmpty P (f P π) = μ)).card : ℝ)
      / (n.factorial : ℝ)
  nonneg := by intro P μ; positivity
  total := by
    intro P
    rw [← Finset.sum_div]
    have hcard : ((Finset.univ : Finset (Equiv.Perm (Fin n))).card : ℝ) =
        ∑ μ : Assignment n m,
          ((Finset.univ.filter
            (fun π : Equiv.Perm (Fin n) => feasibleOrEmpty P (f P π) = μ)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun π => feasibleOrEmpty P (f P π))
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      push_cast
      rfl
    rw [← hcard, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    have : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    field_simp
  supported := by
    intro P μ h
    have hne : (Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => feasibleOrEmpty P (f P π) = μ)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      apply h
      rw [he]
      simp
    obtain ⟨π, hπ⟩ := hne
    rw [Finset.mem_filter] at hπ
    rw [← hπ.2]
    exact feasible_feasibleOrEmpty P _

/-- RPG (Algorithm 1) as a randomized mechanism: a uniform random order of the agents
(line 1), then the deterministic run with the fixed routine `MM`. -/
def rpg (MM : MaxMatchingRoutine n m) : Mechanism n m :=
  uniformOrderLottery (fun P π => rpgOut MM P π)

/-! ## Class vectors -/

/-- `z_{i,j}(M)`: `1` if `M(i) ∈ C_j^i` (0-based `j`), `0` otherwise. -/
def entryVal (P : Profile n m) (M : Assignment n m) (i : Fin n) (j : ℕ) : ℕ :=
  if ∃ a ∈ (P i).classes j, (i, a) ∈ M then 1 else 0

/-- The class vector `z(M)` for an agent order given by positions `pos : Fin n → ℕ`
(a bijection onto `{0, …, n − 1}`): entry `(i, j)` sits at index `j · n + pos i`, i.e. the pairs
are ordered by rank first and then by position (§4.1, PDF p. 10). -/
def classVec (P : Profile n m) (pos : Fin n → ℕ) (M : Assignment n m) (k : ℕ) : ℕ :=
  if ∃ i : Fin n, ∃ j : ℕ, j * n + pos i = k ∧ entryVal P M i j = 1 then 1 else 0

/-- `M` is feasible at `P` and has the lexicographically largest class vector among all
matchings feasible at `P`, for the order given by `pos` ("best class vector"). -/
def IsLexBest (P : Profile n m) (pos : Fin n → ℕ) (M : Assignment n m) : Prop :=
  Feasible P M ∧ ∀ ν : Assignment n m, Feasible P ν →
    LexGE (rankLength P * n) (classVec P pos M) (classVec P pos ν)

/-- Positions of the priority order `π`: agent `i` sits at position `π i`. -/
def permPos (π : Equiv.Perm (Fin n)) (i : Fin n) : ℕ := (π i : ℕ)

/-! ## Key-ordered runs (§4.4, PDF p. 12) -/

/-- The processing order induced by keys `u`: smaller keys first. -/
def keyOrder (u : Fin n → ℝ) : List (Fin n) :=
  (List.finRange n).insertionSort (fun a b => u a ≤ u b)

/-- The position of agent `i` in the key order: the number of agents with a smaller key. -/
def keyPos (u : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => u j < u i)).card

/-- `M(u)`, the RPG output for the order induced by the keys `u` and the fixed routine. -/
def rpgOutKeys (MM : MaxMatchingRoutine n m) (P : Profile n m) (u : Fin n → ℝ) :
    Assignment n m :=
  (rpgRunList MM P (keyOrder u)).M

/-- Agent `i` is matched in `M`. -/
def Matched (M : Assignment n m) (i : Fin n) : Prop := ∃ a, (i, a) ∈ M

/-- `F_t(u) = {i : i is unmatched in M(u^{i,t})}` (11): the agents left unmatched by their
comparison runs, where `u^{i,t}` replaces only `u_i` by `t`. -/
def startingAgents (MM : MaxMatchingRoutine n m) (P : Profile n m) (u : Fin n → ℝ) (t : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬ Matched (rpgOutKeys MM P (Function.update u i t)) i)

/-! ## Ranks and Pareto optimality (§2, PDF p. 7) -/

/-- The (0-based) rank of the class containing agent `i`'s object in `μ`; `⊤` if `i` receives
no listed object (unmatched). -/
def agentRank (P : Profile n m) (μ : Assignment n m) (i : Fin n) : ℕ∞ :=
  if h : ∃ j, ∃ a ∈ (P i).classes j, (i, a) ∈ μ then (Nat.find h : ℕ∞) else ⊤

/-- Pareto optimality at `P` (§2): `μ` is feasible, and no feasible `ν` makes every agent weakly
better off (rank no larger) and some agent strictly better off. Objects in one class are tied;
every acceptable object beats being unmatched (rank `⊤`). -/
def IsParetoOptimal (P : Profile n m) (μ : Assignment n m) : Prop :=
  Feasible P μ ∧ ¬ ∃ ν : Assignment n m, Feasible P ν ∧
    (∀ i, agentRank P ν i ≤ agentRank P μ i) ∧ ∃ i, agentRank P ν i < agentRank P μ i

/-- `Pr_{μ ∼ φ(P)}[μ is Pareto optimal at P]`. -/
def poProb (φ : Mechanism n m) (P : Profile n m) : ℝ :=
  ∑ μ, if IsParetoOptimal P μ then φ.prob P μ else 0

/-! ## Shortened lists -/

/-- The list `p` ended after its first `h` classes (ranks `1, …, h`): classes `j < h` kept
whole, later classes removed. -/
def truncate {m : ℕ} (p : Preference m) (h : ℕ) : Preference m where
  length := min p.length h
  classes j := if j < h then p.classes j else ∅
  nonempty_iff j := by
    by_cases hj : j < h
    · simp only [hj, if_true, lt_min_iff, and_true]
      exact p.nonempty_iff j
    · simp [hj]
  disjoint j k hjk := by
    by_cases hj : j < h <;> by_cases hk : k < h <;> simp [hj, hk, p.disjoint j k hjk]

/-- `P^{≤h}`: every list ended after rank `h`. -/
def truncateProfile (P : Profile n m) (h : ℕ) : Profile n m := fun i => truncate (P i) h

end

end HouseAllocLT.LowerBound.Supplement


