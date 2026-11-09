-- Prove2me | Definitions.Def_ProportionalGroupDivision_Main_Gifting
-- name    : ProportionalGroupDivision_Main_Gifting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:19.458792+00:00
-- url     : https://prove2.me/theorems/7c1d6616-3db4-47e7-8aac-ec2eeb18d0b3
-- title:
--   Algorithm 1 — the gifting algorithm, its trace, $\Delta_i$, the order $p$ and the residual matrix $B$
-- statement:
--   One group with $n_s$ agents has valuation matrix $A\in[0,1]^{n_s\times m}$. The algorithm has a threshold coefficient $\theta$ (the paper's $C'\Upsilon$) and a stopping level $s$ (the paper's $n/k$). It starts with $v=0$ (no good gifted) and all agents active, $S=[n_s]$. A dummy good valued $0$ by every agent is always available, so the following maximum exists.
--
--   1. Let $\lambda=\max_{j:\,v_j=0}\sum_{i\in S}A_{i,j}$ and let $j$ attain it.
--   2. With this $\lambda$ fixed, remove from $S$ every active agent with $\langle A_i,v\rangle\ge\theta\sqrt\lambda$.
--   3. If somebody was removed, go back to step 1 (recompute $j$ and $\lambda$ for the new $S$).
--   4. Otherwise, if $\lambda<s$ or $S=\varnothing$, terminate; else gift good $j$ ($v_j\leftarrow1$) and go to step 1.
--
--   From a run one reads off: the gifted set $v$; for every agent, $\Delta_i=\max\{\lambda,s\}$ with $\lambda$ taken at the moment agent $i$ is removed, and $\Delta_i=s$ if it is never removed; the sequence $p_1,\dots,p_{n_s}$ of agents in the order of removal, followed by the never-removed agents; and the matrix
--
--   $$B=\begin{pmatrix}A'_{p_1}\\ \vdots\\ A'_{p_{n_s}}\end{pmatrix},$$
--
--   where $A'$ is $A$ with the gifted columns deleted. These are the objects of Claims 11–13.
--
--   **Formalization Note** The paper's $\arg\max$ and "in any order" leave ties open; the definition takes an arbitrary tie-breaking priority $\tau$ (an ordering of the goods and an ordering of the agents): the first maximizing ungifted good in $\tau$ is gifted, and agents removed in one pass, as well as the never-removed agents, appear in $p$ in the order $\tau$. The dummy good is never gifted; with nonnegative entries it is the only maximizer only when $\lambda=0$, in which case the run stops anyway when $s>0$. Each non-terminating round removes an agent or gifts a new good, so the state after $n_s+m+1$ rounds is the terminal one.
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, §2.1, Algorithm 1 and the definitions before Claims 11 and 12, PDF pp. 12–14 = printed pp. 12–14

import Mathlib

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-!
# The gifting algorithm (Algorithm 1, PDF pp. 12–14)

One group with `ns` agents (rows) and valuation matrix `A ∈ [0,1]^{ns × m}`. The algorithm has two
real parameters: the threshold coefficient `θ` (the paper's `C′ · Υ`) and the stopping level `s`
(the paper's `n/k`). It keeps the set `v` of gifted goods and the set `S` of active agents.

One round: let `λ` be the largest column sum `∑_{i ∈ S} A_{i,j}` over the goods `j ∉ v`, where a
dummy good of value `0` for everyone is always available (the paper's convention on p. 12), so
`λ ≥ 0` is defined even when no actual good is left. With this `λ` fixed, every active agent with
`⟨A_i, v⟩ ≥ θ √λ` is removed. If somebody was removed, the round restarts (recompute `j`, `λ` on the
new `S` and filter again), before anything is gifted. If nobody was removed: if `λ < s` or
`S = ∅` the algorithm terminates; otherwise the good `j` attaining `λ` is gifted (`v_j ← 1`).
The paper's `arg max` and its "in any order" leave ties open; here they are resolved by an arbitrary
priority order `τ` (a `TieOrder`): among the maximizing ungifted goods the one listed first by
`τ.goods` is gifted, agents removed in the same filtration pass are recorded in the order listed by
`τ.agents`, and so are the never-removed agents at the end of `p`. Statements about the algorithm
quantify over every `τ`. The dummy good is never gifted (if no actual good attains `λ`, the
algorithm terminates; with nonnegative entries this happens only when `λ = 0`).

Every non-terminating round removes an agent or gifts a new good, so after `ns + m + 1` rounds the
algorithm has terminated; `giftRun` is the state after that many rounds.
-/

/-- The state of Algorithm 1: gifted goods `v`, active agents `S`, the removal record (each
removed agent with the value of `λ` at its removal, in removal order), and the termination flag. -/
structure GiftState (ns m : ℕ) where
  gifted : Finset (Fin m)
  active : Finset (Fin ns)
  removals : List (Fin ns × ℝ)
  done : Bool

/-- A tie-breaking priority: goods are scanned in the order `τ.goods 0, τ.goods 1, …` and agents
in the order `τ.agents 0, τ.agents 1, …`. -/
structure TieOrder (ns m : ℕ) where
  goods : Equiv.Perm (Fin m)
  agents : Equiv.Perm (Fin ns)

/-- The initial state: `v = 0`, `S = [ns]`, nobody removed. -/
def giftInit (ns m : ℕ) : GiftState ns m := ⟨∅, Finset.univ, [], false⟩

/-- The column sum `∑_{i ∈ S} A_{i,j}` over the active agents. -/
def colSum {ns m : ℕ} (A : Matrix (Fin ns) (Fin m) ℝ) (S : Finset (Fin ns)) (j : Fin m) : ℝ :=
  ∑ i ∈ S, A i j

/-- `λ`: the largest active column sum over the ungifted goods and the dummy good (value `0`). -/
noncomputable def giftLam {ns m : ℕ} (A : Matrix (Fin ns) (Fin m) ℝ) (S : Finset (Fin ns))
    (v : Finset (Fin m)) : ℝ :=
  (insert 0 ((Finset.univ.filter (fun j => j ∉ v)).image (colSum A S))).max'
    (Finset.insert_nonempty _ _)

/-- The good chosen for gifting: the first ungifted actual good in the priority `τ.goods` attaining
`λ` (`none` if only the dummy good attains it). -/
noncomputable def giftChoice {ns m : ℕ} (τ : TieOrder ns m) (A : Matrix (Fin ns) (Fin m) ℝ) (S : Finset (Fin ns))
    (v : Finset (Fin m)) : Option (Fin m) :=
  open Classical in
  ((List.finRange m).map τ.goods).find? (fun j => decide (j ∉ v ∧ colSum A S j = giftLam A S v))

/-- One round of Algorithm 1 with threshold coefficient `θ` and stopping level `s`. -/
noncomputable def giftStep {ns m : ℕ} (τ : TieOrder ns m) (θ s : ℝ) (A : Matrix (Fin ns) (Fin m) ℝ)
    (st : GiftState ns m) : GiftState ns m :=
  open Classical in
  if st.done then st else
    let lam := giftLam A st.active st.gifted
    let R := ((List.finRange ns).map τ.agents).filter
      (fun i => decide (i ∈ st.active ∧ θ * Real.sqrt lam ≤ ∑ g ∈ st.gifted, A i g))
    if R ≠ [] then
      { st with active := st.active \ R.toFinset,
                removals := st.removals ++ R.map (fun i => (i, lam)) }
    else if lam < s ∨ st.active = ∅ then { st with done := true }
    else
      match giftChoice τ A st.active st.gifted with
      | none => { st with done := true }
      | some j => { st with gifted := insert j st.gifted }

/-- The terminal state of Algorithm 1 (after `ns + m + 1` rounds). -/
noncomputable def giftRun {ns m : ℕ} (τ : TieOrder ns m) (θ s : ℝ) (A : Matrix (Fin ns) (Fin m) ℝ) : GiftState ns m :=
  (giftStep τ θ s A)^[ns + m + 1] (giftInit ns m)

/-- The output `v` of Algorithm 1: the set of gifted goods. -/
noncomputable def giftedSet {ns m : ℕ} (τ : TieOrder ns m) (θ s : ℝ) (A : Matrix (Fin ns) (Fin m) ℝ) : Finset (Fin m) :=
  (giftRun τ θ s A).gifted

/-- p. 14: `Δ_i = max{λ, s}` with `λ` taken at the moment agent `i` is removed, and `Δ_i = s` if
agent `i` is never removed. -/
noncomputable def giftDelta {ns m : ℕ} (τ : TieOrder ns m) (θ s : ℝ) (A : Matrix (Fin ns) (Fin m) ℝ) (i : Fin ns) : ℝ :=
  match ((giftRun τ θ s A).removals.find? (fun e => decide (e.1 = i))) with
  | some e => max e.2 s
  | none => s

/-- p. 14: the sequence `p_1, …, p_{ns}`: agents in the order of removal (within one filtration
pass, in the priority `τ.agents`), followed by the never-removed agents in the priority `τ.agents`. -/
noncomputable def giftOrder {ns m : ℕ} (τ : TieOrder ns m) (θ s : ℝ) (A : Matrix (Fin ns) (Fin m) ℝ) : List (Fin ns) :=
  let rem := (giftRun τ θ s A).removals.map Prod.fst
  rem ++ ((List.finRange ns).map τ.agents).filter (fun i => decide (i ∉ rem))

/-- The position map `ℓ ↦ p_ℓ` of `giftOrder` (a list of length `ns` listing each agent once). -/
noncomputable def giftPerm {ns m : ℕ} (τ : TieOrder ns m) (θ s : ℝ) (A : Matrix (Fin ns) (Fin m) ℝ) (ℓ : Fin ns) :
    Fin ns :=
  (giftOrder τ θ s A).getD ℓ ℓ

/-- p. 14: the matrix `B` with rows `A′_{p_1}, …, A′_{p_{ns}}`, where `A′` is `A` with the gifted
columns deleted (columns are the ungifted goods). -/
noncomputable def giftResidual {ns m : ℕ} (τ : TieOrder ns m) (θ s : ℝ) (A : Matrix (Fin ns) (Fin m) ℝ) :
    Fin ns → {g : Fin m // g ∉ giftedSet τ θ s A} → ℝ :=
  fun ℓ g => A (giftPerm τ θ s A ℓ) g

end ProportionalGroupDivision.Main


