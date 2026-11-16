-- Prove2me | Definitions.Def_BernoulliQPTAS_Scheduling_Supplement_Greedy
-- name    : BernoulliQPTAS_Scheduling_Supplement_Greedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:33:25.799575+00:00
-- url     : https://prove2.me/theorems/40a0e941-6992-4562-8d45-8e850c0f98d3
-- title:
--   The adaptive priority rule $G$, adaptive orders and the objective of Lemma 5.2
-- statement:
--   This file builds on the published Section 2 model (Bernoulli jobs, causal policy trees, states with machine release times) and defines the objects of Section 5.
--
--   **The rule $G$.** Fix distinct ranks $\rho(j)\in\mathbb N$ for the jobs. For $m\ge 2$ the rule keeps the multiset $A$ of the $m-1$ largest realized processing times among the jobs started so far, padded with zeros, and its minimum $\theta=\min A$ (initially $A=\{0,\dots,0\}$, so $\theta=0$). Whenever a machine is free, $G$ starts a remaining job minimizing, in lexicographic order,
--
--   $$
--   \bigl(q_j\min\{p_j,\theta\},\; q_j,\; \rho(j)\bigr),
--   $$
--
--   and then inserts the realized processing time ($p_j$ or $0$) into $A$, keeping the $m-1$ largest values. $G$ is non-idling: each job starts at the earliest machine release, on the lowest-labeled machine attaining it. For $m=1$ the first key is $\mu_j=q_jp_j$, i.e. $G$ is SEPT. $\Lambda=\sum_j q_j$ is `sumProb`.
--
--   **Charged implementation.** `greedyRun` is an explicit program for $G$ along one realization $\omega$, in the published bit-operation cost model (`Charged`, exact rational arithmetic with quadratic charges): it scans the remaining jobs, computes the keys, compares them lexicographically, picks the earliest machine, and updates the sorted multiset $A$ and the machine releases. It returns the realized actions (job, machine, start time).
--
--   **Adaptive orders and the objective of Lemma 5.2.** An adaptive order is a decision tree that picks the next job among the remaining ones as a function of the outcomes observed so far; it is valid for a set $R$ if it picks every job of $R$ exactly once on every branch. From a state $(A,R)$ with $|R|=s$, the realized increments are $D'_i=\min\{x_i,\theta_i\}$, where $x_i$ is the realized processing time of the $i$-th picked job and $\theta_i$ the current minimum of $A$ (then $A$ is updated). The objective is
--
--   $$
--   \mathbb E\Bigl[\sum_{i=1}^{s}(s-i)\,D'_i\Bigr],
--   $$
--
--   the expectation over independent Bernoulli outcomes. `greedyOrder` is the greedy rule written as an adaptive order.
--
--   **Formalization Note** The multiset $A$ is a list of rationals; `threshold` is its minimum. Ranks are natural numbers, and only their relative order matters.
-- source:
--   Junho Hwang, A QPTAS for Stochastic Scheduling of Bernoulli Jobs, STOC 2027 submission #427 (October 2026), PDF SHA-256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9, Section 5, pp. 14–15 (policy G, keys, Λ, the O(N²) remark; Section 5.1 increments D′ and the objective of Lemma 5.2)

import Definitions.Def_BernoulliQPTAS_Scheduling_Program
import Definitions.Def_BernoulliQPTAS_Scheduling_Reduction

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling.Supplement

open BernoulliQPTAS.Scheduling

/-! ### Section 5, pp. 14–15: the adaptive priority rule `G` and the surrogate `H` -/

/-- Realized processing time of job `j` as a rational: `p_j` if positive, else `0`. -/
def realized {N m : ℕ} (I : Instance N m) (j : Fin N) (positive : Bool) : ℚ :=
  if positive then I.size j else 0

/-- `θ = min A`: the minimum of the multiset `A` (the `m - 1` largest realized processing
    times so far, padded with zeros), stored as a list; `0` for the empty list. -/
def threshold (A : List ℚ) : ℚ := (A.mergeSort (fun x y => decide (x ≤ y))).headD 0

/-- Update of `A` after a realized value `x`: keep the `r` largest values of `A ∪ {x}`. -/
def updateTop (r : ℕ) (A : List ℚ) (x : ℚ) : List ℚ :=
  ((x :: A).mergeSort (fun x y => decide (y ≤ x))).take r

/-- The first key of p. 14, `d_j(θ) = q_j · min{p_j, θ}` for `m ≥ 2`. For `m = 1` the rule is
    SEPT, whose key is `μ_j = q_j p_j` (the minimum over an empty multiset is `+∞`). -/
def firstKey {N m : ℕ} (I : Instance N m) (θ : ℚ) (j : Fin N) : ℚ :=
  if m ≤ 1 then I.probability j * I.size j else I.probability j * min (I.size j) θ

/-- The lexicographic key `(q_j min{p_j, θ}, q_j, ρ(j))` of p. 14. -/
def greedyKey {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) (θ : ℚ) (j : Fin N) :
    Lex (ℚ × Lex (ℚ × ℕ)) :=
  toLex (firstKey I θ j, toLex (I.probability j, ρ j))

/-- The job the greedy rule starts next among the remaining jobs `R`, given the current
    multiset `A`: a minimizer of the lexicographic key (unique when `ρ` is injective). -/
def greedyChoice {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) (A : List ℚ)
    (R : Finset (Fin N)) : Option (Fin N) :=
  ((List.finRange N).filter (· ∈ R)).argmin (greedyKey I ρ (threshold A))

/-- The policy `G` from a state: non-idling (each start at the earliest machine release,
    on the lowest-labeled machine attaining it), always starting the greedy choice, and
    updating `A` with the realized processing time. -/
noncomputable def greedyTree {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) :
    ℕ → List ℚ → State N m → PolicyTree N m
  | 0, _, _ => .done
  | fuel + 1, A, s =>
      match greedyChoice I ρ A s.remaining, earliestMachine s with
      | some j, some i =>
          let a : Action N m := ⟨j, i, minRelease s⟩
          .start a (greedyTree I ρ fuel (updateTop (m - 1) A (realized I j false))
                (advance I s a false))
            (greedyTree I ρ fuel (updateTop (m - 1) A (realized I j true))
                (advance I s a true))
      | _, _ => .done

/-- The policy `G` of p. 14 for the whole instance: all machines free at time `0`, and
    initially `A` consists of `m - 1` zeros (so `θ = 0`). -/
noncomputable def greedyPolicy {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) : PolicyTree N m :=
  greedyTree I ρ N (List.replicate (m - 1) 0) (initialState Finset.univ)

/-- `Λ = Σ_j q_j`. -/
def sumProb {N m : ℕ} (I : Instance N m) : ℚ := ∑ j, I.probability j

/-! ### A charged implementation of `G` along one realization (the O(N²) remark, p. 14) -/

/-- Charged lexicographic comparison of two keys. -/
def keyLt (a b : ℚ × ℚ × ℕ) : Charged Bool := do
  if ← qLt a.1 b.1 then pure true
  else if ← qLt b.1 a.1 then pure false
  else if ← qLt a.2.1 b.2.1 then pure true
  else if ← qLt b.2.1 a.2.1 then pure false
  else do
    tick (natBits a.2.2 + natBits b.2.2)
    pure (decide (a.2.2 < b.2.2))

/-- Charged computation of the key of job `j` at threshold `θ`. -/
def keyCharged {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) (θ : ℚ) (j : Fin N) :
    Charged (ℚ × ℚ × ℕ) := do
  let p ← readSize I j
  let q ← readProbability I j
  tick (natBits (ρ j))
  let x ← if m ≤ 1 then pure p else do
    if ← qLt p θ then pure p else pure θ
  let d ← qMul q x
  pure (d, q, ρ j)

/-- Scan a list of jobs and keep the first one of minimum key. -/
def argminCharged {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) (θ : ℚ) :
    List (Fin N) → Charged (Option (Fin N × (ℚ × ℚ × ℕ)))
  | [] => pure none
  | j :: rest => do
      let kj ← keyCharged I ρ θ j
      let r ← argminCharged I ρ θ rest
      match r with
      | none => pure (some (j, kj))
      | some (j', k') => if ← keyLt k' kj then pure (some (j', k')) else pure (some (j, kj))

/-- The earliest release among the machines, lowest label on ties. -/
def earliestCharged : List ℚ → Charged (ℕ × ℚ)
  | [] => pure (0, 0)
  | [x] => pure (0, x)
  | x :: rest => do
      let r ← earliestCharged rest
      if ← qLt r.2 x then pure (r.1 + 1, r.2) else pure (0, x)

/-- Remove one copy of the minimum of a list sorted in nondecreasing order. -/
def dropMin : List ℚ → List ℚ
  | [] => []
  | _ :: xs => xs

/-- The charged run of `G` on the realization `ω`, with fuel `fuel`, remaining jobs `rem`,
    the multiset `A` stored sorted nondecreasingly (its head is `θ`), and machine releases
    `free`. Returns the realized actions `(job, machine, start time)` in order. -/
def greedyLoop {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) (ω : Outcome N) :
    ℕ → List (Fin N) → List ℚ → List ℚ → Charged (List (Fin N × ℕ × ℚ))
  | 0, _, _, _ => pure []
  | fuel + 1, rem, A, free => do
      let θ := A.headD 0
      let best ← argminCharged I ρ θ rem
      match best with
      | none => pure []
      | some (j, _) => do
          let e ← earliestCharged free
          let p ← readSize I j
          let x : ℚ := if ω j then p else 0
          let release ← qAdd e.2 x
          let A' ← if m ≤ 1 then pure A else do
            let B ← insertSorted x A
            pure (dropMin B)
          let rest ← greedyLoop I ρ ω fuel (rem.erase j) A' (free.set e.1 release)
          pure ((j, e.1, e.2) :: rest)

/-- The charged run of `G` from the initial state on the realization `ω`. -/
def greedyRun {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) (ω : Outcome N) :
    Charged (List (Fin N × ℕ × ℚ)) :=
  greedyLoop I ρ ω N (List.finRange N) (List.replicate (m - 1) 0) (List.replicate m 0)

/-! ### Section 5.1, p. 15: adaptive orders and the objective of Lemma 5.2 -/

/-- An adaptive order: the next job may depend on all outcomes observed so far; no times. -/
inductive OrderTree (N : ℕ) where
  | done : OrderTree N
  | pick : Fin N → OrderTree N → OrderTree N → OrderTree N

/-- An adaptive order of the remaining set `R` picks every job of `R` exactly once on every
    branch. -/
def ValidOrder {N : ℕ} : Finset (Fin N) → OrderTree N → Prop
  | R, .done => R = ∅
  | R, .pick j z p => j ∈ R ∧ ValidOrder (R.erase j) z ∧ ValidOrder (R.erase j) p

/-- The jobs in the order realized on outcome `ω`. -/
def orderTrace {N : ℕ} : OrderTree N → Outcome N → List (Fin N)
  | .done, _ => []
  | .pick j z p, ω => j :: (if ω j then orderTrace p ω else orderTrace z ω)

/-- The increments `D'_1, D'_2, …` of `W_{m-1}` along a realized sequence of starts, from
    the multiset `A`: a new realized value `x` changes `W_{m-1}` by `min{x, θ}`. -/
def increments {N m : ℕ} (I : Instance N m) (ω : Outcome N) : List ℚ → List (Fin N) → List ℚ
  | _, [] => []
  | A, j :: js =>
      min (realized I j (ω j)) (threshold A) ::
        increments I ω (updateTop (m - 1) A (realized I j (ω j))) js

/-- The objective `E[Σ_{i=1}^{s} (s - i) D'_i]` of Lemma 5.2 for the adaptive order `o`
    from the state `(A, R)`, `s = |R|`, under the product law of the outcomes. -/
noncomputable def orderObjective {N m : ℕ} (I : Instance N m) (A : List ℚ)
    (R : Finset (Fin N)) (o : OrderTree N) : ℝ :=
  ∑ ω : Outcome N, (outcomeWeight I ω : ℝ) *
    ∑ i : Fin (increments I ω A (orderTrace o ω)).length,
      (((R.card : ℤ) - ((i : ℕ) + 1 : ℤ) : ℤ) : ℝ) *
        ((increments I ω A (orderTrace o ω)).get i : ℝ)

/-- The greedy rule as an adaptive order from `(A, R)`. -/
def greedyOrder {N m : ℕ} (I : Instance N m) (ρ : Fin N → ℕ) :
    ℕ → List ℚ → Finset (Fin N) → OrderTree N
  | 0, _, _ => .done
  | fuel + 1, A, R =>
      match greedyChoice I ρ A R with
      | none => .done
      | some j => .pick j
          (greedyOrder I ρ fuel (updateTop (m - 1) A (realized I j false)) (R.erase j))
          (greedyOrder I ρ fuel (updateTop (m - 1) A (realized I j true)) (R.erase j))

end BernoulliQPTAS.Scheduling.Supplement


