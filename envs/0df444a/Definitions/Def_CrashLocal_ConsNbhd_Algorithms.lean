-- Prove2me | Definitions.Def_CrashLocal_ConsNbhd_Algorithms
-- name    : CrashLocal_ConsNbhd_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:59:56.41922+00:00
-- url     : https://prove2.me/theorems/e04a0870-e1b7-4675-964c-4af8ad01eadb
-- title:
--   Algorithms 4 and 5, the large-girth algorithm, propagation graphs and the choices (2) of T
-- statement:
--   §5.3–5.5. alg4 n R (Algorithm 4): gather for n − 1 rounds, reconstruct J_v = G[Q_v] and output J_v[B_{J_v}(v, R)]. girthAlg R (§5.5): gather for R rounds and output G[Q_v]. alg5 R T (Algorithm 5): Phase I (rounds 1, …, R) is Algorithm 2 with W_v = {v}; in Phase II (global rounds R + 1, …, R + T) every node sends W_v to every neighbor and adds each received identifier that belongs to Q_v; at the end of round R + T it outputs G[W_v] reconstructed from K_v. For its execution: propSet x = V_x = {x} ∪ {nodes holding σ_x at the end of some Phase I round}, so Γ_x = G[V_x]; storesToken r w x: w has not crashed and id x ∈ W_w at the end of round r; floodAdv adv R U is the crash pattern on U of Lemma 12(i): nodes that crashed in rounds ≤ R crash before the initial computation, a node crashing in global round R + r crashes in round r, with the same per-recipient delivery. Choice2 c Δ R T adv lists the three choices (2): Δ ≥ 3 and T = Δ ∑_{i=0}^{R−1} (Δ−1)^i; or T = c·Δ·R·f for some f ≥ 1 with at most f crashes; or Δ = 2 and T = 2R.
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, §5.3–5.5, Algorithms 4–5 and (1)–(2), pp. 26–29, 31

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Gathering
import Definitions.Def_CrashLocal_ConsNbhd_Flooding

noncomputable section
open Classical

namespace CrashLocal.ConsNbhd

variable {V L : Type}

/-- Algorithm 4: gather for `n − 1` rounds, reconstruct `J_v = G[Q_v]` from `K_v` and output
`H_v = J_v[B_{J_v}(v, R)]`. -/
def alg4 (n R : ℕ) : NodeProgram L (View L) :=
  gatherThen (n - 1) (fun me K => (reconstruct K).induce ((reconstruct K).ballSet me R))

/-- The large-girth algorithm of §5.5 (Lemma 19): gather for `R` rounds and output `G[Q_v]`. -/
def girthAlg (R : ℕ) : NodeProgram L (View L) :=
  gatherThen R (fun _ K => reconstruct K)

/-- Local state of Algorithm 5: own identifier, rounds completed, collected stars `K_v`, stored
tokens `W_v` (identifiers). -/
structure RPState (L : Type) where
  me : ℕ
  round : ℕ
  K : Set (Star L)
  W : Set ℕ

/-- Algorithm 5 (restricted propagation) with radius `R` and `T` propagation rounds. Phase I
(global rounds `1, …, R`): Algorithm 2, `K_v ← K_v ∪` received stars. `W_v = {v}`. Phase II (global
rounds `R + 1, …, R + T`): send `W_v` to every neighbor and add each received identifier that is in
`Q_v = {x : σ_x ∈ K_v}`. Output at the end of round `R + T`: `H_v = G[W_v]` reconstructed from
`K_v`. -/
def alg5 (R T : ℕ) : NodeProgram L (View L) where
  State := RPState L
  Msg := Set (Star L) × Set ℕ
  init a l N := ⟨a, 0, {⟨a, l, N⟩}, {a}⟩
  send s _ :=
    if s.round < R then (s.K, ∅) else if s.round < R + T then (∅, s.W) else (∅, ∅)
  update s inb :=
    if s.round < R then
      ⟨s.me, s.round + 1, s.K ∪ {σ | ∃ b M, inb b = some M ∧ σ ∈ M.1}, s.W⟩
    else if s.round < R + T then
      ⟨s.me, s.round + 1, s.K,
        s.W ∪ {a | (∃ σ ∈ s.K, σ.root = a) ∧ ∃ b M, inb b = some M ∧ a ∈ M.2}⟩
    else s
  output s := if s.round = R + T then some ((reconstruct s.K).induce s.W) else none

/-- The execution of Algorithm 5. -/
def alg5Cfg (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (R T : ℕ) :
    ℕ → V → Option (RPState L) :=
  config G id lab (alg5 R T) adv

/-- `V_x`: `x` together with every node that holds `σ_x` at the end of some round of Phase I
(including nodes that crash later). The propagation graph is `Γ_x = G[V_x]`. -/
def propSet (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (R T : ℕ)
    (x : V) : Set V :=
  {w | w = x ∨ ∃ r ≤ R, ∃ s, alg5Cfg G id lab adv R T r w = some s ∧ starOf G id lab x ∈ s.K}

/-- In Algorithm 5, `w` has not crashed and stores token `x` at the end of (global) round `r`. -/
def storesToken (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (R T : ℕ)
    (r : ℕ) (w x : V) : Prop :=
  ∃ s, alg5Cfg G id lab adv R T r w = some s ∧ id x ∈ s.W

/-- The crash pattern of the flooding execution of Lemma 12(i) on the nodes of `U`: nodes that
crashed before Phase II (in a round `≤ R`) are inactive from the start, a node crashing in Phase II
round `r` (global round `R + r`) crashes in round `r`, with the same delivery choices. -/
def floodAdv (adv : Adversary V) (R : ℕ) (U : Set V) : Adversary U where
  crashTime w :=
    match adv.crashTime w.val with
    | none => none
    | some s => if s ≤ R then some 0 else some (s - R)
  delivered u w := adv.delivered u.val w.val

/-- The three choices (2) of the number `T` of Phase II rounds, with the admissible executions of
each: `T = Δ ∑_{i=0}^{R-1} (Δ−1)^i` when `Δ ≥ 3` (any crashes); `T = c·Δ·R·f` for a known bound
`f ≥ 1` on the number of crashes (executions with at most `f` crashes); `T = 2R` when `Δ = 2` (any
crashes). -/
def Choice2 (c Δ R T : ℕ) (adv : Adversary V) : Prop :=
  (3 ≤ Δ ∧ T = Δ * ∑ i ∈ Finset.range R, (Δ - 1) ^ i) ∨
  (∃ f, 1 ≤ f ∧ T = c * Δ * R * f ∧ adv.crashCount ≤ f) ∨
  (Δ = 2 ∧ T = 2 * R)

end CrashLocal.ConsNbhd


