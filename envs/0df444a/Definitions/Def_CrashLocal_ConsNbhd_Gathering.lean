-- Prove2me | Definitions.Def_CrashLocal_ConsNbhd_Gathering
-- name    : CrashLocal_ConsNbhd_Gathering
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:59:01.14419+00:00
-- url     : https://prove2.me/theorems/7eaed5fd-7b56-42bc-9f0e-26f5d1470ca0
-- title:
--   Algorithm 2 (full-information gathering), first receptions and Q_v
-- statement:
--   §5.1. A Star records a root identifier, the root's input label and the root's neighbor identifiers; starOf v = σ_v. reconstruct K is the labeled graph with the roots of K as nodes, an edge between two roots when one's star lists the other, and each root labeled from its star (for the genuine stars of a set Q of nodes this is G[Q]). gatherThen t fin is Algorithm 2 for t rounds followed by a local computation: K_v ← {σ_v}; in rounds 1, …, t send K_v to every neighbor and add every received star to K_v; at the end of round t output fin(own identifier, K_v) (the state is frozen afterwards). gather t returns K_v. For the execution of gather t: holdsStar r v x (v has σ_x at the end of round r), firstLearns r v x (holds it at round r and at no earlier round), receivesStar r u v x (in round r ≥ 1 the adjacent node u's message is delivered to v, which completes the round, and contains σ_x), Qset v = Q_v = {x : σ_x ∈ K_v} and Kset v = K_v at the end of round t.
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, §5.1 and Algorithm 2, pp. 23–24

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Model

noncomputable section
open Classical

namespace CrashLocal.ConsNbhd

/-- A labeled star as communicated (§3.3): the root's identifier, the root's input label and the
identifiers of the root's neighbors. -/
structure Star (L : Type) where
  root : ℕ
  label : L
  nbrs : Set ℕ

variable {V L : Type}

/-- The labeled star `σ_v = (v, N_G[v])` of `v`. -/
def starOf (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (v : V) : Star L :=
  ⟨id v, lab v, id '' G.neighborSet v⟩

/-- The labeled graph a node reconstructs from a collection `K` of stars: the roots of `K`, the
edges between two roots reported in a star, and each root's label from its star. For the genuine
stars of the nodes in `Q` this is `G[Q]`. -/
def reconstruct (K : Set (Star L)) : View L where
  nodes := {a | ∃ σ ∈ K, σ.root = a}
  edges := {e | ∃ σ ∈ K, ∃ τ ∈ K, τ.root ∈ σ.nbrs ∧ e = s(σ.root, τ.root)}
  label := fun a => if h : ∃ σ ∈ K, σ.root = a then some h.choose.label else none

/-- Local state of full-information gathering: own identifier, rounds completed, collected
stars `K_v`. -/
structure GatherState (L : Type) where
  me : ℕ
  round : ℕ
  K : Set (Star L)

/-- Algorithm 2 (full-information gathering) for `t` rounds, followed by a local computation
`fin (own identifier) K_v` at the end of round `t`. `K_v ← {σ_v}`; in rounds `r = 1, …, t` send
`K_v` to every neighbor and add all received stars to `K_v`. -/
def gatherThen {Out : Type} (t : ℕ) (fin : ℕ → Set (Star L) → Out) : NodeProgram L Out where
  State := GatherState L
  Msg := Set (Star L)
  init a l N := ⟨a, 0, {⟨a, l, N⟩}⟩
  send s _ := if s.round < t then s.K else ∅
  update s inb :=
    if s.round < t then ⟨s.me, s.round + 1, s.K ∪ {σ | ∃ b M, inb b = some M ∧ σ ∈ M}⟩ else s
  output s := if s.round = t then some (fin s.me s.K) else none

/-- Algorithm 2 for `t` rounds, returning `K_v`. -/
def gather (t : ℕ) : NodeProgram L (Set (Star L)) :=
  gatherThen t (fun _ K => K)

/-- The execution of Algorithm 2 for `t` rounds. -/
def gatherCfg (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (t : ℕ) :
    ℕ → V → Option (GatherState L) :=
  config G id lab (gather t) adv

/-- In Algorithm 2 (`t` rounds), `v` holds `σ_x` at the end of round `r`. -/
def holdsStar (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (t r : ℕ)
    (v x : V) : Prop :=
  ∃ s, gatherCfg G id lab adv t r v = some s ∧ starOf G id lab x ∈ s.K

/-- `v` first learns `σ_x` in round `r`. -/
def firstLearns (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (t r : ℕ)
    (v x : V) : Prop :=
  holdsStar G id lab adv t r v x ∧ ∀ r' < r, ¬ holdsStar G id lab adv t r' v x

/-- In round `r ≥ 1` of Algorithm 2, `v` completes the round and receives from `u` a message
containing `σ_x`. -/
def receivesStar (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (t r : ℕ)
    (u v x : V) : Prop :=
  G.Adj u v ∧ adv.alive r v ∧ ∃ M : Set (Star L),
    msgFrom G id (gather (L := L) t) adv (gatherCfg G id lab adv t (r - 1)) r u v = some M ∧
      starOf G id lab x ∈ M

/-- `Q_v = {x : σ_x ∈ K_v}` after Algorithm 2 for `t` rounds. -/
def Qset (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (t : ℕ) (v : V) :
    Set V :=
  {x | holdsStar G id lab adv t t v x}

/-- `K_v` at the end of Algorithm 2 for `t` rounds (`∅` if `v` crashed). -/
def Kset (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (adv : Adversary V) (t : ℕ) (v : V) :
    Set (Star L) :=
  match gatherCfg G id lab adv t t v with
  | some s => s.K
  | none => ∅

end CrashLocal.ConsNbhd


