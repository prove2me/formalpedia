-- Prove2me | Definitions.Def_PopRAM_SimProtocol
-- name    : PopRAM_SimProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:52.039303+00:00
-- url     : https://prove2.me/theorems/e5a72e91-fb3d-4d7c-aa93-e2c3a31c11bb
-- title:
--   Unary input and output of a simulation protocol
-- statement:
--   A **simulation protocol** with $T_R$ inputs and $T_P$ outputs is a population protocol with a finite state set $Q$, together with an input state $\iota(i)\in Q$ for every input variable $i$, a state $q_0\in Q$ in which every non-input agent starts, and an output map assigning to each state at most one output variable.
--
--   An input tuple $k$ is placed on $n$ agents by a **labelling** that labels exactly $k_i$ agents with input variable $i$; a labelled agent starts in $\iota(i)$ and every other agent in $q_0$. The **output count** of variable $j$ in a configuration $c$ is the number of agents whose state counts towards output $j$. For a target $b=(b_1,\dots,b_{T_P})$, the set $\mathrm{Correct}(b)$ consists of the configurations that are silent and have output counts exactly $b$.
--
--   Since silent configurations are absorbing, the first time a run enters $\mathrm{Correct}(b)$ is the stabilisation time of a silent protocol with output $b$: after it, no agent changes state.
--
--   **Formalization Note** The protocol is a bundled structure with `Fintype Q`; `HasCounts lab k` states that the labelling places exactly $k_i$ agents on variable $i$.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), abstract (PDF p.1); §2, p.5 (PDF p.6); p.6 (PDF p.7); p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PopRAM_Protocol
import Definitions.Def_PopRAM_PProgram

set_option autoImplicit false

namespace PopRAM

/-! # Unary input/output interface of a simulation protocol

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), abstract (PDF p.1); §2, p.5 (PDF p.6): "input Ai
is represented by a set Xi of |Xi| = Ai agents, and output Bi by a set Yi of |Yi| = Bi agents";
p.6 (PDF p.7): "Input variable i … ki agents in state in_i", "Sout = {out1, …, outTP}"; p.8 (PDF
p.9): "All other agents are initially leaders".

**Formalization Note**
- A protocol with `TR` inputs and `TP` outputs is a finite state type `Q` with a transition function
  `δ`, input states `ι i` for the input variables, one state `q₀` in which every non-input agent
  starts, and an output map `out : Q → Option (Fin TP)` (`out q = some j`: the state counts towards
  output `j`).
- An input tuple `k` is placed on the `n` agents by a labelling `lab : Fin n → Option (Fin TR)` with
  exactly `k i` agents labelled `i`; agent `a` starts in `ι i` if `lab a = some i` and in `q₀`
  otherwise. Every labelling with these counts is allowed.
- `Correct target` is the set of configurations that are **silent** and whose output counts equal
  `target`. Silent configurations are absorbing, so the first time the run enters `Correct target` is
  the stabilisation time of a silent protocol ("silent if no agent changes state after
  stabilisation", abstract). -/

/-- A population protocol with `TR` unary inputs and `TP` unary outputs. -/
structure SimProtocol (TR TP : ℕ) where
  /-- the state space -/
  Q : Type
  [fin : Fintype Q]
  [deq : DecidableEq Q]
  /-- the transition function, initiator first -/
  δ : Q → Q → Q × Q
  /-- the input state of each input variable -/
  ι : Fin TR → Q
  /-- the initial state of every non-input agent -/
  q₀ : Q
  /-- the output variable a state counts towards, if any -/
  out : Q → Option (Fin TP)

attribute [instance] SimProtocol.fin SimProtocol.deq

namespace SimProtocol

variable {TR TP : ℕ} (S : SimProtocol TR TP) {n : ℕ}

/-- The initial configuration of a labelling. -/
def init (lab : Fin n → Option (Fin TR)) : Fin n → S.Q :=
  fun a => (lab a).elim S.q₀ S.ι

/-- The number of agents counting towards output `j`. -/
def outCount (c : Fin n → S.Q) (j : Fin TP) : ℕ :=
  (Finset.univ.filter (fun a => S.out (c a) = some j)).card

/-- Silent configurations with output counts `target`. -/
def Correct (target : Fin TP → ℕ) : Set (Fin n → S.Q) :=
  {c | Silent S.δ c ∧ ∀ j, S.outCount c j = target j}

end SimProtocol

/-- The labelling `lab` places exactly `k i` agents on input variable `i`. -/
def HasCounts {TR n : ℕ} (lab : Fin n → Option (Fin TR)) (k : Fin TR → ℕ) : Prop :=
  ∀ i, (Finset.univ.filter (fun a => lab a = some i)).card = k i

end PopRAM


