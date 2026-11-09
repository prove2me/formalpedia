-- Prove2me | Definitions.Def_RandomQueryXOR_DetBP
-- name    : RandomQueryXOR_DetBP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:26.264385+00:00
-- url     : https://prove2.me/theorems/7f075210-ff01-4683-9cc3-592362bc86c1
-- title:
--   Deterministic layered branching program of width $W$ and length $T$
-- statement:
--   A **deterministic layered branching program** of width $W$ and length $T$ over a sample alphabet $A$ has layers $0,1,\dots,T$ with $W$ nodes each, a start node in layer $0$, for each layer $t<T$ and node $v$ one outgoing edge per possible sample $a\in A$ leading to a node of layer $t+1$, and an output bit on each node of layer $T$. On a sample sequence $a_1,\dots,a_T$ it follows the edges from the start node; $P_t$ denotes the node reached after the first $t$ samples, and the output is the label of $P_T$.
--
--   With $W=2^S$ the nodes of a layer are the $S$-bit memory states. In the random query model the samples are pairs $(i,x(i))$; in the gate-keeper model of §4.1 they are triples $(i,b,w(i))$.
--
--   **Formalization Note** Nodes of a layer are `Fin W`; `step t v a` is the node of layer $t+1$ reached from node $v$ of layer $t$ on sample $a$. `runFrom` runs the program from a given node and time over consecutive samples (times $\ge T$ leave the node unchanged); `stateAt a t` is $P_t$. A randomized program is a probability distribution on this finite set of deterministic programs.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, §3.1 (i)–(iv), pp.13–14 (PDF pp.15–16)

import Mathlib

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

/-- A deterministic layered branching program of width `W` and length `T` reading samples from
an alphabet `A` (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query
Model*, arXiv:2611.04353, §3.1 (i)–(iv), pp.13–14 = PDF pp.15–16): layers `0, …, T` of `W` nodes
each, a start node in layer `0`, for every layer `t < T` and node `v` an outgoing edge for every
possible sample `a ∈ A` (`step t v a` is the node of layer `t + 1` it leads to), and an output
bit on every node of the final layer.

**Formalization Note** Layers are indexed `0, …, T` and nodes of a layer by `Fin W` (the
paper's `S`-bit labels when `W = 2^S`). The samples of the random query model are
`A = ι × Bool` (pairs `(i, x(i))`), those of the gate-keeper model of §4.1 are
`ι × Bool × Option Bool` (triples `(i, b, w(i))`, `none` = ⊥). -/
structure DetBP (W : ℕ) (A : Type) (T : ℕ) where
  /-- the start node of layer `0` -/
  start : Fin W
  /-- `step t v a`: the node of layer `t + 1` reached from node `v` of layer `t` on sample `a` -/
  step : Fin T → Fin W → A → Fin W
  /-- the output labels of the final layer -/
  out : Fin W → Bool

namespace DetBP

variable {W T : ℕ} {A : Type}

/-- A deterministic program is its triple of start node, transition maps and output labels. -/
def equivProd : DetBP W A T ≃ Fin W × (Fin T → Fin W → A → Fin W) × (Fin W → Bool) where
  toFun P := (P.start, P.step, P.out)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype A] [DecidableEq A] : Fintype (DetBP W A T) :=
  Fintype.ofEquiv _ equivProd.symm

instance [Fintype A] [DecidableEq A] : DecidableEq (DetBP W A T) :=
  equivProd.decidableEq

/-- One step at time `s` (0-based) on the sample sequence `a`: from node `v` of layer `s` to the
node of layer `s + 1` along the edge labelled `a s`; times `s ≥ T` leave the node unchanged. -/
def stepAt (P : DetBP W A T) (a : Fin T → A) (s : ℕ) (v : Fin W) : Fin W :=
  if h : s < T then P.step ⟨s, h⟩ v (a ⟨s, h⟩) else v

/-- `runFrom P a s₀ v m`: the node reached after processing the samples at times
`s₀, s₀ + 1, …, s₀ + m − 1` starting from node `v` (of layer `s₀`). -/
def runFrom (P : DetBP W A T) (a : Fin T → A) (s₀ : ℕ) (v : Fin W) : ℕ → Fin W
  | 0 => v
  | m + 1 => P.stepAt a (s₀ + m) (P.runFrom a s₀ v m)

/-- `P_t`: the node (label) reached after processing the first `t` samples `a 0, …, a (t-1)`
(`P_0` is the start node; `P_t = P_T` for `t ≥ T`). -/
def stateAt (P : DetBP W A T) (a : Fin T → A) (t : ℕ) : Fin W :=
  P.runFrom a 0 P.start t

/-- The output of the program on the sample sequence `a`: the label of the final node `P_T`. -/
def output (P : DetBP W A T) (a : Fin T → A) : Bool :=
  P.out (P.stateAt a T)

end DetBP

end RandomQueryXOR


