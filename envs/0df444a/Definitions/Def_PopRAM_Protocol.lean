-- Prove2me | Definitions.Def_PopRAM_Protocol
-- name    : PopRAM_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:07.869719+00:00
-- url     : https://prove2.me/theorems/b1a6345c-f938-4ff9-9357-356f347f3ef0
-- title:
--   Population protocols under the uniform random scheduler
-- statement:
--   A **population protocol** consists of a set $Q$ of states and a deterministic transition function $\delta : Q\times Q\to Q\times Q$. We write $A + B \to A' + B'$ when $\delta(A,B)=(A',B')$: an interaction between an **initiator** in state $A$ and a **responder** in state $B$ changes their states to $A'$ and $B'$.
--
--   A population of $n$ agents is indexed by $\{0,\dots,n-1\}$, and a **configuration** assigns a state to every agent. A **schedule** is a sequence $\omega=(\omega_0,\omega_1,\dots)$ of ordered pairs $(i,j)$ of distinct agents; under the **uniform random scheduler** the pairs $\omega_t$ are independent and uniformly distributed over the $n(n-1)$ ordered pairs of distinct agents. The **run** from a configuration $c_0$ is $C_0=c_0$ and $C_{t+1}$ = $C_t$ with the initiator $i$ and responder $j$ of $\omega_t$ updated by $\delta(C_t(i),C_t(j))$, all other agents unchanged; $C_t$ is the configuration after $t$ interactions.
--
--   A configuration $c'$ is **reachable** from $c$ if some finite sequence of interactions leads from $c$ to $c'$. A configuration $c$ is **silent** if no interaction of two distinct agents changes any state: $\delta(c(i),c(j))=(c(i),c(j))$ for all $i\ne j$. For a set $S$ of configurations, the **hitting time** $\tau_S(\omega)\in\mathbb N\cup\{\infty\}$ is the least $t$ with $C_t\in S$ ($\infty$ if none). The (parallel) **time** of the paper is the number of interactions divided by $n$.
--
--   These are the objects in which every statement of the mission is phrased.
--
--   **Formalization Note** Configurations are functions $\mathrm{Fin}\,n\to Q$. The scheduler law is the infinite product of the uniform law on ordered pairs (`Measure.infinitePi`); for $n<2$ no pair exists and the law is the zero measure, so every probabilistic statement assumes $n\ge 2$. All bounds are stated in interactions. `whpBound n η` is $n^{-\eta}$.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), abstract (PDF p.1) and §1, p.1 (PDF p.2)

import Mathlib

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace PopRAM

/-! # Population protocols under the uniform random scheduler

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), abstract (PDF p.1) and §1, p.1 (PDF p.2):
"a random scheduler selects an ordered pair of distinct agents, called the initiator and the
responder, uniformly at random at each step"; "We write a transition as A + B → A′ + B′".

**Formalization Note** A protocol is a state type `Q` with a deterministic transition function
`δ : Q → Q → Q × Q`; in `δ a b` the first argument is the initiator and the second the responder.
The population is `Fin n`, a configuration is `Fin n → Q` (agents are indistinguishable, so this
carries the same information as a multiset of states). A schedule is `ω : ℕ → Pair n`, where
`Pair n` is the type of ordered pairs of distinct agents; its law `sched n` is the infinite product
of the uniform law on `Pair n` (i.i.d. uniform pairs). For `n < 2` there is no pair and `sched n` is
the zero measure; every statement of the mission that uses `sched n` assumes `2 ≤ n`. Time is
measured in interactions: the paper's parallel time `X` is `n · X` interactions. -/

/-- Ordered pairs `(initiator, responder)` of distinct agents. -/
def Pair (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≠ p.2}

instance (n : ℕ) : Fintype (Pair n) := by unfold Pair; infer_instance

instance (n : ℕ) : DecidableEq (Pair n) := by unfold Pair; infer_instance

/-- The discrete σ-algebra on pairs. -/
instance (n : ℕ) : MeasurableSpace (Pair n) := ⊤

/-- The uniform law on the ordered pairs of distinct agents (`n ≥ 2`). -/
noncomputable def pairPMF (n : ℕ) (h : 2 ≤ n) : PMF (Pair n) :=
  haveI : Nonempty (Pair n) :=
    ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩⟩
  PMF.uniformOfFintype (Pair n)

/-- The law of the random scheduler: i.i.d. uniform ordered pairs of distinct agents. It is the
zero measure when `n < 2` (no pair exists). -/
noncomputable def sched (n : ℕ) : Measure (ℕ → Pair n) :=
  if h : 2 ≤ n then Measure.infinitePi (fun _ : ℕ => (pairPMF n h).toMeasure) else 0

/-- One interaction: the initiator `p.1.1` and the responder `p.1.2` apply `δ`; all other agents are
unchanged. -/
def step {Q : Type*} {n : ℕ} (δ : Q → Q → Q × Q) (c : Fin n → Q) (p : Pair n) : Fin n → Q :=
  fun a =>
    if a = p.1.1 then (δ (c p.1.1) (c p.1.2)).1
    else if a = p.1.2 then (δ (c p.1.1) (c p.1.2)).2
    else c a

/-- The run from `c₀` on schedule `ω`: `run δ c₀ ω t` is the configuration after `t` interactions. -/
def run {Q : Type*} {n : ℕ} (δ : Q → Q → Q × Q) (c₀ : Fin n → Q) (ω : ℕ → Pair n) :
    ℕ → (Fin n → Q)
  | 0 => c₀
  | t + 1 => step δ (run δ c₀ ω t) (ω t)

/-- `c'` is reachable from `c` in zero or more interactions. -/
def Reachable {Q : Type*} {n : ℕ} (δ : Q → Q → Q × Q) : (Fin n → Q) → (Fin n → Q) → Prop :=
  Relation.ReflTransGen (fun c c' => ∃ p : Pair n, c' = step δ c p)

/-- A configuration is **silent** when no interaction of two distinct agents changes any state. -/
def Silent {Q : Type*} {n : ℕ} (δ : Q → Q → Q × Q) (c : Fin n → Q) : Prop :=
  ∀ i j : Fin n, i ≠ j → δ (c i) (c j) = (c i, c j)

/-- The hitting time of a set `S` of configurations: the least number of interactions `t` with
`run δ c₀ ω t ∈ S`, and `⊤` if there is none. -/
noncomputable def hit {Q : Type*} {n : ℕ} (δ : Q → Q → Q × Q) (c₀ : Fin n → Q)
    (S : Set (Fin n → Q)) (ω : ℕ → Pair n) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : run δ c₀ ω t ∈ S), (t : ℕ∞)

/-- The number of agents whose state satisfies `p`. -/
def countIn {Q : Type*} {n : ℕ} (c : Fin n → Q) (p : Q → Prop) [DecidablePred p] : ℕ :=
  (Finset.univ.filter (fun a => p (c a))).card

/-- The high-probability failure bound `n^{-η}` as an extended nonnegative real. -/
noncomputable def whpBound (n : ℕ) (η : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n : ℝ) ^ (-η))

end PopRAM


