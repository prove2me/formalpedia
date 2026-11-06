-- Prove2me | Definitions.Def_UninformedMG_Game
-- name    : UninformedMG_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:29.054104+00:00
-- url     : https://prove2.me/theorems/a5c8f103-c9aa-4d80-83cf-886ba52c8c63
-- title:
--   Episodic two-player layered Markov game $(S_h, A_h, B_h, P_h, \ell_h)_{h\le H}$
-- statement:
--   An **episodic two-player Markov game** with $H$ steps consists of
--
--   1. finite nonempty **state layers** $S_1,\dots,S_H$ and a **terminal layer** $S_{H+1}=\{s_{H+1}\}$ with a single state; states at different steps belong to different layers;
--   2. at each step $h\in[H]$, finite nonempty **action sets** $A_h$ of the learner and $B_h$ of the opponent;
--   3. **transition probabilities** $P_h(\cdot\mid s,a,b)\in\Delta(S_{h+1})$ for $s\in S_h$, $a\in A_h$, $b\in B_h$;
--   4. **losses** $\ell_h(s,a,b)\in[0,1]$.
--
--   The number of nonterminal states is $S=\sum_{h=1}^H|S_h|$. A **Markov policy** of the learner is a family $\mu_h(\cdot\mid s)\in\Delta(A_h)$, $s\in S_h$; a Markov policy of the opponent is $\nu_h(\cdot\mid s)\in\Delta(B_h)$. A **trajectory** lists the states $s_1,\dots,s_{H+1}$ and both players' actions $a_h,b_h$.
--
--   This is the model of the whole mission: the transitions and losses are fixed and unknown to the learner, which knows neither the opponent's action sets nor its actions.
--
--   **Formalization Note** Steps are 0-based: Lean layer $h\in\{0,\dots,H\}$ is the paper's step $h+1$, and Lean layer $H$ is the terminal layer. A step-$h$ transition goes from layer `h.castSucc` to layer `h.succ`. Layers are distinct types. States and actions carry the discrete $\sigma$-algebra. Policies are real tables, and validity is the separate predicates `IsLPolicy`/`IsOPolicy`.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Section 1.1, pp.1–2 (PDF pp.3–4)

import Mathlib

namespace UninformedMG

/-- **Episodic two-player layered Markov game** (Section 1.1, p.2 = PDF p.4).
Liu, Luo, Ratliff, Zhang, *Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games*,
arXiv:2611.01649 (held version, sha256 1d229c89…), Section 1.1, pp.1–2.

`H` steps; at step `h` a finite nonempty state layer `S_h`, finite nonempty learner actions `A_h`
and opponent actions `B_h`; a terminal singleton layer `S_{H+1}`; transitions
`P_h(· | s, a, b) ∈ Δ(S_{h+1})`; losses `ℓ_h(s, a, b) ∈ [0, 1]`.

**Formalization Note.** Steps are 0-based: the Lean layer `h : Fin (H + 1)` is the paper's step
`h + 1`, and the Lean layer `Fin.last H` is the terminal layer `S_{H+1}`, which has exactly one
element. Actions are indexed by `h : Fin H` (paper step `h + 1`), and a transition at step `h`
goes from layer `h.castSucc` to layer `h.succ`. Layers are distinct types, which makes the
paper's "states at different steps belong to disjoint sets" automatic. -/
structure Game (H : ℕ) where
  /-- The state layer `S_{h+1}` (Lean `h`), `h = 0, …, H`; `Fin.last H` is the terminal layer. -/
  St : Fin (H + 1) → Type
  [stFintype : ∀ h, Fintype (St h)]
  [stDecEq : ∀ h, DecidableEq (St h)]
  [stNonempty : ∀ h, Nonempty (St h)]
  /-- The terminal layer `S_{H+1}` is a singleton. -/
  terminal : Unique (St (Fin.last H))
  /-- The learner's action set `A_{h+1}` at Lean step `h`. -/
  Act : Fin H → Type
  [actFintype : ∀ h, Fintype (Act h)]
  [actDecEq : ∀ h, DecidableEq (Act h)]
  [actNonempty : ∀ h, Nonempty (Act h)]
  /-- The opponent's action set `B_{h+1}` at Lean step `h` (unknown to the learner). -/
  Opp : Fin H → Type
  [oppFintype : ∀ h, Fintype (Opp h)]
  [oppDecEq : ∀ h, DecidableEq (Opp h)]
  [oppNonempty : ∀ h, Nonempty (Opp h)]
  /-- Transition probabilities `P_h(s' | s, a, b)`. -/
  trans : (h : Fin H) → St h.castSucc → Act h → Opp h → St h.succ → ℝ
  trans_nonneg : ∀ h s a b s', 0 ≤ trans h s a b s'
  trans_sum : ∀ h s a b, ∑ s', trans h s a b s' = 1
  /-- Losses `ℓ_h(s, a, b)`. -/
  loss : (h : Fin H) → St h.castSucc → Act h → Opp h → ℝ
  loss_nonneg : ∀ h s a b, 0 ≤ loss h s a b
  loss_le_one : ∀ h s a b, loss h s a b ≤ 1

attribute [instance] Game.stFintype Game.stDecEq Game.stNonempty Game.actFintype Game.actDecEq
  Game.actNonempty Game.oppFintype Game.oppDecEq Game.oppNonempty

variable {H : ℕ}

/-- States, actions and opponent actions carry the discrete σ-algebra. -/
instance Game.measSt (G : Game H) (h : Fin (H + 1)) : MeasurableSpace (G.St h) := ⊤
instance Game.measAct (G : Game H) (h : Fin H) : MeasurableSpace (G.Act h) := ⊤
instance Game.measOpp (G : Game H) (h : Fin H) : MeasurableSpace (G.Opp h) := ⊤

instance Game.discSt (G : Game H) (h : Fin (H + 1)) : DiscreteMeasurableSpace (G.St h) :=
  ⟨fun _ => trivial⟩
instance Game.discAct (G : Game H) (h : Fin H) : DiscreteMeasurableSpace (G.Act h) :=
  ⟨fun _ => trivial⟩
instance Game.discOpp (G : Game H) (h : Fin H) : DiscreteMeasurableSpace (G.Opp h) :=
  ⟨fun _ => trivial⟩

/-- The number `S = ∑_{h=1}^H |S_h|` of nonterminal states (p.2). -/
def Game.numStates (G : Game H) : ℕ := ∑ h : Fin H, Fintype.card (G.St h.castSucc)

/-- A Markov policy of the learner, `μ_h(a | s)`, as a table (validity is `IsLPolicy`). -/
abbrev LPolicy (G : Game H) := (h : Fin H) → G.St h.castSucc → G.Act h → ℝ

/-- A Markov policy of the opponent, `ν_h(b | s)`, as a table (validity is `IsOPolicy`). -/
abbrev OPolicy (G : Game H) := (h : Fin H) → G.St h.castSucc → G.Opp h → ℝ

/-- `μ` is a Markov policy: `μ_h(· | s) ∈ Δ(A_h)` for every step and state. -/
def IsLPolicy (G : Game H) (μ : LPolicy G) : Prop :=
  ∀ h s, μ h s ∈ stdSimplex ℝ (G.Act h)

/-- `ν` is a Markov policy of the opponent: `ν_h(· | s) ∈ Δ(B_h)`. -/
def IsOPolicy (G : Game H) (ν : OPolicy G) : Prop :=
  ∀ h s, ν h s ∈ stdSimplex ℝ (G.Opp h)

/-- One episode's trajectory: states `s_1, …, s_{H+1}` (Lean layers `0, …, H`), the learner's
actions `a_h` and the opponent's actions `b_h`. -/
structure Traj (G : Game H) where
  st : (h : Fin (H + 1)) → G.St h
  act : (h : Fin H) → G.Act h
  opp : (h : Fin H) → G.Opp h

end UninformedMG


