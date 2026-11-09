-- Prove2me | Definitions.Def_HarmonicKServer_Competitive_Harmonic
-- name    : HarmonicKServer_Competitive_Harmonic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:31.586217+00:00
-- url     : https://prove2.me/theorems/33b4a0d9-6725-4801-8ba4-237a5831ec99
-- title:
--   §2 — Harmonic transition and causal adversary service
-- statement:
--   A configuration is a tuple $X:[k]\to V$, with repeated positions allowed. A request $r$ is covered when $x_i=r$ for some label. Harmonic stays put on a covered request. Otherwise, it selects label $i$ with probability
--   $$p_i(X,r)=\frac{1}{Z_rd(x_i,r)},\qquad Z_r=\sum_j\frac1{d(x_j,r)},$$
--   and moves precisely that server to $r$. The cost is the sum of labelled movement distances from the imported configuration model.
--
--   An adversary policy maps a list of completed online choices to a request and a finite service schedule of labelled moves. Each move is charged, and executing the schedule gives the adversary's configuration before the fresh online label is drawn. Iteration computes both configurations and both accumulated costs. Validity requires covering the selected request after service; laziness is a separate optional predicate, never part of general validity. Any deterministic policy based on the complete public past has this representation, since the past requests, configurations and actions can all be reconstructed from its completed label history and initial data.
--
--   **Formalization Note** A covered request uses the deterministic dummy label zero; all branches leave the configuration fixed and cost zero. At $k=0$ that dummy law is not a probability distribution, so every algorithm theorem requires $k\ge1$. Service schedules allow extra moves and detours, with no injectivity restriction on either initial tuple. Endpoint schedules are finite in the usual discrete server model; any longer trajectory can be shortened causally to its endpoint moves without increasing adversary cost.
-- source:
--   Yichen Huang, STOC 2027 submission #95 (October 2026), p. 3, §2, configurations, transition, adaptive order and lazy convention (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/95.pdf; pinned PDF SHA256 20635ef9c29593d01fa406f1a63fdc6b98250e5fc1b1b5c4ed088b407a4e8fd6. Title-page date: November 3, 2026; canonical metadata citation: October 2026.

import Mathlib
import Definitions.Def_KServer_model

namespace HarmonicKServer.Competitive
open scoped BigOperators

abbrev History (k : ℕ) := List (Fin k)

def Covers {k : ℕ} {V : Type*} (X : KServer.Config k V) (r : V) : Prop :=
  ∃ i, X i = r

noncomputable def relocate {k : ℕ} {V : Type*}
    (X : KServer.Config k V) (i : Fin k) (r : V) : KServer.Config k V :=
  Function.update X i r

noncomputable def harmonicNext {k : ℕ} {V : Type*}
    (X : KServer.Config k V) (r : V) (i : Fin k) : KServer.Config k V := by
  classical
  exact if Covers X r then X else relocate X i r

noncomputable def normalizer {k : ℕ} {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (r : V) : ℝ := ∑ j, 1 / dist (X j) r

/-- On a covered request the label is a deterministic, unobserved dummy (label zero). -/
noncomputable def harmonicProbability {k : ℕ} {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (r : V) (i : Fin k) : ℝ := by
  classical
  exact if Covers X r then (if i.val = 0 then 1 else 0)
    else 1 / (normalizer X r * dist (X i) r)

noncomputable def harmonicCost {k : ℕ} {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (r : V) (i : Fin k) : ℝ :=
  KServer.moveCost X (harmonicNext X r i)

/-- Every move in a service schedule is explicitly charged, including detours. -/
abbrev Moves (k : ℕ) (V : Type*) := List (Fin k × V)

noncomputable def execute {k : ℕ} {V : Type*} :
    KServer.Config k V → Moves k V → KServer.Config k V
  | Y, [] => Y
  | Y, (i,r) :: ms => execute (relocate Y i r) ms

noncomputable def travel {k : ℕ} {V : Type*} [MetricSpace V] :
    KServer.Config k V → Moves k V → ℝ
  | _, [] => 0
  | Y, (i,r) :: ms => dist (Y i) r + travel (relocate Y i r) ms

structure Action (k : ℕ) (V : Type*) where
  request : V
  moves : Moves k V

/-- The input contains only completed online choices, never the current fresh label. -/
abbrev Adversary (k : ℕ) (V : Type*) := History k → Action k V

structure State (k : ℕ) (V : Type*) where
  online : KServer.Config k V
  adversary : KServer.Config k V
  onlineCost : ℝ
  adversaryCost : ℝ

noncomputable def initial {k : ℕ} {V : Type*}
    (X Y : KServer.Config k V) : State k V := ⟨X,Y,0,0⟩

noncomputable def advance {k : ℕ} {V : Type*} [MetricSpace V]
    (S : State k V) (a : Action k V) (i : Fin k) : State k V :=
  ⟨harmonicNext S.online a.request i, execute S.adversary a.moves,
    S.onlineCost + harmonicCost S.online a.request i,
    S.adversaryCost + travel S.adversary a.moves⟩

noncomputable def runFrom {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) : History k → State k V → List (Fin k) → State k V
  | _, S, [] => S
  | h, S, i :: tail => runFrom A (h ++ [i]) (advance S (A h) i) tail

noncomputable def stateAt {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (h : History k) : State k V :=
  runFrom A [] (initial X Y) h

def ValidAdversary {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) : Prop :=
  ∀ h, Covers (execute (stateAt A X Y h).adversary (A h).moves) (A h).request

def LazyAdversary {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) : Prop := by
  classical
  exact ∀ h, let S := stateAt A X Y h
    if Covers S.adversary (A h).request then (A h).moves = []
    else ∃ i, (A h).moves = [(i, (A h).request)]

end HarmonicKServer.Competitive


