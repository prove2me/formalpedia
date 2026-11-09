-- Prove2me | Definitions.Def_WeakGraphOracles_OneSided_protocol
-- name    : WeakGraphOracles_OneSided_protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:18:26.361588+00:00
-- url     : https://prove2.me/theorems/4a52f97e-fc3e-4f8a-a30c-9a22b131d529
-- title:
--   Finite-depth randomized oracle policies
-- statement:
--   An adaptive oracle program chooses each query using its earlier replies and internal coins. For query alphabet $Q$, reply alphabet $R$, and a natural query bound $q$, a deterministic plan is a tree of depth at most $q$, with an accept/reject decision at a leaf. A randomized policy is an arbitrary probability distribution over those complete plans. Execution with response kernel $K$ draws a fresh reply from $K(a)$ after query $a$ and records the transcript.
--
--   $$\Pr_{A,K}[B]=\sum_{t}A(t)\Pr_{t,K}[B].$$
--
--   This reusable oracle-protocol layer imposes neither a running-time bound nor any access to a hidden input. For the finite alphabets used here, randomizing the complete plan represents all internal randomization, including correlated coins and early stopping. Event probabilities come from normalized discrete probability laws, with no integration defaults.
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 5 (PDF p. 6), Definition 1; pp. 5–6 (PDF pp. 6–7), Remark 2

import Mathlib

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- A deterministic adaptive oracle program with at most `q` calls. Randomizing
its complete contingent plan includes correlated internal coins and early stopping.
The program has no argument containing the hidden input. -/
inductive QueryTree (Q R : Type) : ℕ → Type
  | stop {q : ℕ} (accept : Bool) : QueryTree Q R q
  | ask {q : ℕ} (query : Q) (next : R → QueryTree Q R q) : QueryTree Q R (q + 1)

abbrev RandomPolicy (Q R : Type) (q : ℕ) := PMF (QueryTree Q R q)

/-- Execution uses a fresh kernel sample at each query, preserving the transcript. -/
noncomputable def executeTree {Q R : Type} (kernel : Q → PMF R) :
    {q : ℕ} → QueryTree Q R q → PMF (Bool × List (Q × R))
  | _, .stop b => PMF.pure (b, [])
  | _, .ask a next => (kernel a).bind fun r =>
      (executeTree kernel (next r)).map fun out => (out.1, (a, r) :: out.2)

noncomputable def executePolicy {Q R : Type} {q : ℕ}
    (kernel : Q → PMF R) (A : RandomPolicy Q R q) : PMF (Bool × List (Q × R)) :=
  A.bind (executeTree kernel)

/-- Real probability of an event in a normalized discrete probability law.
Mapping to Bool avoids any integral or measurability default. -/
noncomputable def eventProbability {X : Type} (μ : PMF X) (P : X → Prop) : ℝ := by
  classical
  exact ((μ.map (fun x => decide (P x))) true).toReal

end WeakGraphOracles.OneSided


