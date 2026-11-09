-- Prove2me | Definitions.Def_LocalPush_SeedRun
-- name    : LocalPush_SeedRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:07:31.826288+00:00
-- url     : https://prove2.me/theorems/e2b4d9c4-2992-483c-8192-67d8499fc1e5
-- title:
--   Algorithm 3 driven by a randomized solver on a seed sequence, and the good event $\mathcal G$
-- statement:
--   Model the randomized solver of line 6 of Algorithm 3 as a function $\mathrm{sol}(S,\omega)$ of the active set $S$ and a seed $\omega$ from a probability space $\Omega$. Running Algorithm 3 on a seed sequence $\omega_0,\omega_1,\dots$ uses seed $\omega_i$ for call $i$; the output is restricted to $S_i$ and extended by zero. The run returns at the first iteration whose output satisfies the stopping rule and otherwise expands by line 10, so $S_i$ is determined by $\omega_0,\dots,\omega_{i-1}$.
--
--   The good event $\mathcal G$ is the set of seed sequences on which every invoked call (every reached iteration) returns an output satisfying the guarantee (6).
--
--   This is the probability space on which Lemma 5.3 bounds $\Pr\{\mathcal G\}$.
--
--   **Formalization Note** `seedSets` returns `some` $S_i$ while the run is active and `none` after it has returned.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), Algorithm 3, p.18 (PDF p.18); the event 𝒢, p.19 (PDF p.19)

import Mathlib
import Definitions.Def_LocalPush_GoodTraj

open Finset Matrix

namespace LocalPush

/-!
# Algorithm 3 driven by a randomized solver: the run on a seed sequence and the good event `𝒢`

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), Algorithm 3, p.18 (PDF p.18), and
the event `𝒢`, p.19: "let 𝒢 be the "good" event that every approximate SDD call invoked by Algorithm 3
satisfies the guarantee (6)."

**Formalization Note.**
* The randomized solver of line 6 is a function `sol : Finset V → Ω → (V → ℝ)`: call `i` on the active set `S`
  returns `sol S (ω i)`, where `ω : ℕ → Ω` is a sequence of seeds, one fresh seed per call. Only the entries on
  `S` are used: the output is restricted to `S` and extended by zero (`solOut`), as on p.17.
* `seedSets … ω i` is `some S_i` when iteration `i` is reached on the seeds `ω` and `none` once the run has
  returned. The run follows lines 6–10 exactly: it returns at the first iteration whose output satisfies the
  stopping rule, and otherwise expands by line 10. `S_i` depends only on `ω 0, …, ω (i−1)`.
* `goodEvent` is `𝒢`: every call that is invoked (every reached iteration) returns an output satisfying (6).
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The solver output of a call on `S` with seed `ω`, restricted to `S` and extended by zero. -/
def solOut {Ω : Type*} (sol : Finset V → Ω → V → ℝ) (S : Finset V) (ω : Ω) : V → ℝ :=
  ext S (restr S (sol S ω))

open scoped Classical in
/-- The active set of iteration `i` of Algorithm 3 run on the seed sequence `ω`, or `none` if the run has
returned before iteration `i`. -/
noncomputable def seedSets (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam η κ : ℝ)
    {Ω : Type*} (sol : Finset V → Ω → V → ℝ) (ω : ℕ → Ω) : ℕ → Option (Finset V)
  | 0 => some {s}
  | i + 1 =>
    match seedSets G s α lam η κ sol ω i with
    | none => none
    | some S =>
      if StopRule G s α lam η S (solOut sol S (ω i)) then none
      else some (expand G s α lam κ S (solOut sol S (ω i)))

/-- The good event `𝒢` (p.19): every invoked solver call satisfies (6). -/
def goodEvent (G : SimpleGraph V) [DecidableRel G.Adj] (s : V) (α lam η κ : ℝ)
    {Ω : Type*} (sol : Finset V → Ω → V → ℝ) : Set (ℕ → Ω) :=
  {ω | ∀ (i : ℕ) (S : Finset V), seedSets G s α lam η κ sol ω i = some S →
    SolveGood G s α lam κ S (solOut sol S (ω i))}

end LocalPush


