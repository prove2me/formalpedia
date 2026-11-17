-- Prove2me | Definitions.Def_PhysReaudit_Supplement_Strategy
-- name    : PhysReaudit_Supplement_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:24:27.201095+00:00
-- url     : https://prove2.me/theorems/f91af1e4-ae9b-46a1-8a39-fc31ac6156e6
-- title:
--   Predictable randomized coordinate-sampling strategies with Gaussian queries $Y=\theta_i+Z$ (App. D.1)
-- statement:
--   This file defines the query model of Appendix D.1.
--
--   Let $\theta\in\mathbb R^d$ be unknown. A query to coordinate $i$ returns
--   $$
--   Y=\theta_i+Z,\qquad Z\sim N(0,1),
--   $$
--   with noise independent across queries, at cost $c_i$.
--
--   1. A **strategy** draws a randomization $u$ from an arbitrary probability space, independent of the noise, and at each step decides from $u$ and the history of (coordinate, observed value) pairs so far whether to stop or which coordinate to query next. The decision is measurable in $u$ and the observed values for each fixed sequence of queried coordinates.
--   2. The **run** at parameter $\theta$: the $k$-th query overall, to coordinate $i_k$, returns $\theta_{i_k}+Z_k$, where $(Z_k)_{k\ge0}$ is the noise stream.
--   3. The **pathwise budget** $B$: for every $\theta$, every $u$ and every noise stream, the run stops after finitely many queries and $\sum_k c_{i_k}\le B$.
--   4. The **final history**: the history at the moment the run stops.
--
--   These are the predictable coordinate-sampling strategies with pathwise cost at most $B$ to which the adaptive lower bound of Theorem 18 applies; they include fixed designs (Proposition 17) as the special case of strategies that ignore the observations.
--
--   **Formalization Note** Drawing all randomization at the start is equivalent to fresh randomization at every step. Since each coordinate choice is predictable, each query reads a fresh entry $Z_k$ of an i.i.d. stream, which is the source's "noise variables are independent".
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), App. D.1 (Protocol, query class, and scope), p.21 (PDF p.22), display (8): "A query to coordinate i produces Y = θi + Z, Z ∼ N(0, 1), at cost ci > 0. Noise variables are independent. Adaptive coordinate choices and stopping rules depend only on past observations and independent randomization. Realized total cost is at most B on every sample path."

import Mathlib

namespace PhysReaudit.Supplement

/-- The history built from a list of queried coordinates `cs` and the values `ys` observed at them, in the
same order as `cs`. -/
def mkHist {d : ℕ} (cs : List (Fin d)) (ys : Fin cs.length → ℝ) : List (Fin d × ℝ) :=
  List.ofFn fun k => (cs.get k, ys k)

/-- A predictable, randomized coordinate-sampling strategy in the Gaussian query model
(Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026
(sha256 a20c437b…), App. D.1, p.21 (PDF p.22): "Adaptive coordinate choices and stopping rules depend only
on past observations and independent randomization").

The strategy draws a randomization `u ∈ U` once, independently of the noise, and then decides from `u` and
the history of (coordinate, observed value) pairs so far (most recent first) whether to stop (`none`) or
which coordinate `i` to query next (`some i`).

**Formalization Note** Drawing all randomization at the start is equivalent to fresh randomization at each
step. The decision is required to be measurable in `(u, observed values)` for each fixed list of queried
coordinates (every decision value has a measurable preimage). -/
structure Strategy (d : ℕ) (U : Type) [MeasurableSpace U] where
  /-- `none`: stop; `some i`: query coordinate `i` next. -/
  next : U → List (Fin d × ℝ) → Option (Fin d)
  /-- Measurability in the randomization and the observed values, for each list of queried coordinates. -/
  measurable_next : ∀ (cs : List (Fin d)) (o : Option (Fin d)),
    MeasurableSet {p : U × (Fin cs.length → ℝ) | next p.1 (mkHist cs p.2) = o}

/-- The state of a coordinate-sampling run: the history (most recent first) and whether it has stopped. -/
structure GState (d : ℕ) where
  hist : List (Fin d × ℝ)
  halted : Bool

/-- The run of strategy `S` at parameter `θ ∈ ℝ^d` (App. D.1, p.21 (PDF p.22), display (8):
"A query to coordinate i produces Y = θ_i + Z, Z ∼ N(0, 1)"), on the outcome `ω = (u, Z)`: the state after
`m` decisions. The `k`-th query overall (0-based) to coordinate `i` returns `θ i + Z k`; a stopped run does
not move.

**Formalization Note** Under `noiseLaw` the stream `Z` is i.i.d. `N(0, 1)` and independent of `u`; since the
choice of coordinate is predictable, every query sees a fresh independent standard Gaussian noise. -/
def grun {d : ℕ} {U : Type} [MeasurableSpace U] (S : Strategy d U) (θ : Fin d → ℝ)
    (ω : U × (ℕ → ℝ)) : ℕ → GState d
  | 0 => ⟨[], false⟩
  | m + 1 =>
    let s := grun S θ ω m
    if s.halted then s else
      match S.next ω.1 s.hist with
      | none => { s with halted := true }
      | some i => { s with hist := (i, θ i + ω.2 s.hist.length) :: s.hist }

/-- The total cost `Σ_k c_{i_k}` of the queries in a history. -/
def histCost {d : ℕ} (c : Fin d → ℝ) (h : List (Fin d × ℝ)) : ℝ :=
  (h.map fun p => c p.1).sum

/-- Pathwise budget (App. D.1, p.21 (PDF p.22): "Realized total cost is at most B on every sample path"):
for every parameter `θ`, randomization `u` and noise stream `Z`, the run stops after finitely many decisions
and the total cost of its queries is at most `B`. -/
def PathwiseBudget {d : ℕ} {U : Type} [MeasurableSpace U] (S : Strategy d U) (c : Fin d → ℝ)
    (B : ℝ) : Prop :=
  ∀ (θ : Fin d → ℝ) (ω : U × (ℕ → ℝ)), ∃ m,
    (grun S θ ω m).halted = true ∧ histCost c (grun S θ ω m).hist ≤ B

open Classical in
/-- The complete stopped transcript's history: the history at the first decision time at which the run has
stopped (empty if the run never stops, which a budgeted strategy excludes). -/
noncomputable def finalHist {d : ℕ} {U : Type} [MeasurableSpace U] (S : Strategy d U)
    (θ : Fin d → ℝ) (ω : U × (ℕ → ℝ)) : List (Fin d × ℝ) :=
  if h : ∃ m, (grun S θ ω m).halted = true then (grun S θ ω (Nat.find h)).hist else []

end PhysReaudit.Supplement


