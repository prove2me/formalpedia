-- Prove2me | Definitions.Def_MinSumClust_Alg3Step
-- name    : MinSumClust_Alg3Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:49.831038+00:00
-- url     : https://prove2.me/theorems/3eeae831-a203-49f0-88af-e3b9a3f89e05
-- title:
--   Algorithm 3 (dual fitting, forward stage) as a run relation
-- statement:
--   Algorithm 3 (p.24) starts at time $\theta=0$ with $\alpha=0$, every client active, nothing opened and no indirect connection. While $A\ne\emptyset$, one of three steps happens:
--
--   1. **Open a cluster.** If Algorithm 2 returns $S$, the cluster $S$ is opened: $D_A(S)=S\cap A$ is recorded, the dependency forest is updated, and $S$ is removed from $A$.
--   2. **Connect a client.** If an active client $j$ and an opened cluster $S$ satisfy $\alpha_j\ge\gamma_{IC}\cdot d(j,S)$, then $j$ leaves $A$ and $C_I(j)=S$.
--   3. **Grow.** Every active $\alpha_j$ is raised uniformly from $\theta$ to $\theta'>\theta$; this is allowed only if no event (Algorithm 2 returning a set, or a connection condition) is enabled at any time in $[\theta,\theta')$.
--
--   A state is **reachable** if some sequence of steps leads to it from the initial state ("throughout the algorithm"); a run is **complete** when no client is active. The final $\alpha$ of a complete run is the dual solution $\alpha^*$, its opened clusters are $\mathcal S$.
--
--   **Formalization Note** Growth stops at the first time an event is enabled; simultaneous enabled events fire one at a time, in any order. Every milestone about Algorithm 3 quantifies over all runs.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Algorithm 3, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_Alg3State
import Definitions.Def_MinSumClust_Alg2Returns

namespace MinSumClust

/-- The state after the uniform growth up to time `θ′`: every active `α_j` becomes `θ′`. -/
def Alg3State.grow {n : ℕ} (σ : Alg3State n) (θ' : ℝ) : Alg3State n :=
  { σ with θ := θ', α := fun j => if j ∈ σ.A then θ' else σ.α j }

/-- An event of Algorithm 3 is enabled in `σ`: Algorithm 2 returns a set (step 1), or some active
`j` and opened `S` have `α_j ≥ γ_IC · d(j, S)` (step 2). -/
def Alg3Enabled {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) : Prop :=
  (∃ S, Alg2Returns P σ S) ∨
    ∃ j ∈ σ.A, ∃ t < σ.hist.length, P.γIC * dist1 P.d j (histGet σ.hist t).1 ≤ σ.α j

/-- **Algorithm 3 (Dual Fitting – the forward stage)**, p.24 (PDF p.26), one step at a time. While
`A ≠ ∅`:

* `openCluster`: Algorithm 2 returns `S`; record `(S, S ∩ A)` (this creates the node of `S` and
  updates the forest, `forestParent`), and remove `S` from `A`;
* `connect`: an active `j` and an opened `S_t` have `α_j ≥ γ_IC · d(j, S_t)`; remove `j` from `A`
  and set `C_I(j) = S_t`;
* `grow`: raise every active `α_j` uniformly from `θ` to `θ′ > θ`, allowed only if no event is
  enabled at any time in `[θ, θ′)`.

**Formalization Note.** Growth stops at the first time an event becomes enabled, and enabled events
fire one at a time in any order (the paper does not order simultaneous events). -/
inductive Alg3Step {n : ℕ} (P : Alg3Params n) : Alg3State n → Alg3State n → Prop
  | openCluster (σ : Alg3State n) (S : Finset (Fin n)) (hA : σ.A.Nonempty)
      (h : Alg2Returns P σ S) :
      Alg3Step P σ { σ with hist := σ.hist ++ [(S, S ∩ σ.A)], A := σ.A \ S }
  | connect (σ : Alg3State n) (j : Fin n) (t : ℕ) (hj : j ∈ σ.A) (ht : t < σ.hist.length)
      (h : P.γIC * dist1 P.d j (histGet σ.hist t).1 ≤ σ.α j) :
      Alg3Step P σ { σ with A := σ.A.erase j, CI := Function.update σ.CI j (some t) }
  | grow (σ : Alg3State n) (θ' : ℝ) (hA : σ.A.Nonempty) (hθ : σ.θ < θ')
      (h : ∀ θ'', σ.θ ≤ θ'' → θ'' < θ' → ¬ Alg3Enabled P (σ.grow θ'')) :
      Alg3Step P σ (σ.grow θ')

/-- The initial state of Algorithm 3: `θ = 0`, `α = 0`, `A = D`, nothing opened, `C_I = ∅`. -/
def Alg3State.init (n : ℕ) : Alg3State n :=
  ⟨0, fun _ => 0, Finset.univ, [], fun _ => none⟩

/-- A state reachable by some run of Algorithm 3 ("throughout the algorithm"). -/
def Alg3Reachable {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) : Prop :=
  Relation.ReflTransGen (Alg3Step P) (Alg3State.init n) σ

/-- A complete run of Algorithm 3: a reachable state with no active client. Its `α` is the final
dual solution `α*`, its `hist` the opened clusters `𝒮`, its `CI` the indirect connections. -/
def Alg3Complete {n : ℕ} (P : Alg3Params n) (σ : Alg3State n) : Prop :=
  Alg3Reachable P σ ∧ σ.A = ∅

end MinSumClust


