-- Prove2me | Definitions.Def_TemporalVoter_voterLaw
-- name    : TemporalVoter_voterLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:04.875015+00:00
-- url     : https://prove2.me/theorems/af0f31b9-a39e-4b4d-8f89-ccc255faded5
-- title:
--   Standard $\kappa$-opinion voter model on a temporal graph (path law) and consensus
-- statement:
--   Let $\mathcal G=(G_t)$ be a temporal graph with fixed degrees on $V$, let $k\ge1$ and let $\sigma_0:V\to\{0,\ldots,k-1\}$. The **standard $k$-opinion voter model** is the process $(\xi_t:t\ge0)$ of opinion assignments $\xi_t:V\to\{0,\dots,k-1\}$ with $\xi_0=\sigma_0$ and the following synchronous update: given $\xi_t$, every vertex $v$ independently chooses a neighbour $w$ of $v$ in $G_t$ uniformly at random and adopts $\xi_t(w)$ with probability $1/2$; otherwise it keeps $\xi_t(v)$. Thus the law of $\xi_{t+1}(v)$ is
--   $$\tfrac12\,\delta_{\xi_t(v)}+\sum_{w\sim_{G_t}v}\frac1{2d(v)}\,\delta_{\xi_t(w)},$$
--   independently over $v$. The process is a time-inhomogeneous Markov chain; its law on paths $\mathbb N\to(V\to\{0,\dots,k-1\})$ is defined here.
--
--   A state $x$ is a **consensus** if all vertices hold the same opinion. The **consensus time** is the first $t$ at which $\xi_t$ is a consensus, so "the consensus time is at most $x$" is the event that some $t\le x$ has $\xi_t$ a consensus.
--
--   **Formalization Note** The path law is built with the Ionescu-Tulcea theorem (`Kernel.traj`) from the step kernels; the step law is the product over $v$ of the vertex laws, written as a fair coin followed by a uniform neighbour. A vertex with no neighbours in $G_t$ keeps its opinion; this branch never occurs since $d(v)\ge1$.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Definition 1.2, p.5

import Mathlib
import Definitions.Def_TemporalVoter_TemporalGraph

open scoped Classical
open MeasureTheory ProbabilityTheory

namespace TemporalVoter

variable {V : Type} [Fintype V]

/-- The law of the new opinion `ξ_{t+1}(v)` of one vertex in the **standard voter model**
(arXiv:2606.13374, version of 2 Nov 2026, Definition 1.2, p.5): with probability `1/2` the vertex
`v` chooses a neighbour `w` of `v` in `G_t` uniformly at random and adopts `ξ_t(w) = x w`;
otherwise it keeps `x v`.

**Formalization Note** The branch for a vertex without neighbours in `G_t` (keep `x v`) never
occurs, since `d(v) ≥ 1` in every snapshot (Definition 1.1); it only makes the law total. -/
noncomputable def vertexLaw (T : TemporalGraph V) {k : ℕ} (t : ℕ) (x : V → Fin k) (v : V) :
    PMF (Fin k) :=
  (PMF.uniformOfFintype Bool).bind fun copy =>
    if copy then
      (if h : ((T.G t).neighborFinset v).Nonempty then (PMF.uniformOfFinset _ h).map x
        else PMF.pure (x v))
    else PMF.pure (x v)

/-- One synchronous step of the voter model from state `x` at time `t`: all vertices update
independently (product of the `vertexLaw`s), using the graph `G_t` (Definition 1.2, p.5). -/
noncomputable def stepLaw (T : TemporalGraph V) {k : ℕ} (t : ℕ) (x : V → Fin k) :
    Measure (V → Fin k) :=
  Measure.pi fun v => (vertexLaw T t x v).toMeasure

instance (T : TemporalGraph V) {k : ℕ} (t : ℕ) (x : V → Fin k) :
    IsProbabilityMeasure (stepLaw T t x) := by
  unfold stepLaw; infer_instance

/-- The step kernel at time `n`: given the history `(ξ_0, …, ξ_n)` it draws `ξ_{n+1}` from
`stepLaw T n ξ_n` (the chain is Markov, time-inhomogeneous, p.5). -/
noncomputable def stepKernel (T : TemporalGraph V) (k : ℕ) (n : ℕ) :
    Kernel (Π _ : Finset.Iic n, V → Fin k) (V → Fin k) :=
  Kernel.ofFunOfCountable fun h => stepLaw T n (h ⟨n, Finset.mem_Iic.2 le_rfl⟩)

instance (T : TemporalGraph V) (k : ℕ) (n : ℕ) : IsMarkovKernel (stepKernel T k n) :=
  ⟨fun h => by
    change IsProbabilityMeasure (stepLaw T n (h ⟨n, Finset.mem_Iic.2 le_rfl⟩))
    infer_instance⟩

/-- **The standard `k`-opinion voter model** (Definition 1.2, p.5) as a path measure: the law of
`(ξ_t : t ≥ 0)` on `ℕ → (V → Fin k)`, started deterministically at `ξ_0 = σ₀` and run with the
step kernels above (Ionescu-Tulcea, `Kernel.traj`). -/
noncomputable def voterLaw (T : TemporalGraph V) (k : ℕ) (σ₀ : V → Fin k) :
    Measure (ℕ → V → Fin k) :=
  Kernel.traj (X := fun _ => V → Fin k) (stepKernel T k) 0 (fun _ => σ₀)

/-- **Consensus** (Definition 1.2, p.5): all vertices hold the same opinion. The consensus time is
the first `t` with `IsConsensus (ξ t)`, so "the consensus time is at most `x`" is the event
`∃ t ≤ x, IsConsensus (ξ t)`. -/
def IsConsensus {k : ℕ} (x : V → Fin k) : Prop :=
  ∀ v w, x v = x w

end TemporalVoter


