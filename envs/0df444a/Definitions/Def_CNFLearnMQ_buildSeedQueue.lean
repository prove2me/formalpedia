-- Prove2me | Definitions.Def_CNFLearnMQ_buildSeedQueue
-- name    : CNFLearnMQ_buildSeedQueue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:31.913665+00:00
-- url     : https://prove2.me/theorems/57629cab-6501-43c1-a1d7-a0adf9dc9110
-- title:
--   Core dependency graph $G_{\mathcal R}$, seeds, and BuildSeedQueue (Algorithm 2)
-- statement:
--   For a family $\mathcal R$ of variable sets, the **core dependency graph** $G_{\mathcal R}$ is the graph on $V$ in which two distinct variables are adjacent iff they occur together in some member of $\mathcal R$. A set $S$ is a **connected vertex set** if the subgraph induced on $S$ is connected. A **seed** of size $s$ is a signed subclause $(S,\sigma_S)$ with $S$ a connected vertex set of size $s$ and any signing $\sigma_S\in\{\mathrm{True},\mathrm{False}\}^S$.
--
--   BuildSeedQueue$(\mathcal R,t)$ builds $G_{\mathcal R}$, enumerates each connected vertex set of size $\lceil k/(t+1)\rceil$ once, and enqueues all its signings.
--
--   Charges: $n+\sum_{R\in\mathcal R}|R|^2$ for building the graph; $n(\Delta+1)^s(s+1)$ for enumerating the connected sets of size $s$, where $\Delta$ is the maximum degree; $s+1$ per enqueued seed.
--
--   **Formalization Note** Seeds are clauses whose support is exactly $S$. The enumeration order is fixed (sublists of the sorted variables).
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Definition 5.4, p.21; §5.1 p.22; Algorithm 2, p.23

import Mathlib
import Definitions.Def_CNFLearnMQ_OProg
import Definitions.Def_CNFLearnMQ_Ntot

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant OProg

variable {n : ℕ}

/-- The core dependency graph `G_R` of a family `R` of variable sets (Feng, Yu, Zhang, STOC 2027
submission (manuscript sha256 519ee6d4…), Definition 5.4, p.21): two distinct variables are adjacent
iff they occur together in some member of `R`. -/
def coreGraph (Rs : Finset (Finset (Fin n))) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ R ∈ Rs, u ∈ R ∧ v ∈ R
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim fun R hR => ⟨R, hR.1, hR.2.2, hR.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `S` is a connected vertex set of `G`: the subgraph of `G` induced on `S` is connected (in
particular `S` is nonempty). -/
def IsConnectedSet (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  (G.induce (S : Set (Fin n))).Connected

/-- The seeds of `G` of size `s` (§5.1, p.22): the signed subclauses `(S, σ_S)` on a connected vertex
set `S` of `G` with `|S| = s`, for every signing `σ_S ∈ {True, False}^S`, encoded as the clauses with
support exactly `S`. -/
noncomputable def seeds (G : SimpleGraph (Fin n)) (s : ℕ) : Finset (Clause n) := by
  classical
  exact Finset.univ.filter fun c => width c = s ∧ IsConnectedSet G (support c)

/-- All signings of the variable set `S`, in a fixed order: the clause with support `S` whose stored
literal value on `v ∈ S` is `true` exactly for the variables of a sublist `L` of `S` sorted
increasingly. Each signing occurs exactly once. -/
def signings (S : Finset (Fin n)) : List (Clause n) :=
  ((S.sort (· ≤ ·)).sublists).map fun L v => if v ∈ S then some (decide (v ∈ L)) else none

/-- BuildSeedQueue(R, t) (Algorithm 2, p.23) with the parameter `k`: construct `G_R`, enumerate every
connected vertex set of `G_R` of size `⌈k/(t + 1)⌉` once (in the order of `sublistsLen` of the
variables), and enqueue all its signings.

Charges: `n + Σ_{R∈R} |R|²` for building `G_R` (line 1); `n·(Δ + 1)^s·(s + 1)` for enumerating the
connected sets of size `s = ⌈k/(t + 1)⌉`, where `Δ` is the maximum degree of `G_R` (each such set
is grown from one of `n` start vertices by repeatedly adding one of at most `Δ + 1` candidates,
writing `s + 1` words each time); `s + 1` per enqueued seed (line 5).

**Formalization Note** The pure Lean enumeration (filtering all `s`-subsets) is free; the charge is
the cost of the neighbour-growing enumeration of the paper's accounting (proof of Theorem 5.1,
p.36: "Constructing the core graph and enumerating seeds costs `O_{k,d,t}(nN_seed)`"). -/
noncomputable def buildSeedQueue (k : ℕ) (t : ℝ) (Rs : Finset (Finset (Fin n))) :
    OProg n (List (Clause n)) := by
  classical
  exact do
    let G := coreGraph Rs
    charge (n + ∑ R ∈ Rs, R.card ^ 2)
    let s := seedSize k t
    charge (n * (G.maxDegree + 1) ^ s * (s + 1))
    let sets := ((List.finRange n).sublistsLen s).filter fun L => decide (IsConnectedSet G L.toFinset)
    let Q := sets.flatMap fun L => signings L.toFinset
    charge (Q.length * (s + 1))
    return Q

end CNFLearnMQ


