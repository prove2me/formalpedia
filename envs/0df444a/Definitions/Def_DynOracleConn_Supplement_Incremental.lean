-- Prove2me | Definitions.Def_DynOracleConn_Supplement_Incremental
-- name    : DynOracleConn_Supplement_Incremental
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:45:17.132201+00:00
-- url     : https://prove2.me/theorems/fa22efa0-712b-4518-b40a-22a34fb772b9
-- title:
--   Insertion-only sequences, list oracles in an arbitrary order, worst-case and total probe budgets
-- statement:
--   This definition adds to the published model of dynamic $s$–$t$ connectivity the notions used by the incremental lower bounds.
--
--   1. An update sequence $\sigma$ is **incremental** if it is valid (every update has two distinct endpoints, insertions add absent edges, the graph starts empty) and every update is an insertion.
--   2. For keys $\rho_v$, one permutation of $[n]$ per vertex $v$, the **list oracle ordered by $\rho$** lists the neighbors of $v$ as $w_1,\dots,w_{d(v)}$ in increasing order of $\rho_v$. The query $\mathrm{Degree}(v)$ returns $d(v)$ and $\mathrm{Neighbor}(v,j)$ returns $w_j$. Every ordering of a finite neighbor set is increasing for some key, so these oracles realize every adjacency-list ordering.
--   3. A randomized algorithm has **worst-case probe bound $T$** on a class of sequences if, on every outcome of its randomness and every sequence of the class, every update makes at most $T$ oracle probes. It has **total probe budget $q$** on a class if every such execution makes at most $q$ probes in total.
--
--   The paper's adjacency lists are in an arbitrary, adversarial order (§1.1, §5.1), and its lower bounds assume that the time bounds hold on every execution (§1.2).
--
--   **Formalization Note** $\mathrm{Neighbor}(v,j)$ is 1-based and returns the code $w_j+1$ of the 0-based vertex $w_j$, or $0$ when $j\notin[d(v)]$, exactly as the published increasing-order list oracle, which is the case $\rho_v=\mathrm{id}$.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4; §1.2, p.6; §5.1, p.30; §6, p.33

import Mathlib
import Definitions.Def_DynOracleConn_Oracles
import Definitions.Def_DynOracleConn_RandAlg

namespace DynOracleConn

/-!
# Insertion-only sequences, list oracles in an arbitrary order, and worst-case and total probe bounds

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4 ("In the
incremental setting all updates are insertions"; "Neighbor(v, j) returns the jth neighbor of v in an
arbitrary ordering"; "A time bound T is worst-case if every update costs at most T"), p.6 ("Our lower
bounds assume that the time bounds hold on every execution"), §5.1, p.30 ("the order of adjacency
lists is arbitrary (i.e., adversarial)") and §6, p.33 ("total probe budget q_total").

**Formalization Note.**
1. `IsIncremental σ`: `σ` is a valid update sequence from the empty graph (published
   `PunctSketch.IsValidStream`) and every update is an insertion.
2. `listOracleBy ρ G` is the adjacency-list oracle in which the neighbors of `v` are listed in
   increasing order of the key `ρ v : Equiv.Perm (Fin n)`. Every enumeration of a finite set of
   neighbors is increasing for some key, so these oracles realize every ordering; the published
   `listOracle` is the case `ρ = fun _ => 1`. Replies are coded exactly as in `listOracle`:
   `Degree(v)` is `d(v)`, `Neighbor(v, j)` is `w_j.val + 1` for `1 ≤ j ≤ d(v)` and `0` otherwise.
3. `WorstCaseOn A O C T`: on every outcome of the randomness and every sequence of the class `C`,
   every update makes at most `T` oracle probes. `TotalBudgetOn A O C q`: on every outcome and every
   sequence of the class `C`, the total number of probes is at most `q`.
-/

namespace Supplement

/-- An insertion-only (incremental) update sequence: a valid sequence from the empty graph all of whose
updates are insertions. -/
def IsIncremental {n : ℕ} (σ : List (PunctSketch.Update n)) : Prop :=
  PunctSketch.IsValidStream σ ∧ ∀ e ∈ σ, e.insert = true

open Classical in
/-- The neighbors of `v` in `G`, listed in increasing order of the key `ρ v`. -/
noncomputable def nbrListBy {n : ℕ} (ρ : Fin n → Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n))
    (v : Fin n) : List (Fin n) :=
  ((((Finset.univ.filter (fun w => G.Adj v w)).image (ρ v)).sort (· ≤ ·))).map (ρ v).symm

/-- The adjacency-list oracle of `G` whose lists are ordered by the keys `ρ`: `Degree(v)` returns
`d(v)`; `Neighbor(v, j)` returns `w_j.val + 1` for the `j`-th neighbor `w_j` of `v` in increasing order
of `ρ v` (`1 ≤ j ≤ d(v)`), and `0` otherwise. -/
noncomputable def listOracleBy {n : ℕ} (ρ : Fin n → Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    ListQuery n → ℕ
  | .degree v => (nbrListBy ρ G v).length
  | .neighbor v j =>
      if j = 0 then 0 else (((nbrListBy ρ G v)[j - 1]?).map (fun w => w.val + 1)).getD 0

variable {n : ℕ} {Q Ans S : Type}

/-- Worst-case probe bound `T` on the sequences of the class `C`: on every outcome `ω` and every
`σ ∈ C`, every update of the run makes at most `T` probes. -/
def WorstCaseOn (A : RandAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans)
    (C : List (PunctSketch.Update n) → Prop) (T : ℝ) : Prop :=
  ∀ (ω : A.Ω) (σ : List (PunctSketch.Update n)), C σ →
    ∀ p ∈ (A.alg ω).transcript O σ, (p.1.length : ℝ) ≤ T

/-- Total probe budget `q` on the sequences of the class `C`: on every outcome `ω` and every `σ ∈ C`,
the run makes at most `q` probes in total. -/
def TotalBudgetOn (A : RandAlg n Q Ans S) (O : SimpleGraph (Fin n) → Q → Ans)
    (C : List (PunctSketch.Update n) → Prop) (q : ℝ) : Prop :=
  ∀ (ω : A.Ω) (σ : List (PunctSketch.Update n)), C σ → ((A.alg ω).totalCost O σ : ℝ) ≤ q

end Supplement

end DynOracleConn


