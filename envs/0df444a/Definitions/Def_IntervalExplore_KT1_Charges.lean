-- Prove2me | Definitions.Def_IntervalExplore_KT1_Charges
-- name    : IntervalExplore_KT1_Charges
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:11.51041+00:00
-- url     : https://prove2.me/theorems/07a4f039-9c0c-40a3-9f6d-19bb89e6724d
-- title:
--   Two-stage updates, vertex and edge charges, and the edge-charge tail
-- statement:
--   Fix an execution of GreedyExp1. After a move, first update the current vertex and known and visited sets and add newly admitted edges without removing old ones. The intermediate graph is the union of the old and fully updated maps. Then remove excluded edges in any fixed order, represented by an injective ranking for that move.
--
--   For a vertex other than the start, $\iota_V(v)$ is the change in potential during stage one of its first arrival; the start has charge zero. In particular, the final first visit changes the potential from one to zero and has charge $-1$. For an edge $e$, $\iota_E(e)$ is the stage-two increase at its first elimination, or zero if it is never eliminated. The tail is
--   $$
--   F'(k)=|\{e\in E:\ \iota_E(e)\ge k\}|.
--   $$
--   The total charges sum over all underlying vertices and edges. Charges are computed from the run, without a supplied stopping time, charge array or bound. A never-visited vertex receives zero as an extension of the definition to arbitrary executions.
--
--   **Formalization Note** Potentials use extended naturals, vertex differences use integers, and edge differences use naturals. Under the milestones' common-tree assumption all relevant distances are finite, deletion is monotone, and the conversions give their literal finite values. Every per-move elimination order remains a free parameter.
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), two-stage update and charges, p.7 (PDF p.8); definition of F′, p.8 (PDF p.9)

import Definitions.Def_IntervalExplore_KT1_GreedyMap

set_option autoImplicit false

namespace IntervalExplore.KT1

/-! Two-stage analysis, printed pp.7–8 (PDF pp.8–9).
Charges are computed from the execution, without assuming termination or a charge bound. -/

/-- An arbitrary order for each time's eliminations; injectivity forbids ties. -/
abbrev EliminationOrder (V : Type) := ℕ → (Sym2 V ↪ ℕ)

noncomputable def stageOneGraph {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) :
    SimpleGraph V := worldMapGraph W A t ⊔ worldMapGraph W A (t + 1)

noncomputable def stageOnePotential {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) : ℕ∞ :=
  potential (stageOneGraph W A t) (state W A (t + 1)).position (worldTargets W A (t + 1))

noncomputable def deleted {V : Type} [Fintype V] (W : World V) (A : Alg) (t : ℕ) :
    Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ W.graph.edgeSet ∧ MovesAt W A t ∧
    e ∈ (worldMapGraph W A t).edgeSet ∧ e ∉ (worldMapGraph W A (t + 1)).edgeSet

noncomputable def beforeDeletion {V : Type} [Fintype V] (W : World V) (A : Alg)
    (order : EliminationOrder V) (t : ℕ) (e : Sym2 V) : SimpleGraph V := by
  classical
  let removed := (deleted W A t).filter fun f => order t f < order t e
  exact SimpleGraph.fromEdgeSet ((stageOneGraph W A t).edgeSet \ (removed : Set (Sym2 V)))

noncomputable def afterDeletion {V : Type} [Fintype V] (W : World V) (A : Alg)
    (order : EliminationOrder V) (t : ℕ) (e : Sym2 V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ((beforeDeletion W A order t e).edgeSet \ {e})

/-- The start has charge zero. For each other vertex take its first actual arrival.
The last new vertex has charge 0-1=-1. Unvisited vertices have zero provisional charge. -/
noncomputable def iotaV {V : Type} [Fintype V] (W : World V) (A : Alg) (v : V) : ℤ := by
  classical
  exact if v = W.start then 0 else
    if hv : ∃ t, MovesAt W A t ∧ (state W A (t + 1)).position = v then
      let t := Nat.find hv
      (stageOnePotential W A t).toNat - ((worldDcur W A t).toNat : ℤ)
    else 0

/-- The increase at the first elimination of e, or zero if never eliminated.
Under CommonTree every potential used here is finite and deletion cannot decrease it;
thus toNat and natural subtraction give the literal finite increase. -/
noncomputable def iotaE {V : Type} [Fintype V] (W : World V) (A : Alg)
    (order : EliminationOrder V) (e : Sym2 V) : ℕ := by
  classical
  exact if he : ∃ t, e ∈ deleted W A t then
    let t := Nat.find he
    let v := (state W A (t + 1)).position
    let U := worldTargets W A (t + 1)
    (potential (afterDeletion W A order t e) v U).toNat -
      (potential (beforeDeletion W A order t e) v U).toNat
  else 0

noncomputable def totalVertexCharge {V : Type} [Fintype V] (W : World V) (A : Alg) : ℤ :=
  ∑ v : V, iotaV W A v

noncomputable def totalEdgeCharge {V : Type} [Fintype V] (W : World V) (A : Alg)
    (order : EliminationOrder V) : ℕ := by
  classical
  exact ∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ W.graph.edgeSet), iotaE W A order e

noncomputable def Fprime {V : Type} [Fintype V] (W : World V) (A : Alg)
    (order : EliminationOrder V) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun e : Sym2 V => e ∈ W.graph.edgeSet ∧ k ≤ iotaE W A order e).card

end IntervalExplore.KT1


