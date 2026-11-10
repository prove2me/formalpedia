-- Prove2me | Definitions.Def_NetworkSumSecure_Solvability_algorithm
-- name    : NetworkSumSecure_Solvability_algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:04:19.198402+00:00
-- url     : https://prove2.me/theorems/608ba6da-2180-45ac-90c8-4b7667801200
-- title:
--   Algorithm 1: path input, initialization, legal selections and finite traces
-- statement:
--   Fix $n$ edge-disjoint paths $Q_j$ from users to the server. Let $Q_i$ denote those starting at user $i$, let $I_Q$ be the users with $Q_i\ne\varnothing$, and assign $z_i=\max(|Q_i|-1,0)$. Every omitted user has a specified auxiliary path $P_i$ to the server, allowed to overlap any other path.
--
--   Initialization labels the $Q_j$ paths bijectively by the coordinates of their own active users. Its columns on the first $Q$ edges are the corresponding standard-basis columns; an omitted user's first auxiliary edge has its message coordinate one and all other coordinates zero. Other edges start at zero. A state records all columns and the last processed edge on each $Q_j$.
--
--   The relay traversal processes the used nonsource edges in topological order. At each edge $e$, a legal column lies in the span of incoming columns, avoids the subspace whose active projection lies in the span of the other $Q$ frontier columns whenever $e$ lies on $Q$, and has a nonzero user block for each omitted user's auxiliary path containing $e$. These are exactly the exclusions in lines 12, 14 and 16. Updating replaces the column of $e$ and advances its $Q$ frontier, if present.
--
--   A legal prefix has its actual initial state and records every selection and update through a specified number of iterations bounded by the finite traversal length. No rank invariant or output claim is part of this relation. The separate output predicate, for $n=r+1$, requires
--
--   $$h_{e_i}^{(i)}\ne0\quad(i\notin I_Q),\qquad\operatorname{rank}(H_{Q_\rho}^{I_Q})=r+1,$$
--
--   as well as zero columns on unused original edges and a causal local code with exactly these global columns that is rank-valid. Keeping the output separate lets the theorem assert existence, absence of stuck prefixes, and correctness for all completed legal choices.
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), pp. 19–24 (PDF pp. 21–26), equations (39)–(53), Algorithm 1 (p. 22 / PDF p. 24)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_algebra

open scoped BigOperators

namespace NetworkSumSecure.Solvability

/-! Equations (39)–(44), Algorithm 1, and verification (45)–(53),
printed pp.19–24 (PDF 21–26). Choices are specified by finite legal traces;
neither rank invariants nor final conclusions are fields of these traces. -/

variable {V E U F : Type}

noncomputable def pathCount {N : Network V E U} {n : ℕ}
    (Q : Fin n → UserPath N) (i : U) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => (Q j).start = i)).card

noncomputable def pathKeys {N : Network V E U} {n : ℕ} (Q : Fin n → UserPath N) (i : U) : ℕ :=
  pathCount Q i - 1

/-- Input paths; the auxiliary paths for omitted users may overlap all other paths. -/
structure PathData (N : Network V E U) (n : ℕ) where
  Q : Fin n → UserPath N
  disjoint : EdgeDisjoint Q
  auxiliary : (i : {i : U // pathCount Q i = 0}) → UserPath N
  auxiliary_start : ∀ i, (auxiliary i).start = i.val

def active {N : Network V E U} {n : ℕ} (D : PathData N n) (i : U) : Prop :=
  0 < pathCount D.Q i

def usedEdge {N : Network V E U} {n : ℕ} (D : PathData N n) (e : E) : Prop :=
  (∃ j, e ∈ (D.Q j).edges) ∨ ∃ i, e ∈ (D.auxiliary i).edges

/-- Enumerating the identity columns in lines 1–6. This is only a bijection
between Q paths and coordinates of their own active users, not a rank certificate. -/
structure Initialization {N : Network V E U} {n : ℕ} (D : PathData N n) where
  label : Fin n → Coord (pathKeys D.Q)
  own_user : ∀ j, (label j).1 = (D.Q j).start
  injective : Function.Injective label
  covers : ∀ c : Coord (pathKeys D.Q), active D c.1 → ∃ j, label j = c

/-- The moving frontier stores one last processed edge on each Q path. -/
structure AlgorithmState {N : Network V E U} {n : ℕ} (D : PathData N n) (F : Type) where
  columns : E → Coord (pathKeys D.Q) → F
  frontier : Fin n → E

noncomputable def initialState [Field F] [Fintype U]
    {N : Network V E U} {n : ℕ} {D : PathData N n} (I : Initialization D) :
    AlgorithmState D F := by
  classical
  exact {
    columns := fun e c =>
      (∑ j : Fin n, if (D.Q j).first = e ∧ I.label j = c then 1 else 0) +
      ∑ i : {i : U // pathCount D.Q i = 0},
        if (D.auxiliary i).first = e ∧ c = ⟨i.val, none⟩ then 1 else 0
    frontier := fun j => (D.Q j).first }

/-- Source outgoing columns are initialized before this finite relay traversal.
Unused edges stay zero, exactly as in the original network before path pruning. -/
noncomputable def relayTraversal [Fintype E] {N : Network V E U} {n : ℕ}
    (D : PathData N n) (O : EdgeOrder N) : List E := by
  classical
  exact (List.ofFn O.edge).filter (fun e =>
    usedEdge D e ∧ ¬ ∃ i, N.graph.tail e = N.user i)

abbrev ActiveCoord {N : Network V E U} {n : ℕ} (D : PathData N n) :=
  {c : Coord (pathKeys D.Q) // active D c.1}

def activeProjection {N : Network V E U} {n : ℕ} (D : PathData N n)
    (v : Coord (pathKeys D.Q) → F) : ActiveCoord D → F := fun c => v c.val

/-- The forbidden B_Q subspace (44), expressed by its active projection.
For the path j containing the current edge, remove its old frontier column. -/
def frontierSpan [Field F] {N : Network V E U} {n : ℕ} {D : PathData N n}
    (s : AlgorithmState D F) (j : Fin n) : Submodule F (ActiveCoord D → F) :=
  Submodule.span F (Set.range (fun k : {k : Fin n // k ≠ j} =>
    activeProjection D (s.columns (s.frontier k.val))))

/-- Lines 12,14,16 combined: incoming span, avoiding B_Q when on Q,
and avoiding every zero-user-block subspace for auxiliary paths containing e. -/
def LegalSelection [Field F] [Fintype E] {N : Network V E U} {n : ℕ}
    {D : PathData N n} (s : AlgorithmState D F) (e : E)
    (v : Coord (pathKeys D.Q) → F) : Prop :=
  v ∈ columnSpan s.columns (incoming N (N.graph.tail e)) ∧
  (∀ j, e ∈ (D.Q j).edges → activeProjection D v ∉ frontierSpan s j) ∧
  ∀ i : {i : U // pathCount D.Q i = 0}, e ∈ (D.auxiliary i).edges →
    (fun c : Option (Fin (pathKeys D.Q i.val)) => v ⟨i.val, c⟩) ≠ 0

noncomputable def advance [Field F] {N : Network V E U} {n : ℕ}
    {D : PathData N n} (s : AlgorithmState D F) (e : E)
    (v : Coord (pathKeys D.Q) → F) : AlgorithmState D F := by
  classical
  exact {
    columns := Function.update s.columns e v
    frontier := fun j => if e ∈ (D.Q j).edges then e else s.frontier j }

/-- A legal prefix records every state and every selected vector. The bound and
finite list ensure that a complete trace has exactly the prescribed iterations. -/
def LegalPrefix [Field F] [Fintype E] [Fintype U] {N : Network V E U} {n : ℕ}
    {D : PathData N n} (O : EdgeOrder N) (I : Initialization D)
    (t : ℕ) (trace : ℕ → AlgorithmState D F) : Prop :=
  t ≤ (relayTraversal D O).length ∧ trace 0 = initialState I ∧
  ∀ j : Fin (relayTraversal D O).length, j.val < t →
    ∃ v, LegalSelection (trace j.val) ((relayTraversal D O).get j) v ∧
      trace (j.val + 1) = advance (trace j.val) ((relayTraversal D O).get j) v

/-- Exact output clauses (43), the rank-valid consequence (24), and a causal
local realization on the full original network, including unused zero edges. -/
def AlgorithmOutput [Field F] [Fintype E] [Fintype U] {N : Network V E U} {r : ℕ}
    (D : PathData N (r + 1)) (s : AlgorithmState D F) : Prop :=
  (∀ e, ¬ usedEdge D e → s.columns e = 0) ∧
  (∀ i : {i : U // pathCount D.Q i = 0},
    (fun c : Option (Fin (pathKeys D.Q i.val)) =>
      s.columns (D.auxiliary i).last ⟨i.val, c⟩) ≠ 0) ∧
  Module.finrank F (Submodule.span F (Set.range (fun j : Fin (r + 1) =>
    activeProjection D (s.columns (D.Q j).last)))) = r + 1 ∧
  ∃ C : LocalCode N F (pathKeys D.Q),
    (∀ e, globalColumn C e = s.columns e) ∧ RankValid C r

end NetworkSumSecure.Solvability


