-- Prove2me | Definitions.Def_SetDefinedGraphs_Clauses
-- name    : SetDefinedGraphs_Clauses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:24:49.377434+00:00
-- url     : https://prove2.me/theorems/680c3c0e-c066-49ae-adce-f14bfb5253d0
-- title:
--   Clauses, full DNFs and clause digraphs: injective, cyclic, acyclic, discrete, path and $P$-compatible clauses; loop coordinates; $C|_I$
-- statement:
--   Let the variables be $q_{i,j}$, $i,j\in[d]$ (more generally $i,j$ in a coordinate set $\iota$).
--
--   1. A **clause** is a conjunction of literals $q_{i,j}$ or $\overline{q_{i,j}}$; for $I\subseteq[d]$, $C|_I$ removes the literals of the variables with an index outside $I$.
--   2. A clause is **full** if it contains exactly one literal per variable. A full clause $C$ is identified with its **clause digraph** $\Delta_C$ on $[d]$ (possibly with loops): $i\to j$ is an arc iff $q_{i,j}$ occurs positively. $C$ holds on $(u,w)$ iff $Q_{u,w}=\Delta_C$. A **full DNF** is a disjunction (a finite set) of full clauses.
--   3. $C$ is **injective** if every vertex of $\Delta_C$ has at most one in-neighbour and at most one out-neighbour. An injective clause is
--      - **cyclic** if $\Delta_C$ contains a directed cycle on at least $2$ vertices, and **acyclic** otherwise;
--      - **discrete** if every component of $\Delta_C$ is a single vertex;
--      - a **path clause** if every non-trivial component of $\Delta_C$ is a directed path and one exists.
--   4. The **loop coordinates** $L(C)$ of an injective clause are the isolated vertices of $\Delta_C$ carrying a loop.
--   5. For a partition $P$ of $[d]$, $C$ is **$P$-compatible** if in $\Delta_C$ every out-neighbourhood and every in-neighbourhood is empty or a $P$-class. $I$ denotes the set of least elements of the $P$-classes.
--   6. A full DNF is **injective** (resp. **discrete**) if all its clauses are.
--
--   **Formalization Note** Since in an injective clause digraph every component is a directed path or a directed cycle, and a looped vertex has no other arcs (p.16), a path clause is encoded as: injective, not cyclic, and with an arc between two distinct vertices. General (not necessarily full) clauses are pairs of positive and negative literal sets.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §3.3 pp.16–17 (PDF pp.18–19): clauses, full clauses and DNFs, clause digraphs, P-compatible, injective, connected/discrete/path/cyclic/acyclic clauses, loop coordinates, C|I; §4.2 p.26 (I = least elements of the P-classes)

import Mathlib

set_option autoImplicit false

namespace SetDefinedGraphs

/-- A **clause** over the variables `q_{i,j}`, `i, j ∈ ι` (arXiv:2607.23754, §3.3, p.16): a conjunction of literals.
`pos i j = true` means the literal `q_{i,j}` occurs, `neg i j = true` means the literal `q̄_{i,j}` occurs. -/
structure Clause (ι : Type) where
  /-- The variables occurring positively. -/
  pos : ι → ι → Bool
  /-- The variables occurring negatively. -/
  neg : ι → ι → Bool

/-- A clause **holds** on an assignment `Q` of the variables if every literal of it is satisfied. -/
def Clause.Holds {ι : Type} (C : Clause ι) (Q : ι → ι → Bool) : Prop :=
  ∀ i j, (C.pos i j = true → Q i j = true) ∧ (C.neg i j = true → Q i j = false)

/-- The Boolean function represented by a clause. -/
noncomputable def Clause.toFun {ι : Type} (C : Clause ι) : (ι → ι → Bool) → Bool :=
  fun Q => by classical exact decide (C.Holds Q)

/-- `C|_I`: the clause obtained from `C` by removing the literals of the variables `q_{i,j}` with at least one index
outside `I` (arXiv:2607.23754, p.17). It is a clause over the variables `q_{i,j}`, `i, j ∈ I`. -/
def Clause.restrict {ι : Type} (C : Clause ι) (I : Set ι) : Clause I :=
  ⟨fun i j => C.pos i j, fun i j => C.neg i j⟩

/-- A **full clause** over the variables `q_{i,j}`, `i, j ∈ ι` (arXiv:2607.23754, p.16), contains exactly one literal
for each variable; it is identified with its **clause digraph** `Δ_C` (a digraph on `ι`, possibly with loops), which has
an arc `i → j` iff `q_{i,j}` occurs positively. A full clause holds on `Q` iff `Q = Δ_C`. -/
abbrev FullClause (ι : Type) : Type := ι → ι → Bool

/-- The Boolean function represented by a **full DNF**, a finite set `H` of full clauses: it is `1` on `Q` iff some
clause of `H` holds on `Q`, i.e. iff `Q ∈ H`. A full clause `C` is the DNF `{C}`. -/
noncomputable def dnfFun {ι : Type} (H : Finset (FullClause ι)) : (ι → ι → Bool) → Bool :=
  fun Q => by classical exact decide (Q ∈ H)

/-- The restriction `C|_I` of a full clause to the coordinates in `I` (p.17); it is a full clause over `I`. -/
def fullRestrict {ι : Type} (C : FullClause ι) (I : Set ι) : FullClause I :=
  fun i j => C i j

/-- A full clause is **injective** if every vertex of its clause digraph has at most one out-neighbour and at most one
in-neighbour (p.16). -/
def IsInjectiveClause {ι : Type} (C : FullClause ι) : Prop :=
  (∀ i j j', C i j = true → C i j' = true → j = j') ∧ (∀ i i' j, C i j = true → C i' j = true → i = i')

/-- An injective clause is **cyclic** if its clause digraph contains a directed cycle with at least `2` vertices
(p.17): distinct `x₀, …, x_{k−1}`, `k ≥ 2`, with arcs `x_t → x_{t+1 mod k}`. -/
def IsCyclicClause {ι : Type} (C : FullClause ι) : Prop :=
  IsInjectiveClause C ∧
    ∃ k : ℕ, 2 ≤ k ∧ ∃ x : Fin k → ι, Function.Injective x ∧ ∀ t : Fin k, C (x t) (x (finRotate k t)) = true

/-- An injective clause is **acyclic** if it is not cyclic (p.17). -/
def IsAcyclicClause {ι : Type} (C : FullClause ι) : Prop :=
  IsInjectiveClause C ∧ ¬ IsCyclicClause C

/-- An injective clause is **discrete** if every connected component of the underlying graph of its clause digraph is a
single vertex (p.17), i.e. the clause digraph has no arc between two distinct vertices (only the variables `q_{i,i}`
can occur positively, p.28). -/
def IsDiscreteClause {ι : Type} (C : FullClause ι) : Prop :=
  IsInjectiveClause C ∧ ∀ i j, C i j = true → i = j

/-- An injective clause is a **path clause** (p.17) if every non-trivial connected component of its clause digraph is
a directed path and there is at least one non-trivial component.

**Formalization Note** In the clause digraph of an injective clause every connected component is a directed path or a
directed cycle (p.16: "Clearly, in the clause digraph of an injective clause every connected component corresponds to
either a directed path or a directed cycle"); a vertex with a loop has no other arcs, so it is a trivial component.
Hence "every non-trivial component is a directed path, and one exists" is encoded as: injective, no directed cycle on
`≥ 2` vertices, and some arc between two distinct vertices. -/
def IsPathClause {ι : Type} (C : FullClause ι) : Prop :=
  IsInjectiveClause C ∧ ¬ IsCyclicClause C ∧ ∃ i j, i ≠ j ∧ C i j = true

/-- The set `L(C)` of **loop coordinates** of an injective clause (p.17, p.27): the vertices of the clause digraph that
are isolated and carry a loop. For an injective clause a loop at `i` forces `i` to be isolated, so `L(C)` is the set of
`i` with `q_{i,i}` positive. -/
def loopCoords {ι : Type} [Fintype ι] (C : FullClause ι) : Finset ι :=
  Finset.univ.filter (fun i => C i i = true)

/-- For a partition `P` of the coordinates, a full clause is **`P`-compatible** (p.16) if, in its clause digraph, the
out-neighbourhood of every vertex is empty or a `P`-class, and the in-neighbourhood of every vertex is empty or a
`P`-class. -/
def IsPCompatible {ι : Type} (P : Setoid ι) (C : FullClause ι) : Prop :=
  (∀ i, (∀ j, C i j = false) ∨ ∃ k, ∀ j, C i j = true ↔ P.r j k) ∧
    (∀ j, (∀ i, C i j = false) ∨ ∃ k, ∀ i, C i j = true ↔ P.r i k)

/-- The set `I ⊆ [d]` consisting of the least element of every `P`-class (p.26). -/
def leastElems {ι : Type} [LinearOrder ι] (P : Setoid ι) : Set ι :=
  {i | ∀ j, P.r i j → i ≤ j}

/-- A full DNF is **injective** if each of its clauses is injective (p.17). -/
def IsInjectiveDNF {ι : Type} (H : Finset (FullClause ι)) : Prop :=
  ∀ C ∈ H, IsInjectiveClause C

/-- A full DNF is **discrete** if each of its clauses is discrete (p.17). -/
def IsDiscreteDNF {ι : Type} (H : Finset (FullClause ι)) : Prop :=
  ∀ C ∈ H, IsDiscreteClause C

end SetDefinedGraphs


