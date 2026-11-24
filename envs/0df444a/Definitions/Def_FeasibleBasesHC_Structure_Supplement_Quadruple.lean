-- Prove2me | Definitions.Def_FeasibleBasesHC_Structure_Supplement_Quadruple
-- name    : FeasibleBasesHC_Structure_Supplement_Quadruple
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:27:19.989554+00:00
-- url     : https://prove2.me/theorems/3324b189-4c6a-4f85-be0c-b08e73559079
-- title:
--   §4 — encoded quadruples, their bases, and ultimate feasibility
-- statement:
--   Let $s\in[n]\setminus\{1\}$, let $\pi$ be a permutation without fixed points satisfying $\pi(i)=i+1$ exactly when $i=s-1$, and let $L,U$ partition $[n]\setminus\{1,s\}$. Indices are cyclic modulo $n$. The encoded basis has
--
--   $$
--   A=\{(i,\pi(i)):i\in[n]\}\cup\{(i,\pi(i-1)):i\ne s\},\qquad Y=\{s\}.
--   $$
--
--   The predicate of feasibility means that this basis belongs to $\Gamma(G)$ for some loopless digraph $G$ containing $A$. This is equivalent to using any such $G$: every nonbasic arc has zero flow, so the basic equations and nonnegativity constraints are unchanged by adding arcs. The definition uses the published polytope and basis objects, including independence of all $2n$ basic columns, rather than replacing feasibility by the desired combinatorial conditions.
--
--   **Formalization Note** Paper node $i$ is represented by $i-1:\mathrm{Fin}\ n$, so node $1$ is $0$ and node $n$ is $-1$. The existing `[NeZero n]` convention makes the root available. The displayed basis on p. 15 and the domain of $\eta_i$ resolve that page's inconsistent thin-arc bullet: the thin arcs $(i+1,\pi(i))$ exclude $i=s-1$, not $i=s$.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 15, the displayed basis B and its governing paragraph

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure.Supplement

/-- The data and standing conditions of Section 4, p. 15.
Paper label i corresponds to i-1 in Fin n; all index arithmetic is cyclic. -/
structure Quadruple (n : ℕ) [NeZero n] where
  s : Fin n
  pi : Equiv.Perm (Fin n)
  L : Finset (Fin n)
  U : Finset (Fin n)
  s_ne_root : s ≠ 0
  fixedPointFree : ∀ i, pi i ≠ i
  successor_iff : ∀ i, pi i = i + 1 ↔ i = s - 1
  disjoint : Disjoint L U
  partition : L ∪ U = Finset.univ \ {0, s}

variable {n : ℕ} [NeZero n]

/-- Basic original arcs, using the displayed B on p. 15 rather than the
thin-arc bullet's misprinted exclusion. -/
def Quadruple.arcs (q : Quadruple n) : Finset (Fin n × Fin n) :=
  Finset.univ.image (fun i => (i, q.pi i)) ∪
    (Finset.univ.erase q.s).image (fun i => (i, q.pi (i - 1)))

/-- The paper's encoded (B,L,U), in the base mission's representation. -/
def Quadruple.basis (q : Quadruple n) : Basis n where
  A := q.arcs
  Y := {q.s}
  L := q.L
  U := q.U

/-- Ultimate feasibility in a loopless ambient graph containing the basic arcs.
Nonbasic flows are zero, so adding ambient arcs does not change this property. -/
def Quadruple.Feasible (q : Quadruple n) : Prop :=
  ∃ G : Digraph n, q.arcs ⊆ G.E ∧ q.basis ∈ GamUlt G

end FeasibleBasesHC.Structure.Supplement


