-- Prove2me | Definitions.Def_GirthBethe_Sharp_BethePermanent
-- name    : GirthBethe_Sharp_BethePermanent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:15:58.480258+00:00
-- url     : https://prove2.me/theorems/1e391f7a-66c7-446e-8302-f5aa24ebd2cd
-- title:
--   §1, (1.1), Theorem 1.3 — support graph, Bethe permanent, 0–1 matrices and disjoint unions of cycles
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ have nonnegative entries. Its support graph $G_A=(L\sqcup R,E)$ has $L$ and $R$ two disjoint copies of $[n]$ (rows and columns) and an edge $ij$ iff $A_{ij}\ne0$; write $A_e=A_{ij}$ for $e=ij$.
--
--   1. (1.1) The Bethe permanent: $\mathrm{Bethe}(A)=0$ if $\mathrm{PM}(G_A)=\emptyset$; otherwise
--   $$\mathrm{Bethe}(A)=\max_{p\in\mathrm{PM}(G_A)}\ \prod_{e\in E(G_A)}\Big(\frac{A_e}{p_e}\Big)^{p_e}(1-p_e)^{1-p_e},$$
--   with boundary terms defined by continuity (a factor equals $1$ at $p_e=0$ and $A_e$ at $p_e=1$).
--   2. $A$ is a 0–1 matrix if every entry is $0$ or $1$.
--   3. A finite graph is a disjoint union of cycles of length $g$ if every vertex has exactly two neighbours and every connected component has exactly $g$ vertices (so each component is a $g$-cycle and every vertex lies on one).
--
--   These are the objects of the paper's main theorem.
--
--   **Formalization Note** Rows and columns are indexed by $\mathrm{Fin}\,n$. The maximum is written as a supremum of the objective over $\mathrm{PM}(G_A)$; that the supremum is attained is the separate item `bethe_max_attained`. Real powers satisfy $x^0=1$ for every $x$, which reproduces the continuity values at $p_e\in\{0,1\}$ for $A_e>0$.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 2, §1 (p. 1, support graph), §1.2 equation (1.1) (p. 2), Theorem 1.3 and Example 1.2 (p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_BipartiteGraph

open Finset

namespace GirthBethe.Sharp

/-! The support graph and the Bethe permanent of a real `n × n` matrix (§1, §1.2 equation (1.1),
§1.3 of Jain–Dong, STOC 2027 submission #705). Rows form the left class `L = Fin n`, columns
the right class `R = Fin n`. -/

/-- The edge set of the support graph `G_A`: `(i, j)` is an edge iff `A i j ≠ 0`. -/
noncomputable def supportEdges {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n × Fin n) :=
  by classical exact univ.filter fun ij => A ij.1 ij.2 ≠ 0

/-- The support graph `G_A` on `L ⊕ R`, `L = R = Fin n`. -/
noncomputable def supportGraph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    SimpleGraph (Fin n ⊕ Fin n) :=
  toGraph (supportEdges A)

/-- The Bethe objective `∏_{e ∈ E(G_A)} (A_e / p_e)^{p_e} (1 - p_e)^{1 - p_e}` of (1.1), with real
powers. On `PM(G_A)` every `p_e ∈ [0, 1]` and `A_e > 0`; the factor equals `1` at `p_e = 0` and
`A_e` at `p_e = 1` (Lean's `x ^ (0:ℝ) = 1`), which are the boundary values by continuity. -/
noncomputable def betheObjective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (p : Edge (supportEdges A) → ℝ) : ℝ :=
  ∏ e : Edge (supportEdges A),
    (A e.1.1 e.1.2 / p e) ^ (p e) * (1 - p e) ^ (1 - p e)

open scoped Classical in
/-- The Bethe permanent (1.1): `Bethe(A) = 0` if `PM(G_A) = ∅`; otherwise the maximum of the
Bethe objective over `PM(G_A)`, written as a supremum (the maximum is attained; see the item
`GirthBethe.Sharp.bethe_max_attained`). -/
noncomputable def bethe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  if (fracPM (supportEdges A)).Nonempty then
    sSup (betheObjective A '' fracPM (supportEdges A))
  else 0

/-- `A` is a 0–1 matrix. -/
def IsZeroOne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- A finite simple graph is a disjoint union of cycles of length `g` (covering all vertices):
every vertex has exactly two neighbours (so every connected component is a cycle) and every
connected component has exactly `g` vertices. -/
def IsDisjointUnionOfCycles {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  (∀ v, (G.neighborSet v).ncard = 2) ∧ ∀ v, (G.connectedComponentMk v).supp.ncard = g

end GirthBethe.Sharp


