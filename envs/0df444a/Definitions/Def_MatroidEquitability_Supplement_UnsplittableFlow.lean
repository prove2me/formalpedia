-- Prove2me | Definitions.Def_MatroidEquitability_Supplement_UnsplittableFlow
-- name    : MatroidEquitability_Supplement_UnsplittableFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:24:53.690196+00:00
-- url     : https://prove2.me/theorems/e283b418-a0ed-4336-afbb-96541714444b
-- title:
--   Single-source networks, flows satisfying the demands, and unsplittable flows
-- statement:
--   Let $D=(V,A)$ be a directed graph with a source $s\in V$, sink terminals $t_1,\dots,t_n\in V$ and demands $d\in\mathbb R^n$. For $v\in V$ let $\delta^-(v)$ and $\delta^+(v)$ be the sets of arcs entering and leaving $v$, and write $x(F)=\sum_{a\in F}x_a$.
--
--   1. $D$ is **acyclic** if no vertex lies on a nonempty closed directed walk.
--   2. A flow $x\in\mathbb R^A_{\ge0}$ **satisfies the demands** if
--   $$x(\delta^-(t_j))=d_j\ \text{ for every } j\in[n],\qquad x(\delta^-(v))=x(\delta^+(v))\ \text{ for every } v\in V\setminus\{s,t_1,\dots,t_n\}.$$
--   3. A flow $y$ is **unsplittable** if for each $j\in[n]$ there is a single directed path $P_j$ from $s$ to $t_j$ carrying $d_j$, so that
--   $$y_a=\sum_{j\,:\,a\in P_j}d_j\qquad\text{for every } a\in A .$$
--   Paths of different terminals may share arcs and may coincide.
--
--   This is the setting of the Morell–Skutella conjecture (Conjecture 5): every flow satisfying the demands should have an unsplittable flow $y$ with $|x_a-y_a|\le\max_j d_j$ on every arc. The conjecture itself is not posed; it is the object of the counterexample of Theorem 18.
--
--   **Formalization Note** Arcs are a type with tail and head maps (parallel arcs allowed), and terminals are indexed by a finite type, which is $[n]$ up to relabelling. A walk is a list of arcs, each arc's head being the next arc's tail; a path is a walk whose vertices are pairwise distinct. Acyclicity and positivity of the demands are not bundled into the network.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), §1.3 "Single-source unsplittable flows" and Conjecture 5, p.6 (PDF p.8)

import Mathlib

namespace MatroidEquitability

namespace Supplement

/-- The single-source flow setting of Conjecture 5 (Morell–Skutella), §1.3 "Single-source unsplittable
flows", printed p.6 = PDF p.8 of Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and
Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…): a digraph
`D = (V, A)` (arcs with a tail and a head, parallel arcs allowed), a source `s ∈ V`, sink terminals
`t_j ∈ V` and demands `d_j`, indexed by a finite type `ι`.

**Formalization Note.** The paper indexes the terminals by `[n]`; here they are indexed by an
arbitrary finite type `ι`, which is `[n]` up to relabelling. Acyclicity and positivity of the
demands (`d ∈ ℝ^n_{>0}`) are not bundled: they are separate predicates (`IsAcyclic`) and hypotheses. -/
structure SSNetwork (V A ι : Type) where
  /-- tail of an arc -/
  tail : A → V
  /-- head of an arc -/
  head : A → V
  /-- the source `s` -/
  source : V
  /-- the terminal `t_j` -/
  terminal : ι → V
  /-- the demand `d_j` -/
  demand : ι → ℝ

namespace SSNetwork

variable {V A ι : Type} (N : SSNetwork V A ι)

/-- `p` (a list of arcs) is a directed walk from `u` to `v`: the first arc leaves `u`, each arc's head
is the next arc's tail, and the last arc enters `v`; the empty list is the walk from `u` to `u`. -/
def IsWalk (N : SSNetwork V A ι) : V → V → List A → Prop
  | u, v, [] => u = v
  | u, v, a :: p => N.tail a = u ∧ IsWalk N (N.head a) v p

/-- `p` is a directed path from `u` to `v`: a walk whose vertices `u, head a₁, head a₂, …` are
pairwise distinct. -/
def IsPath (u v : V) (p : List A) : Prop :=
  N.IsWalk u v p ∧ (u :: p.map N.head).Nodup

/-- `D` is acyclic: no vertex has a nonempty closed walk. -/
def IsAcyclic : Prop :=
  ∀ (v : V) (p : List A), N.IsWalk v v p → p = []

/-- `x(δ⁻(v))`, the flow on the arcs entering `v`. -/
noncomputable def inflow [Fintype A] (x : A → ℝ) (v : V) : ℝ :=
  by classical exact ∑ a ∈ Finset.univ.filter (fun a => N.head a = v), x a

/-- `x(δ⁺(v))`, the flow on the arcs leaving `v`. -/
noncomputable def outflow [Fintype A] (x : A → ℝ) (v : V) : ℝ :=
  by classical exact ∑ a ∈ Finset.univ.filter (fun a => N.tail a = v), x a

/-- A flow `x ∈ ℝ^A_{≥0}` satisfies the demands (p.6): `x(δ⁻(t_j)) = d_j` for every terminal `j`, and
`x(δ⁻(v)) = x(δ⁺(v))` for every `v ∈ V \ {s, t_1, …, t_n}`. -/
def SatisfiesDemands [Fintype A] (x : A → ℝ) : Prop :=
  (∀ a, 0 ≤ x a) ∧ (∀ j, N.inflow x (N.terminal j) = N.demand j) ∧
    ∀ v, v ≠ N.source → (∀ j, v ≠ N.terminal j) → N.inflow x v = N.outflow x v

/-- A flow `y` is unsplittable (p.6): for each terminal `j` there is a single path `P_j` from `s` to
`t_j` carrying `d_j`, so that `y_a = Σ_{j : a ∈ P_j} d_j` for every arc `a`. Paths of different
terminals may share arcs and may coincide. -/
def IsUnsplittable [Fintype ι] (y : A → ℝ) : Prop :=
  ∃ P : ι → List A, (∀ j, N.IsPath N.source (N.terminal j) (P j)) ∧
    ∀ a, y a = ∑ j, (by classical exact if a ∈ P j then N.demand j else 0)

end SSNetwork

end Supplement

end MatroidEquitability


