-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Supplement_Directed
-- name    : MeanCertificates1424_Hardness_Supplement_Directed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:55:36.248479+00:00
-- url     : https://prove2.me/theorems/e1104e6b-7fb2-45a5-ae7c-b784ee43084a
-- title:
--   Directed difference constraints with interval reports and directed source alphabets
-- statement:
--   Appendix E replaces the model of §2 by a strongly connected directed graph $D=(V,A)$ with real arc costs $c_{uv}$ (possibly negative) and no negative directed cycle, with directed shortest-path cost $d_D(u,v)$ (possibly negative). The field constraints are $x_v-x_u\le c_{uv}$ for $uv\in A$. Vertex $i$ reports a finite interval $J_i=[\underline y_i,\overline y_i]$, at most $b$ of these intervals may be violated, and trusted finite audit intervals are retained on $Q$. The **robust feasible class** is
--
--   $$
--   C=\{x:\ x_v-x_u\le c_{uv}\ (uv\in A),\ |\{i:x_i\notin J_i\}|\le b,\ x_q\in[\alpha_q,\beta_q]\ (q\in Q)\}.
--   $$
--
--   Every report and audit anchor is a source with a distinct identity and interval $[\alpha_a,\beta_a]$. With $q=b+1$, $A^+_v$ is the set of values $\beta_a+d_D(a,v)$ of the first $q$ sources in increasing order, and $A^-_v$ the set of values $\alpha_a-d_D(v,a)$ of the first $q$ sources in decreasing order, ties broken by a fixed injective order on identities.
--
--   These objects state Theorem E.1.
--
--   **Formalization Note** Walks are vertex lists whose consecutive pairs are arcs; $d_D$ is the infimum of walk costs, which is a minimum under strong connectivity and the absence of negative cycles.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Appendix E (printed p.29, PDF p.31)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

namespace MeanCertificates1424.Hardness.Supplement

/-! # Directed difference constraints with interval reports (Appendix E, printed p.29, PDF p.31)

This model replaces §2: a strongly connected digraph `D = (V, A)` with real arc costs
`c_{uv}` (possibly negative) and no negative directed cycle; constraints `x_v − x_u ≤ c_{uv}`;
each vertex reports a finite interval `J_i = [y̲_i, ȳ_i]`, at most `b` violated; trusted finite
audit intervals on `Q`. -/

structure DirInst where
  n : ℕ
  arc : Fin n → Fin n → Prop
  cost : Fin n → Fin n → ℝ
  budget : ℕ
  repLo : Fin n → ℝ
  repHi : Fin n → ℝ
  audits : Finset (Fin n)
  lo : Fin n → ℝ
  hi : Fin n → ℝ

/-- A directed walk, as its vertex list: consecutive vertices are joined by arcs. -/
def IsDirWalk (D : DirInst) (p : List (Fin D.n)) : Prop :=
  p ≠ [] ∧ ∀ e ∈ p.zip p.tail, D.arc e.1 e.2

/-- Total arc cost of a vertex list. -/
def walkCost (D : DirInst) (p : List (Fin D.n)) : ℝ :=
  ((p.zip p.tail).map fun e => D.cost e.1 e.2).sum

def StronglyConnected (D : DirInst) : Prop :=
  ∀ u v, ∃ p, IsDirWalk D p ∧ p.head? = some u ∧ p.getLast? = some v

/-- Every closed directed walk has nonnegative total cost. -/
def NoNegCycle (D : DirInst) : Prop :=
  ∀ p, IsDirWalk D p → p.head? = p.getLast? → 0 ≤ walkCost D p

/-- `d_D(u, v)`: least cost of a directed walk from `u` to `v` (possibly negative; finite
under strong connectivity and no negative cycle). -/
noncomputable def ddist (D : DirInst) (u v : Fin D.n) : ℝ :=
  sInf {c | ∃ p, IsDirWalk D p ∧ p.head? = some u ∧ p.getLast? = some v ∧ c = walkCost D p}

/-- The robust feasible class `C`. -/
def dirFeasible (D : DirInst) : Set (Fin D.n → ℝ) :=
  {x | (∀ u v, D.arc u v → x v - x u ≤ D.cost u v) ∧
    (Finset.univ.filter fun i => ¬ (D.repLo i ≤ x i ∧ x i ≤ D.repHi i)).card ≤ D.budget ∧
    ∀ q ∈ D.audits, D.lo q ≤ x q ∧ x q ≤ D.hi q}

/-- Sources: one per report interval (`inl i`) and one per audit (`inr q`). -/
def dirSources (D : DirInst) : Finset (Source D.n) :=
  Finset.univ.map Function.Embedding.inl ∪ D.audits.map Function.Embedding.inr

def dirAlpha (D : DirInst) : Source D.n → ℝ
  | Sum.inl i => D.repLo i
  | Sum.inr q => D.lo q

def dirBeta (D : DirInst) : Source D.n → ℝ
  | Sum.inl i => D.repHi i
  | Sum.inr q => D.hi q

/-- `A⁺_v`: values `β_a + d_D(a, v)` of the first `q = b + 1` sources in increasing order,
ties broken by the fixed identity order `ord`. -/
noncomputable def dirUp (D : DirInst) (ord : Source D.n → ℕ) (v : Fin D.n) : Finset ℝ :=
  (topSources (dirSources D) (fun a => dirBeta D a + ddist D (srcLoc a) v) ord
    (D.budget + 1)).image fun a => dirBeta D a + ddist D (srcLoc a) v

/-- `A⁻_v`: values `α_a − d_D(v, a)` of the first `q = b + 1` sources in decreasing order,
ties broken by the fixed identity order `ord`. -/
noncomputable def dirLow (D : DirInst) (ord : Source D.n → ℕ) (v : Fin D.n) : Finset ℝ :=
  (topSources (dirSources D) (fun a => -(dirAlpha D a - ddist D v (srcLoc a))) ord
    (D.budget + 1)).image fun a => dirAlpha D a - ddist D v (srcLoc a)

end MeanCertificates1424.Hardness.Supplement


