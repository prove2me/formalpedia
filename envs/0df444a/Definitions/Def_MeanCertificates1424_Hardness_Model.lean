-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Model
-- name    : MeanCertificates1424_Hardness_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:25.493923+00:00
-- url     : https://prove2.me/theorems/d81e6acb-0dff-4061-a4ff-eb470acc3cc2
-- title:
--   Graph fields, common mismatches, uniform mean certificates and densest subgraphs
-- statement:
--   Let $G$ be a finite connected simple graph on $n\ge1$ vertices. The numerical input consists of a positive rational Lipschitz bound $L$, rational noise tolerance $\epsilon\ge0$, a budget $0\le b\le n$, and rational reports $y_v$. There are no audits and the target is the uniform mean. A candidate field $x$ ranges over every real vector on the vertices. Its single mismatch set is $\{v:|x_v-y_v|>\epsilon\}$, and the feasible class consists exactly of edge-Lipschitz fields with at most $b$ mismatches:
--
--   $$C(y)=\{x\in\mathbb R^n: |x_u-x_v|\le L\ (uv\in E),\ |\{v:|x_v-y_v|>\epsilon\}|\le b\},\qquad \mu(x)=n^{-1}\sum_v x_v.$$
--
--   The lower and upper endpoints are the infimum and supremum of the feasible means. Their difference is the width $W$, and $r(y)=W/2$. The conditional absolute error of an output $a$ is $\sup_{x\in C(y)}|a-\mu(x)|$. A regular input satisfies the standing graph and parameter assumptions, $b<n$, and $C(y)\ne\varnothing$. The restricted promise additionally fixes $L=1$, $\epsilon=0$, reports in $\{0,1,2,3\}$, three-colorability, diameter exactly two, and $b\le\rho n$.
--
--   For an arbitrary finite simple input graph $H$, the separate densest-subgraph quantity is $\operatorname{dk}_k(H)=\max_{|S|\le k}|E(H[S])|$. An admissible pair has at least one edge and $2\le k\le |V(H)|$. Two-sided factor approximation means membership in $[W/\alpha,\alpha W]$.
--
--   These definitions distinguish one aggregate certificate from separately optimized coordinate ranges and distinguish conditional error from the global recovery radius.
--
--   **Formalization Note** Only numerical machine inputs are rational. Candidate fields remain real. Endpoints use extended reals; all subsequent subtraction and approximation claims are made on nonempty anchored promises. Exact diameter two uses paths of length at most two plus a nonadjacent pair, avoiding disconnected-distance defaults. This file specializes Section 2 to the uniform, unaudited setting of all four targets.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Section 2, Definition 2.1 and Section 3.1, printed pp.5–6 (PDF pp.7–8)

import Mathlib

set_option autoImplicit false

namespace MeanCertificates1424.Hardness

/-- Uniform-mean, no-audit specialization of §2, printed pp.5–6 (PDF pp.7–8).
Only numerical input is rational; candidate fields range over all real vectors. -/
structure UniformInstance where
  n : ℕ
  graph : SimpleGraph (Fin n)
  budget : ℕ
  lipschitz : ℚ
  noise : ℚ
  reports : Fin n → ℚ

/-- Standing assumptions of §2; feasibility and anchoring are separate predicates. -/
def Valid (I : UniformInstance) : Prop :=
  0 < I.n ∧ I.graph.Connected ∧ 0 < I.lipschitz ∧ 0 ≤ I.noise ∧ I.budget ≤ I.n

def EdgeLipschitz (I : UniformInstance) (x : Fin I.n → ℝ) : Prop :=
  ∀ u v, I.graph.Adj u v → |x u - x v| ≤ (I.lipschitz : ℝ)

/-- One mismatch set for the entire field; reports have no smoothness constraint. -/
noncomputable def mismatches (I : UniformInstance) (x : Fin I.n → ℝ) : Finset (Fin I.n) :=
  Finset.univ.filter fun v => |x v - (I.reports v : ℝ)| > (I.noise : ℝ)

noncomputable def feasible (I : UniformInstance) : Set (Fin I.n → ℝ) :=
  {x | EdgeLipschitz I x ∧ (mismatches I x).card ≤ I.budget}

noncomputable def mean (I : UniformInstance) (x : Fin I.n → ℝ) : ℝ :=
  (∑ v, x v) / I.n

/-- The exact endpoints use the complete lattice EReal, including unbounded inputs.
On the empty class lower = +∞ and upper = −∞; on an unbounded class the
corresponding endpoint is infinite. No real conditional supremum defaults are used. -/
noncomputable def lower (I : UniformInstance) : EReal :=
  sInf ((fun x => (mean I x : EReal)) '' feasible I)

noncomputable def upper (I : UniformInstance) : EReal :=
  sSup ((fun x => (mean I x : EReal)) '' feasible I)

/-- Used only on valid, nonempty, anchored instances, where both endpoints are finite.
Empty/unanchored inputs are outside every width/estimation promise below. -/
noncomputable def width (I : UniformInstance) : EReal := upper I - lower I

noncomputable def radius (I : UniformInstance) : EReal := (1 / 2 : ℝ) * width I

noncomputable def conditionalError (I : UniformInstance) (a : ℝ) : EReal :=
  sSup ((fun x => ((|a - mean I x| : ℝ) : EReal)) '' feasible I)

def Regular (I : UniformInstance) : Prop :=
  Valid I ∧ I.budget < I.n ∧ (feasible I).Nonempty

/-- Exact diameter two, without the disconnected-distance default. -/
def DiameterTwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ u v, u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) ∧
  ∃ u v, u ≠ v ∧ ¬ G.Adj u v

def ThreeColorable {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n → Fin 3, ∀ u v, G.Adj u v → c u ≠ c v

/-- Restricted family in Theorem 1.1 and Corollaries 3.2–3.3.
This is a promise on input data, not additional constraints in the feasible class. -/
def Restricted (ρ : ℚ) (I : UniformInstance) : Prop :=
  Regular I ∧ I.lipschitz = 1 ∧ I.noise = 0 ∧
  ThreeColorable I.graph ∧ DiameterTwo I.graph ∧
  (∀ v, I.reports v ∈ ({0, 1, 2, 3} : Finset ℚ)) ∧
  (I.budget : ℚ) ≤ ρ * I.n

/-- Two-sided approximation [W/α, αW]; α≥1 is imposed at each theorem. -/
noncomputable def WidthApprox (α : ℝ) (I : UniformInstance) (a : ℝ) : Prop :=
  (1 / α : ℝ) * width I ≤ (a : EReal) ∧ (a : EReal) ≤ (α : EReal) * width I

noncomputable def ErrorApprox (c : ℝ) (I : UniformInstance) (a : ℝ) : Prop :=
  conditionalError I a ≤ (c : EReal) * radius I

/-- Ordered endpoint pairs enumerate each undirected edge exactly once. -/
noncomputable def edgePairs {r : ℕ} (H : SimpleGraph (Fin r)) : Finset (Fin r × Fin r) := by
  classical
  exact Finset.univ.filter fun e => e.1 < e.2 ∧ H.Adj e.1 e.2

noncomputable def edgeCount {r : ℕ} (H : SimpleGraph (Fin r)) : ℕ := (edgePairs H).card

noncomputable def inducedEdges {r : ℕ} (H : SimpleGraph (Fin r))
    (S : Finset (Fin r)) : ℕ :=
  ((edgePairs H).filter fun e => e.1 ∈ S ∧ e.2 ∈ S).card

/-- §3.1: the maximum over all subsets of cardinality at most k, not degree.
The empty subset is always available and gives zero; this finite supremum is attained. -/
noncomputable def dks {r : ℕ} (H : SimpleGraph (Fin r)) (k : ℕ) : ℕ :=
  Finset.univ.powerset.sup fun S => if S.card ≤ k then inducedEdges H S else 0

def Admissible {r : ℕ} (H : SimpleGraph (Fin r)) (k : ℕ) : Prop :=
  1 ≤ edgeCount H ∧ 2 ≤ k ∧ k ≤ r

end MeanCertificates1424.Hardness


