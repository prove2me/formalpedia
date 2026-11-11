-- Prove2me | Definitions.Def_StableMSR_Recovery_Model
-- name    : StableMSR_Recovery_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:57:34.195352+00:00
-- url     : https://prove2.me/theorems/0ca63ca1-353f-4ca5-a424-b7a0a438dc63
-- title:
--   Finite MSR partitions, objectives, and stability
-- statement:
--   Let $P=\{0,\ldots,n-1\}$ with its input order. An unordered exact-$k$ partition of $W\subseteq P$ is a family of $k$ pairwise disjoint nonempty subsets with union $W$. The metric-array predicate asks that the real table be the distance function of a Mathlib metric space; no rationality or dimension restriction is imposed.
--
--   For a nonempty cluster $C$ and any real array $\delta$, define
--   $$
--   e_\delta(c,C)=\max_{x\in C}\delta(c,x),\qquad
--   r_\delta(C)=\min_{c\in C}e_\delta(c,C),\qquad
--   \operatorname{cost}_\delta(\mathcal P)=\sum_{C\in\mathcal P}r_\delta(C).
--   $$
--   Optimality and uniqueness compare all feasible unordered partitions. A $\gamma$-perturbation is symmetric and satisfies $d\le\delta\le\gamma d$ on every pair; it has no triangle condition. Stability means that the same partition is uniquely optimal under every such array. Restriction retains the whole blocks contained in a set; alignment means the set is a union of whole blocks.
--
--   This supplies a shared objective and stability definition for every structural statement. **Formalization Note** Empty-set eccentricity and radius are set to zero, but feasible clusters and radius claims are nonempty. Feasibility also represents the empty region with zero clusters. The input type `Fin n` is an order-preserving relabelling, not a rational or geometric restriction.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), pp. 1–2, 4–6, model and §3 notation; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Mathlib

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

abbrev Point (n : ℕ) := Fin n
abbrev Cluster (n : ℕ) := Finset (Point n)
abbrev Partition (n : ℕ) := Finset (Cluster n)

/-- Unordered exact-k partitions of W. Empty W has the unique zero-block partition. -/
def Feasible {n : ℕ} (W : Cluster n) (k : ℕ) (Q : Partition n) : Prop :=
  Q.card = k ∧ (∀ C ∈ Q, C.Nonempty) ∧ (Q : Set (Cluster n)).Pairwise Disjoint ∧ Q.biUnion id = W

/-- All finite real metric arrays; the general metric object is Mathlib's MetricSpace. -/
def IsMetricArray {n : ℕ} (d : Point n → Point n → ℝ) : Prop :=
  ∃ m : MetricSpace (Point n), ∀ x y, @dist (Point n) m.toDist x y = d x y

noncomputable def eccentricity {n : ℕ} (d : Point n → Point n → ℝ)
    (C : Cluster n) (c : Point n) : ℝ :=
  if h : C.Nonempty then C.sup' h (d c) else 0

/-- The empty-set value is a convention only; all cluster uses are guarded by nonemptiness. -/
noncomputable def radius {n : ℕ} (d : Point n → Point n → ℝ) (C : Cluster n) : ℝ :=
  if h : C.Nonempty then C.inf' h (eccentricity d C) else 0

noncomputable def cost {n : ℕ} (d : Point n → Point n → ℝ) (Q : Partition n) : ℝ :=
  ∑ C ∈ Q, radius d C

noncomputable def OptimalCenter {n : ℕ} (d : Point n → Point n → ℝ)
    (C : Cluster n) (c : Point n) : Prop := c ∈ C ∧ eccentricity d C c = radius d C

noncomputable def Optimal {n : ℕ} (d : Point n → Point n → ℝ)
    (W : Cluster n) (k : ℕ) (O : Partition n) : Prop :=
  Feasible W k O ∧ ∀ Q, Feasible W k Q → cost d O ≤ cost d Q

noncomputable def UniqueOptimal {n : ℕ} (d : Point n → Point n → ℝ)
    (W : Cluster n) (k : ℕ) (O : Partition n) : Prop :=
  Optimal d W k O ∧ ∀ Q, Optimal d W k Q → Q = O

/-- Symmetric increases, without any triangle inequality on d'. Includes the diagonal. -/
def Perturbation {n : ℕ} (d : Point n → Point n → ℝ) (γ : ℝ)
    (d' : Point n → Point n → ℝ) : Prop :=
  (∀ x y, d' x y = d' y x) ∧ ∀ x y, d x y ≤ d' x y ∧ d' x y ≤ γ * d x y

noncomputable def Stable {n : ℕ} (d : Point n → Point n → ℝ)
    (k : ℕ) (γ : ℝ) (O : Partition n) : Prop :=
  Feasible Finset.univ k O ∧
    ∀ d', Perturbation d γ d' → UniqueOptimal d' Finset.univ k O

noncomputable def restrictPartition {n : ℕ} (O : Partition n) (W : Cluster n) : Partition n :=
  O.filter (fun C => C ⊆ W)

def Aligned {n : ℕ} (O : Partition n) (W : Cluster n) : Prop :=
  ∃ F ⊆ O, F.biUnion id = W

end StableMSR.Recovery


