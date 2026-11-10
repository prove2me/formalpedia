-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_Graphs
-- name    : EdgeSublinearMWIS_Main_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:40:21.972208+00:00
-- url     : https://prove2.me/theorems/4d36e7a2-a889-452c-952b-28bc8f3f5e16
-- title:
--   Finite graph classes, separators and independent-set objectives
-- statement:
--   A graph has labels $0,\ldots,n-1$. A hereditary class is closed under every induced injection, including relabelings. A separator $S\subseteq W$ is balanced when every component $D$ of $G[W\setminus S]$ satisfies $3|D|\le2|W|$. The separation number bounds separator sizes on every induced subgraph. Strongly edge-sublinear classes have uniform $0\le b<1$, $c>0$ with separator size at most $cm^b$ for every member with $m\ge1$ edges.
--
--   For rational weights, including negative weights, the objective is
--   $$\alpha_w(G[W])=\max\{\sum_{v\in I}w_v:I\subseteq W,\ I\text{ independent}\}.$$
--   The empty independent set is included. The energy sums $x_ux_v$ over each unordered edge once. Treewidth is the referenced finite-tree definition; edgeless and empty graphs have treewidth zero. This file also supplies the uniform treewidth bound (2), independent blow-ups with nonempty fibers, the recursion height, and an integer threshold with an unspecified class coefficient. These are data and predicates, without algorithmic correctness assumptions.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §§1–2, Eq. (2); §3; §5.2; §6, p.5 (PDF p.5), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TreewidthApprox_Pushed_Setting

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

abbrev GraphClass := (n : ℕ) → SimpleGraph (Fin n) → Prop

/-- Closure under every induced injection also includes invariance under relabeling. -/
def Hereditary (C : GraphClass) : Prop :=
  ∀ {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m ↪ Fin n), C n G →
    (∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) → C m H

noncomputable def components {n : ℕ} (G : SimpleGraph (Fin n))
    (W S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  ((W \ S).image (TreewidthApprox.Pushed.avoidComp G (S ∪ (Finset.univ \ W))))

def Balanced {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) : Prop :=
  S ⊆ W ∧ ∀ D ∈ components G W S, 3 * D.card ≤ 2 * W.card

noncomputable def separationNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {s : ℕ | ∀ W : Finset (Fin n), ∃ S, Balanced G W S ∧ S.card ≤ s}

noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).card

noncomputable def degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (G.neighborSet v).ncard

/-- Only nonzero edge counts are restricted; arbitrarily many isolated vertices are allowed. -/
def StronglyEdgeSublinear (C : GraphClass) : Prop :=
  Hereditary C ∧ ∃ b c : ℝ, 0 ≤ b ∧ b < 1 ∧ 0 < c ∧
    ∀ n (G : SimpleGraph (Fin n)), C n G → 1 ≤ edgeCount G →
      ∃ S, Balanced G Finset.univ S ∧ (S.card : ℝ) ≤ c * (edgeCount G : ℝ) ^ b

/-- Equation (2), including the edgeless case tw = 0. -/
def TreewidthBound (C : GraphClass) (a : ℕ) (K : ℝ) : Prop :=
  0 < K ∧ ∀ n (G : SimpleGraph (Fin n)), C n G →
    (PlantedSubgraphLD.tw G : ℝ) ≤ K * (edgeCount G : ℝ) ^ (1 - 1 / (a : ℝ))

noncomputable def alpha {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) : ℕ := by
  classical
  exact (W.powerset.filter (fun (I : Finset (Fin n)) => G.IsIndepSet (I : Set (Fin n)))).sup Finset.card

/-- A maximum over the nonempty finite family of independent subsets of W. -/
noncomputable def weightedAlphaOn {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (w : Fin n → ℚ) : ℝ :=
  sSup {z : ℝ | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧
    z = ∑ v ∈ I, (w v : ℝ)}

noncomputable def weightedAlpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) : ℝ :=
  weightedAlphaOn G Finset.univ w

def vertexSum {n : ℕ} (x : Fin n → ℝ) (W : Finset (Fin n)) : ℝ := ∑ v ∈ W, x v

noncomputable def edgeEnergy {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) : ℝ := by
  classical
  exact ∑ e ∈ ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)), x e.1 * x e.2

def Light {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    (δ : ℝ) (x : Fin n → ℝ) : Prop :=
  Balanced G W S ∧ vertexSum x S ≤ δ * vertexSum x W

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Integer test for ceil(log base 3/2 n), with h(0)=0. The finite search bound
2n is sufficient; establishing this agreement is a theorem obligation. -/
def height (n : ℕ) : ℕ :=
  ((List.range (2 * n + 1)).find? (fun j => decide (2 ^ j * n ≤ 3 ^ j))).getD (2 * n)

/-- A fixed integer B absorbs the class constant and the change of logarithm base. -/
def threshold (B a n : ℕ) (δ : ℚ) : ℕ :=
  max 1 ⌈(B : ℚ) * ((height n : ℚ) / δ) ^ (4 * a - 2)⌉₊

def BlowupClass (C : GraphClass) : GraphClass := fun m H =>
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)), C n G ∧ ∃ f : Fin m → Fin n,
    Function.Surjective f ∧ ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)

end EdgeSublinearMWIS.Main


