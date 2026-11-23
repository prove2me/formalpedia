-- Prove2me | Definitions.Def_BilevelSOC_SecondOrder_Supplement_NormalGraph
-- name    : BilevelSOC_SecondOrder_Supplement_NormalGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:36:58.162444+00:00
-- url     : https://prove2.me/theorems/1b246c5a-3b5a-43f2-b174-63917ad2140f
-- title:
--   §2.1–2.2 and (4.5) — regular normal graph and metric subregularity
-- statement:
--   For a set $K\subseteq\mathbb R^m$, the regular normal cone at $y\in K$ is the polar of the published sequential Bouligand tangent cone, and its value off $K$ is empty:
--
--   $$\widehat N_K(y)=\{v:\langle v,u\rangle\le0\text{ for every }u\in T_K(y)\}\quad(y\in K).$$
--
--   The graph of a multifunction $S$ is $\{(x,y):y\in S(x)\}$. Metric subregularity at $(x,v)$ requires graph membership and an existential positive constant $\kappa$ and neighborhood $U$ such that $\operatorname{dist}(a,S^{-1}(v))\le\kappa\operatorname{dist}(v,S(a))$ for every $a\in U$. Distances are extended nonnegative reals, so the distance to an empty set is $+\infty$.
--
--   For the fixed convex lower feasible set $K=K(0)$ under Assumption 4.10, the normal graph, full translated feasibility map $\operatorname{gph}\widehat N_K-\{(y,-\nabla_yf(x,y))\}$, and preimage tangent estimate of Lemma 4.11 are defined from $D$, rather than treated as independent parameters. These objects retain the full graph and both components of the residual.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, pp. 3–4, 6–10, 12–17, §2.1–2.2 and (4.5)

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Multipliers
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
def graph (S : V → Set W) : Set (V × W) := {z | z.2 ∈ S z.1}
/-- Extended distance retains distance +∞ to the empty set. -/
def MetricSubregularAt (S : V → Set W) (x : V) (v : W) : Prop :=
  v ∈ S x ∧ ∃ U ∈ 𝓝 x, ∃ κ : NNReal, 0 < κ ∧
    ∀ a ∈ U, Metric.infEDist a {b | v ∈ S b} ≤ (κ : ENNReal) * Metric.infEDist v (S a)
variable {r : ℕ}
def regularNormal (K : Set (Y r)) (y : Y r) : Set (Y r) :=
  {v | y ∈ K ∧ ∀ u ∈ tangentCone K y, inner ℝ v u ≤ 0}
variable {n m p q : ℕ}
def normalGraph (D : Data n m p q) : Set (Y m × Y m) :=
  graph (regularNormal (lowerFeas D 0))
noncomputable def normalResidual (D : Data n m p q) (z : E n × Y m) : Set (Y m × Y m) :=
  {v | ∃ w ∈ normalGraph D, v = w - (z.2, - yGrad D.f z)}
noncomputable def normalTangentEstimate (D : Data n m p q) (z : E n × Y m) : Set (E n × Y m) :=
  {d | (d.2, - yHess D.f z d) ∈
    tangentCone (normalGraph D) (z.2, - yGrad D.f z)}
end BilevelSOC.SecondOrder.Supplement


