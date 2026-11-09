-- Prove2me | Definitions.Def_BatchMaxService_Metric_Trees
-- name    : BatchMaxService_Metric_Trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:21:54.122926+00:00
-- url     : https://prove2.me/theorems/7f150e2f-b714-4559-b7eb-0d387cdf1caf
-- title:
--   Actual connecting trees, terminal MSTs and uniform tree work
-- statement:
--   For a finite set $A\subseteq X$, a connecting tree may use any additional vertices in $X$, whereas a terminal spanning tree uses exactly $A$. Trees are finite unordered edge sets with specified nonempty vertex sets, every edge endpoint in that set, and the published connected-forest predicate. With $w(F)=\sum_{\{u,v\}\in E(F)}d(u,v)$, define
--
--   $$\operatorname{ST}_X(A)=\min_{F:\,A\subseteq V(F)}w(F),\qquad\operatorname{MST}(A)=\min_{F:\,V(F)=A}w(F).$$
--
--   Both are literal finite minima over vertex and edge subsets of the complete metric. The source's optional Steiner vertices remain available, and a singleton tree has no edges and weight zero. The published MST predicate is specialized to the complete graph on the subtype of the terminal set.
--
--   A charged deterministic tree procedure returns a finite tree and its computational work. Its approximation contract for $\rho\ge1$ requires $A\subseteq V(F(A))$ and $w(F(A))\le\rho\operatorname{ST}_X(A)$. The separate polynomial-work predicate uses one coefficient and degree for all site counts, metrics and nonempty terminal sets. This contract is a hypothesis only of Proposition 5.6.
--
--   **Formalization Note** The two finite minima are in ENNReal and use $+\infty$ for an empty family. They are not evaluated by the online algorithm. Generic graph connectedness, forests and MST minimality are imported from the published graph definitions.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Sections 3.3 and 5.3, (3.3), (5.13), (5.18), printed pp. 6, 17–18 / PDF pp. 7, 18–19

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsMST

namespace BatchMaxService.Metric

variable {n : ℕ}

/-- Raw finite tree representation; validity is a separate predicate, never a certificate field. -/
structure MetricTree (n : ℕ) where
  vertices : Finset (Fin n)
  edges : Finset (Sym2 (Fin n))
  deriving DecidableEq

/-- Complete graph on exactly U, including diagonal edge names which forests automatically exclude. -/
def completeGraph (U : Finset (Fin n)) :
    CombOpt.SpanningTree.Graph {x // x ∈ U} (Sym2 {x // x ∈ U}) := ⟨id⟩

noncomputable def localEdges (U : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    Finset (Sym2 {x // x ∈ U}) := by
  classical
  exact Finset.univ.filter fun e => Sym2.map Subtype.val e ∈ E

/-- Every endpoint belongs to U and the published connected-forest predicate holds on U. -/
noncomputable def IsTree (F : MetricTree n) : Prop :=
  F.vertices.Nonempty ∧
  (∀ e ∈ F.edges, ∀ x ∈ e, x ∈ F.vertices) ∧
  (completeGraph F.vertices).IsSpanningTree (localEdges F.vertices F.edges)

noncomputable def edgeLength [MetricSpace (Fin n)] : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨dist, fun x y => dist_comm x y⟩

noncomputable def treeWeight [MetricSpace (Fin n)] (F : MetricTree n) : ℝ :=
  ∑ e ∈ F.edges, edgeLength e

/-- Literal finite enumeration of vertex sets and unordered edge sets. -/
noncomputable def treeCandidates (n : ℕ) : Finset (MetricTree n) := by
  classical
  exact (((Finset.univ : Finset (Fin n)).powerset).product
    ((Finset.univ : Finset (Sym2 (Fin n))).powerset)).image
    (fun UE => ⟨UE.1, UE.2⟩)

/-- Source (3.3): the finite minimum of actual trees with vertices anywhere in X.
    Finset.inf is a minimum on a nonempty finite family, with +∞ for an empty one. -/
noncomputable def SteinerCost [MetricSpace (Fin n)] (A : Finset (Fin n)) : ENNReal := by
  classical
  exact ((treeCandidates n).filter fun F => IsTree F ∧ A ⊆ F.vertices).inf
    (fun F => ENNReal.ofReal (treeWeight F))

/-- Terminal-only MST: the finite minimum over trees with exactly A as vertices. -/
noncomputable def MSTCost [MetricSpace (Fin n)] (A : Finset (Fin n)) : ENNReal := by
  classical
  exact ((treeCandidates n).filter fun F => IsTree F ∧ F.vertices = A).inf
    (fun F => ENNReal.ofReal (treeWeight F))

/-- The published minimum-spanning-tree predicate specialized to terminal distances. -/
noncomputable def IsTerminalMST [MetricSpace (Fin n)] (A : Finset (Fin n))
    (F : MetricTree n) : Prop :=
  F.vertices = A ∧ IsTree F ∧
  (completeGraph A).IsMST (fun e => edgeLength (Sym2.map Subtype.val e))
    (localEdges A F.edges)

/-- Unit-cost real arithmetic/comparison programs return their result and a charged work counter.
    The fixed implementation below supplies the counter by loop recurrences. -/
abbrev Charged (α : Type) := α × ℕ
abbrev TreeProcedure (n : ℕ) := Finset (Fin n) → Charged (MetricTree n)

/-- Pointwise tree approximation, assumed only in Proposition 5.6, never in the goal. -/
noncomputable def TreeApproximation [MetricSpace (Fin n)] (ρ : ℝ) (f : TreeProcedure n) : Prop :=
  ∀ A, A.Nonempty → IsTree (f A).1 ∧ A ⊆ (f A).1.vertices ∧
    ENNReal.ofReal (treeWeight (f A).1) ≤ ENNReal.ofReal ρ * SteinerCost A

/-- Uniform in N and in all real weights. The coefficient and degree precede the metric/input. -/
def PolynomialTreeWork (f : ∀ n, MetricSpace (Fin n) → TreeProcedure n) : Prop :=
  ∃ C d : ℕ, 0 < C ∧ ∀ n m A, A.Nonempty → ((f n m) A).2 ≤ C * (n + 1)^d

end BatchMaxService.Metric


