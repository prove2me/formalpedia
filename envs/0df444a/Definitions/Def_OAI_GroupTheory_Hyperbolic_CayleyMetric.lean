-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_CayleyMetric
-- name    : OAI_GroupTheory_Hyperbolic_CayleyMetric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:21:35.556633+00:00
-- url     : https://prove2.me/theorems/f1cbd7c7-fe6e-4b4b-8d1f-8ce15143725e
-- title:
--   The word metric of a presented group as a discrete metric
-- statement:
--   Graph distance as a discrete metric, and the word metric of a block presentation.
--
--   1. **Graph metric.** For a connected simple graph $X$, the graph distance is a discrete metric, and each walk in $X$ is a discrete path with the same length whose points are exactly the support of the walk.
--   2. **Cayley metric.** For a block presentation with presented group $\Gamma$, the Cayley graph is the multiplicative Cayley graph of the set of generator images. It is connected because the generators generate, and its graph distance is the Cayley metric on $\Gamma$.
--   3. **Lifted forms.** For $o,a\in\Gamma$ and a radius $T$, the lifted form of a lifted edge $e=(e_0,y)$ with flip $(\bar e_0,x)$ evaluates the tent form of the Cayley metric along the edge:
--   $$
--   \omega(x,y)=\bigl(\tau(x)+\tau(y)\bigr)\bigl(d(a,y)-d(a,x)\bigr),\qquad \tau(z)=\max\bigl(0,\ T-d(o,z)\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/CayleyMetric.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/CayleyMetric.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric
import Definitions.Def_OAI_GroupTheory_Hyperbolic_ThinTriangles

namespace OAI

namespace Release075.Discrete
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)

noncomputable def graphMetric : Metric V where
  dist := X.dist
  self _ := X.dist_self
  symm _ _ := X.dist_comm
  triangle _ _ _ := hX.dist_triangle

noncomputable def walkPath {a b : V} (p : X.Walk a b) : Path (graphMetric X hX) a b where
  length := p.length
  point := p.getVert
  zero := p.getVert_zero
  stable _ h := p.getVert_of_length_le h
  step _ h := by
    change X.dist _ _ ≤ 1
    exact (X.dist_eq_one_iff_adj.mpr (p.adj_getVert_succ h)).le

@[simp] theorem walkPath_mem {a b x : V} (p : X.Walk a b) :
    (walkPath X hX p).Mem x ↔ x ∈ p.support := by
  classical
  constructor
  · rintro ⟨i,_,rfl⟩
    exact p.getVert_mem_support i
  · intro hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i,by change i ≤ p.length; rw [p.length_support] at hi; omega,?_⟩
    exact (p.getVert_eq_support_getElem (by rw [p.length_support] at hi; omega)).trans he

end Release075.Discrete

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev cayley : SimpleGraph d.GroupType := SimpleGraph.mulCayley (Set.range d.edge)
noncomputable abbrev cayleyMetric : Discrete.Metric d.GroupType :=
  Discrete.graphMetric d.cayley d.cayley_connected

noncomputable def liftedForm (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) : ℤ :=
  d.cayleyMetric.form o a T (d.liftedFlip e).2 e.2

end Release075.BlockPresentation

namespace Release075.TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI


