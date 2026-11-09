-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Instance
-- name    : NearLinearRSP_TwoResources_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:32.035517+00:00
-- url     : https://prove2.me/theorems/9b43ae8e-2185-4e44-9b01-96ef4b58194a
-- title:
--   Nonnegative resources, directed paths and the RSP optimum
-- statement:
--   Let $G=(V,E)$ be a finite directed graph, with $n$ vertices labelled $0,\ldots,n-1$ and a fixed enumeration of its distinct ordered-pair edges. A separate resource instance consists of a source $s\in V$, nonnegative real edge lengths $\ell$, nonnegative real edge costs $c$, and a nonnegative budget $C$. A path is a nonempty finite vertex sequence whose successive pairs are edges. Repeated vertices and traversals are allowed, and resource sums count every occurrence. The one-vertex path $[s]$ has both sums zero.
--
--   A path to $t$ is feasible when its cost is at most the original budget $C$. Its extended optimal length is
--   $$
--   \operatorname{OPT}_C(t)=\inf\{\ell(P):P\text{ is an }s\text{–}t\text{ path},\ c(P)\le C\}\in[0,\infty].
--   $$
--   The empty feasible set has infimum infinity. The aspect ratio $W$ uses only positive lengths, and equals one when there are none. The active vertices are the source and edge endpoints; isolated targets receive implicit defaults.
--
--   These definitions build on the separate general graph object and provide the common resource layer for every result. Approximation can also be expressed by comparison with every exactly feasible path, which avoids requiring a supplied optimum or an attainment hypothesis.
--
--   **Formalization Note** The graph object is separate from its resource functions. Natural labels and the input edge ordering change no graph instance. Nonnegative real numbers are represented by NNReal and the optimum by ENNReal. Off-edge resource values are ignored. The totalized preprocessing scale is $\max(1,m)(1+\log\max(2,n))(1+\log(\max(2,n)W))/\varepsilon^9$.
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), pp.1–4, Definition 1.1, footnote 4 and Section 2

import Definitions.Def_NearLinearRSP_TwoResources_Digraph

set_option autoImplicit false
open scoped NNReal ENNReal

namespace NearLinearRSP.TwoResources

/-- Resources are separate from the general graph object. -/
structure Instance where
  graph : Digraph
  source : ℕ
  source_valid : source < graph.n
  length : ℕ → ℕ → ℝ≥0
  cost : ℕ → ℕ → ℝ≥0
  budget : ℝ≥0

def IsPath (G : Digraph) (s t : ℕ) (P : List ℕ) : Prop :=
  P.head? = some s ∧ P.getLast? = some t ∧
    P.IsChain (fun u v => (u, v) ∈ G.edges)

noncomputable def pathWeight (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) : ℝ :=
  ((P.zip P.tail).map (fun e => (w e.1 e.2 : ℝ))).sum

def Feasible (I : Instance) (t : ℕ) (P : List ℕ) : Prop :=
  IsPath I.graph I.source t P ∧ pathWeight I.cost P ≤ I.budget

/-- Extended optimum: the infimum of the empty feasible set is infinity. -/
noncomputable def optimum (I : Instance) (t : ℕ) : ℝ≥0∞ :=
  ⨅ (P : List ℕ) (_ : Feasible I t P), ENNReal.ofReal (pathWeight I.length P)

/-- A comparator formulation includes every exactly feasible path, including zero optima. -/
def ApproxWitness (I : Instance) (ε : ℝ) (t : ℕ) (P : List ℕ) : Prop :=
  IsPath I.graph I.source t P ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget ∧
    ∀ R : List ℕ, Feasible I t R → pathWeight I.length P ≤ (1 + ε) * pathWeight I.length R

noncomputable def positiveLengths (I : Instance) : List ℝ :=
  (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).filter (0 < ·)

noncomputable def firstPositiveLength (I : Instance) : ℝ :=
  (positiveLengths I).foldl min ((positiveLengths I).headD 1)

noncomputable def largestLength (I : Instance) : ℝ :=
  (positiveLengths I).foldl max 0

noncomputable def aspectRatio (I : Instance) : ℝ :=
  if (positiveLengths I).isEmpty then 1 else largestLength I / firstPositiveLength I

/-- Only incident vertices and the source need records; isolated vertices have defaults. -/
def activeVertices (I : Instance) : List ℕ :=
  (I.source :: I.graph.edges.flatMap (fun e => [e.1, e.2])).eraseDups

noncomputable def preprocessingScale (I : Instance) (ε : ℝ) : ℝ :=
  (max 1 I.graph.edges.length : ℕ) *
    (1 + Real.log (max 2 I.graph.n : ℕ)) *
    (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) / ε ^ 9

end NearLinearRSP.TwoResources


