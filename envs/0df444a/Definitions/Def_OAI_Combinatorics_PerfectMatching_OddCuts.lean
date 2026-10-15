-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
-- name    : OAI_Combinatorics_PerfectMatching_OddCuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:48:47.483357+00:00
-- url     : https://prove2.me/theorems/5209a674-18a8-4aff-953b-6aa56ddda813
-- title:
--   Crossing edges, degrees, cut masses and the odd-cut constraint system
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$, each edge $e$ having endpoints $\ell(e)\neq r(e)$. Let $x\in\mathbb{R}^E$ be an edge vector and $S\subseteq V$ a set of vertices.
--
--   1. *Crossing edges and cuts.* An edge $e$ *crosses* $S$ if exactly one of its endpoints lies in $S$. The cut $\delta(S)\subseteq E$ is the set of edges crossing $S$. Parallel edges are kept as distinct elements of $\delta(S)$, and $\delta(V\setminus S)=\delta(S)$.
--   2. *Degree.* The $x$-degree of a vertex $v$ is
--   $$
--   \deg_x(v)=\sum_{e\in E:\ v\in\{\ell(e),r(e)\}}x_e .
--   $$
--   3. *Cut mass.* The $x$-mass of the cut of $S$ is
--   $$
--   x\big(\delta(S)\big)=\sum_{e\in\delta(S)}x_e .
--   $$
--   4. *The degree and odd-cut constraint system.*
--   $$
--   Q(G)=\Big\{x\in\mathbb{R}^E:\ x_e\ge0\ \ \forall e\in E,\quad \deg_x(v)=1\ \ \forall v\in V,\quad x\big(\delta(S)\big)\ge1\ \ \forall S\subseteq V\text{ with }|S|\text{ odd}\Big\}.
--   $$
--
--   Degree and cut mass are linear in $x$: $\deg_{ax+by}(v)=a\deg_x(v)+b\deg_y(v)$ and $(ax+by)(\delta(S))=a\,x(\delta(S))+b\,y(\delta(S))$ for all real $a,b$. The set $Q(G)$ is the inequality system in Edmonds' description of the perfect matching polytope by nonnegativity, degree and odd-cut constraints. Every indicator vector of a perfect matching satisfies it. The odd sets range over all subsets of odd size, including singletons and, when $|V|$ is odd, the whole of $V$ (whose cut is empty).
--
--   **Formalization Note** The definitions are `Crosses`, `cut`, `degree`, `cutMass` and `constraintPolytope`, with $S$ a `Finset V`. The module also provides a decidability instance for crossing and the lemmas `mem_cut`, `crosses_compl`, `cut_compl`, `degree_linear` and `cutMass_linear`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/OddCuts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/OddCuts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation

namespace OAI

/-!
Degree and odd-cut constraints for the perfect matching polytope.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- Exactly one endpoint in S; edge identities are kept, including parallels. -/
def Crosses (G : LooplessGraph V E) (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

instance crossesDecidable (G : LooplessGraph V E) (S : Finset V) (e : E) :
    Decidable (G.Crosses S e) := inferInstanceAs (Decidable
      ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

def cut (G : LooplessGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (G.Crosses S)

def degree (G : LooplessGraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if G.Incident v e then x e else 0

def cutMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.cut S, x e

/-- The degree and odd-cut constraint system. -/
def constraintPolytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ (∀ v, G.degree x v = 1) ∧
    (∀ S : Finset V, Odd S.card → 1 ≤ G.cutMass x S)}

omit [Fintype V] [DecidableEq E] in
@[simp] theorem mem_cut (G : LooplessGraph V E) (S : Finset V) (e : E) :
    e ∈ G.cut S ↔ G.Crosses S e := by simp [cut]

omit [Fintype E] [DecidableEq E] in
theorem crosses_compl (G : LooplessGraph V E) (S : Finset V) (e : E) :
    G.Crosses Sᶜ e ↔ G.Crosses S e := by
  simp only [Crosses, Finset.mem_compl, not_not]
  tauto

omit [DecidableEq E] in
@[simp] theorem cut_compl (G : LooplessGraph V E) (S : Finset V) :
    G.cut Sᶜ = G.cut S := by ext; simp [crosses_compl]

omit [Fintype V] [DecidableEq E] in
theorem degree_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (v : V) :
    G.degree (a • x+b • y) v = a*G.degree x v+b*G.degree y v := by
  have he : ∀ e, (if G.Incident v e then (a • x+b • y) e else 0) =
      a*(if G.Incident v e then x e else 0)+b*(if G.Incident v e then y e else 0) := by
    intro e
    by_cases h : G.Incident v e <;> simp [h]
  simp only [degree, he, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype V] [DecidableEq E] in
theorem cutMass_linear (G : LooplessGraph V E) (x y : E → ℝ) (a b : ℝ) (S : Finset V) :
    G.cutMass (a • x+b • y) S = a*G.cutMass x S+b*G.cutMass y S := by
  simp [cutMass, Finset.sum_add_distrib, Finset.mul_sum]

end LooplessGraph

end MatchingEntropy

end

end OAI


