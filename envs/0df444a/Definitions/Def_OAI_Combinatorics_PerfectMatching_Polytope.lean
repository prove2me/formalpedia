-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
-- name    : OAI_Combinatorics_PerfectMatching_Polytope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:52:43.179647+00:00
-- url     : https://prove2.me/theorems/e3e2b5f9-919f-4129-818b-012835bad6d9
-- title:
--   Simple support graph of an edge vector and singleton cuts in a multigraph
-- statement:
--   Let $G$ be a loopless multigraph with finite vertex set $V$ and finite edge set $E$, each edge $e$ having endpoints $\ell(e)\neq r(e)$, and let $x\in\mathbb{R}^E$.
--
--   1. *Simple support graph.* $\operatorname{supp}_G(x)$ is the simple graph on $V$ in which distinct vertices $v,w$ are adjacent if and only if some edge $e$ with $x_e>0$ joins them, i.e. $\{\ell(e),r(e)\}=\{v,w\}$. It forgets which of several parallel edges carries the positive weight, and it has no loops because $G$ has none.
--   2. *Singleton cuts.* An edge crosses the singleton $\{v\}$ if and only if it is incident to $v$, which uses looplessness. Consequently the cut mass of a singleton is the degree:
--   $$
--   x\big(\delta(\{v\})\big)=\sum_{e\ni v}x_e=\deg_x(v).
--   $$
--
--   The support graph turns questions about the positive part of a fractional matching on a multigraph into questions about an ordinary simple graph, where Tutte's criterion for perfect matchings is available. This is used in proving Edmonds' description of the perfect matching polytope. The singleton identity shows that for one-element odd sets the odd-cut constraint concerns the same quantity as the degree constraint.
--
--   **Formalization Note** The support graph is `supportSimple G x : SimpleGraph V`, and the singleton facts are the simp lemmas `crosses_singleton` and `cutMass_singleton`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Polytope.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Polytope.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Tutte's criterion and Edmonds' perfect matching polytope theorem for multigraphs.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

/-- The simple support graph forgets only parallel-edge identities. -/
def supportSimple (G : LooplessGraph V E) (x : E → ℝ) : SimpleGraph V where
  Adj v w := ∃ e, 0 < x e ∧ ((G.left e=v ∧ G.right e=w) ∨ (G.left e=w ∧ G.right e=v))
  symm := ⟨by intro v w; rintro ⟨e,hx,h⟩; exact ⟨e,hx,h.symm⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e,_,(⟨hl,hr⟩ | ⟨hl,hr⟩)⟩ <;> exact G.loopless e (hl.trans hr.symm)⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem crosses_singleton (G : LooplessGraph V E) (v : V) (e : E) :
    G.Crosses {v} e ↔ G.Incident v e := by
  have hh := G.loopless e
  simp only [Crosses, Finset.mem_singleton, Incident]
  have hn : ¬ (G.left e=v ∧ G.right e=v) := fun h => hh (h.1.trans h.2.symm)
  tauto

omit [Fintype V] [DecidableEq E] in
@[simp] theorem cutMass_singleton (G : LooplessGraph V E) (x : E → ℝ) (v : V) :
    G.cutMass x {v} = G.degree x v := by
  simp [cutMass,cut,Finset.sum_filter,degree]

end LooplessGraph

end MatchingEntropy

end

end OAI


