-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
-- name    : OAI_Combinatorics_MatchingEntropy_Polytope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:30:58.753423+00:00
-- url     : https://prove2.me/theorems/e12f52d4-96c1-4c17-9f43-e0757c794e22
-- title:
--   Singleton cuts in a loopless multigraph: crossing equals incidence
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$, every edge $e$ having two endpoints $\ell(e)\neq r(e)$. A vertex $v$ is incident to $e$ if $v\in\{\ell(e),r(e)\}$, and $e$ crosses a set $S\subseteq V$ if exactly one of its endpoints lies in $S$; $\delta(S)$ is the set of crossing edges. For $x\in\mathbb{R}^E$ write $\deg_x(v)=\sum_{e\text{ incident to }v}x_e$ and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$.
--
--   1. *Crossing a singleton.* For every vertex $v$ and edge $e$, the edge $e$ crosses $\{v\}$ if and only if $e$ is incident to $v$.
--   2. *Singleton cut mass.* For every $x\in\mathbb{R}^E$ and $v\in V$,
--   $$
--   x\big(\delta(\{v\})\big)=\deg_x(v).
--   $$
--
--   Looplessness is what makes the first statement true: a loop at $v$ would be incident to $v$ without crossing $\{v\}$. The identity shows that, for one-element odd sets, the odd-cut constraint $x(\delta(S))\ge1$ of the perfect matching polytope concerns the same quantity as the degree constraint $\deg_x(v)=1$.
--
--   **Formalization Note** The two facts are the simp lemmas `crosses_singleton` and `cutMass_singleton`; crossing, cuts, degrees and cut masses come from the project's base definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Polytope.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Polytope.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

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

end MatchingEntropyBounds.LooplessGraph

end

end OAI


