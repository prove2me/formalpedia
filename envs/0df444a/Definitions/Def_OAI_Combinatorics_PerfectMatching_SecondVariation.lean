-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
-- name    : OAI_Combinatorics_PerfectMatching_SecondVariation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:46:59.007118+00:00
-- url     : https://prove2.me/theorems/416c1351-450c-4966-ae29-79914e95ccef
-- title:
--   Entropy defect of an edge marginal against the nonlinear barrier
-- statement:
--   Let $G$ be a loopless multigraph with vertex set $V$ and finite edge set $E$: every edge $e$ has two endpoints $\ell(e)\neq r(e)$, and parallel edges are distinct elements of $E$. A vertex $v$ is *incident* to $e$ if $v\in\{\ell(e),r(e)\}$. A *perfect matching* is a set $M\subseteq E$ such that every vertex is incident to exactly one edge of $M$; $\mathcal M(G)$ denotes the finite set of perfect matchings and $\mathbf 1_M\in\{0,1\}^E$ the indicator vector of $M$. Write $\eta(s)=-s\log s$ (with $\eta(0)=0$) and, for a real vector $z$ indexed by a finite set, $H(z)=\sum_i\eta(z_i)$ for its Shannon entropy. A *feasible law* for $y\in\mathbb{R}^E$ is a probability vector $p=(p_M)_{M\in\mathcal M(G)}$ (so $p_M\ge 0$ and $\sum_M p_M=1$) whose mean is $y$, that is, $\sum_{M}p_M\,\mathbf 1_M(e)=y_e$ for every edge $e$; write $\mathcal F_G(y)$ for the set of feasible laws and $H_{\max}(G,y)=\sup\{H(q):q\in\mathcal F_G(y)\}$ for the maximal entropy of a feasible law.
--
--   1. *Entropy defect.* For a real parameter $m$ and an edge vector $y\in\mathbb{R}^E$,
--   $$
--   D_m(y)=\Phi_m\big(H(y)\big)-H_{\max}(G,y)=H(y)-8m\big(1-e^{-H(y)/m}\big)-H_{\max}(G,y),
--   $$
--   where $\Phi_m(h)=h-8m(1-e^{-h/m})$ is the nonlinear entropy barrier and $H(y)=\sum_{e\in E}\eta(y_e)$ is the entropy of the edge vector itself.
--
--   For a multigraph on $2m$ vertices, the main entropy comparison $H(y)-H_{\max}(G,y)\le 8m(1-e^{-H(y)/m})$ says exactly that $D_m(y)\le 0$ for all $y$ in the perfect matching polytope. The defect is the objective of the variational argument: its maximum over the polytope is attained, and the second-order condition at a maximizer is analysed.
--
--   **Formalization Note** The definition is `entropyDefect G m y := entropyBarrier m (entropy y) - maxMatchingEntropy G y`. Here `maxMatchingEntropy` is the real supremum `sSup` of the entropies of feasible laws. With Lean's conventions it equals $0$ when there is no feasible law, i.e. outside the polytope, and the logarithm satisfies $\log 0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/SecondVariation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/SecondVariation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus

namespace OAI

/-!
The second-variation inequality at a maximum of the actual entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropyDefect (G : LooplessGraph V E) (m : ℝ) (y : E → ℝ) : ℝ :=
  entropyBarrier m (entropy y)-maxMatchingEntropy G y

end MatchingEntropy

end

end OAI


