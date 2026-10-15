-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
-- name    : OAI_Combinatorics_PerfectMatching_Coupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:50:15.448196+00:00
-- url     : https://prove2.me/theorems/26f2ec97-f3e0-4339-9b5b-19b3414297f3
-- title:
--   Pushforward weights and the label-matching coupling of two finite laws
-- statement:
--   Let $A$ and $B$ be finite sets, $C$ a set of labels with decidable equality, $p\in\mathbb{R}^A$ and $q\in\mathbb{R}^B$ weight vectors, and $f:A\to C$, $g:B\to C$ labelling maps.
--
--   1. *Pushforward (fiber) mass.* For a label $c\in C$,
--   $$
--   (f_*p)(c)=\sum_{a\in A:\ f(a)=c}p_a ,
--   $$
--   the total $p$-weight of the fiber $f^{-1}(c)$.
--   2. *Label-matching coupling.* The joint weight of a pair $(a,b)\in A\times B$ is
--   $$
--   \pi(a,b)=\begin{cases}\dfrac{p_a\,q_b}{(f_*p)(f(a))}, & f(a)=g(b),\\ 0, & f(a)\neq g(b).\end{cases}
--   $$
--
--   Only pairs with equal labels receive mass. If $p$ and $q$ are probability vectors with the same pushforward, $f_*p=g_*q$, then $\pi$ is a coupling of $p$ and $q$: its marginals on $A$ and on $B$ are $p$ and $q$. The common label is then distributed as $f_*p=g_*q$, and given a label $c$ of positive mass the two coordinates are independent, with laws $p$ conditioned on $f^{-1}(c)$ and $q$ conditioned on $g^{-1}(c)$. In the intended application, $p$ and $q$ are laws on perfect matchings of the two graphs obtained by contracting either side of an odd cut, and the label is the edge each matching uses across the cut. Compatible pairs can then be glued into perfect matchings of the original graph.
--
--   **Formalization Note** The definitions are `fiberMass p f c` and `jointLaw p q f g z` with $z=(a,b)$. The quotient uses Lean's convention $x/0=0$, so a pair whose label has zero $f_*p$-mass gets weight $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Coupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Coupling.lean by skeleton subtraction
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

namespace OAI

/-!
Finite pushforwards and couplings with a prescribed common marginal.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

/-- Finite pushforward weights. -/
def fiberMass {A C : Type*} [Fintype A] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (c : C) : ℝ := ∑ a, if f a = c then p a else 0

/-- The explicit cut-choice coupling. Only equal choices receive mass. -/
def jointLaw {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    (p : A → ℝ) (q : B → ℝ) (f : A → C) (g : B → C) (z : A × B) : ℝ :=
  if f z.1 = g z.2 then p z.1*q z.2 / fiberMass p f (f z.1) else 0

end MatchingEntropy

end

end OAI


