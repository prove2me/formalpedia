-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
-- name    : OAI_Combinatorics_MatchingEntropy_Duality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:35:25.363585+00:00
-- url     : https://prove2.me/theorems/800c8b83-bca4-42af-8e72-d013042a5cf9
-- title:
--   Partition function (exponential moment) of a finite weighted family
-- statement:
--   Let $I$ be a finite index set, $p\in\mathbb{R}^I$ a weight vector and $a\in\mathbb{R}^I$ a real function on $I$. The *partition function* of $a$ with respect to $p$ is
--   $$
--   Z_{p,a}(t)=\sum_{i\in I}p_i\,e^{t a_i}\qquad(t\in\mathbb{R}).
--   $$
--   If $p$ lies in the probability simplex, i.e. $p_i\ge0$ for all $i$ and $\sum_i p_i=1$, then $Z_{p,a}(0)=1$.
--
--   For a probability vector $p$, $Z_{p,a}(t)$ is the expectation of $e^{ta}$ under the law $p$, the moment generating function of the random variable $a$, and $\log Z_{p,a}$ is its cumulant generating function. Exponentially tilted laws $p_i e^{ta_i}/Z_{p,a}(t)$ and the convex function $t\mapsto\log Z_{p,a}(t)$ are the standard tools in convex-duality arguments for entropy, for example in variational formulas relating entropy to exponential moments.
--
--   **Formalization Note** The definition is `partition p a t` and the normalization is the simp lemma `partition_zero`; $p$ is not required to be nonnegative in the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Duality.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Duality.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def partition {ι : Type uι} [Fintype ι] (p a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (t*a i)

@[simp] theorem partition_zero {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) : partition p a 0 = 1 := by
  simpa only [partition, zero_mul, Real.exp_zero, mul_one] using hp.2

end MatchingEntropyBounds

end

end OAI


