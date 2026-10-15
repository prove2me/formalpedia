-- Prove2me | Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
-- name    : OAI_Combinatorics_PerfectMatching_Duality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:44:56.307024+00:00
-- url     : https://prove2.me/theorems/3e672e42-61c1-43be-89aa-467953fa3534
-- title:
--   Exponential tilts, partition functions and linear scores of perfect matchings
-- statement:
--   Let $I$ be a finite index set, let $p\in\mathbb{R}^I$ be a weight vector (typically a probability vector), let $a\in\mathbb{R}^I$ be a score and let $t\in\mathbb{R}$.
--
--   1. *Partition function.* The exponential partition function of the score $a$ under $p$ is
--   $$
--   Z_{p,a}(t)=\sum_{i\in I}p_i\,e^{t a_i}.
--   $$
--   If $p$ is a probability vector (nonnegative with total mass $1$), then $Z_{p,a}(0)=1$.
--   2. *Exponentially tilted law.* The tilt of $p$ by $a$ at parameter $t$ is
--   $$
--   p^{(t)}_i=\frac{p_i\,e^{t a_i}}{Z_{p,a}(t)}\qquad(i\in I).
--   $$
--   When $p$ is nonnegative and not identically zero, $p^{(t)}$ is a probability vector with the same support as $p$, and $p^{(0)}=p$ when $p$ is a probability vector.
--   3. *Linear score of a perfect matching.* For a loopless multigraph $G$ with edge set $E$, edge weights $u\in\mathbb{R}^E$ and a constant $c\in\mathbb{R}$, the score of a perfect matching $M$ is
--   $$
--   \lambda_{u,c}(M)=\sum_{e\in E}u_e\,\mathbf 1_M(e)-c ,
--   $$
--   the total $u$-weight of $M$ minus $c$. The constant $c$ allows the score to be centered under a given law, and centering does not change the tilted law.
--
--   These objects support the duality between laws on perfect matchings and their edge marginals. Tilting a law on $\mathcal M(G)$ by a linear score moves its mean through the matching polytope in a controlled way, and the logarithm of the partition function is the quantity dual to entropy when laws with prescribed means are compared.
--
--   **Formalization Note** `partition p a t` and `tiltedLaw p a t` are defined for any finite index type. The tilted law uses Lean's division convention $x/0=0$, so it is identically $0$ when the partition function vanishes. `partition_zero` records $Z_{p,a}(0)=1$ for $p$ in `probabilitySimplex`, and `linearScore G u c M` is the score in item 3.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Duality.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Duality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic

namespace OAI

/-!
Finite exponential tilts, partition functions, and entropy duality on a face.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Finite exponential partition function, based on a probability law p. -/
def partition {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, p i * Real.exp (t*a i)

def tiltedLaw {ι : Type*} [Fintype ι] (p a : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  p i * Real.exp (t*a i) / partition p a t

@[simp] theorem partition_zero {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) : partition p a 0 = 1 := by
  simpa only [partition, zero_mul, Real.exp_zero, mul_one] using hp.2

/-- A score affine in the matching vector; the constant permits centering
without changing the duality calculation. -/
def linearScore (G : LooplessGraph V E) (u : E → ℝ) (c : ℝ) (M : G.Matching) : ℝ :=
  (∑ e, u e * G.indicator M e) - c

end MatchingEntropy

end

end OAI


