-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
-- name    : OAI_Probability_ThorpCompatibility_ConditionalEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:13:53.923221+00:00
-- url     : https://prove2.me/theorems/5b033208-71ef-4d62-ac81-f2081fdb5581
-- title:
--   Joint law of a distribution and a Markov kernel
-- statement:
--   Let $B$ and $C$ be finite sets, let $P$ be a law (probability mass function) on $C$, and let $K$ be a Markov kernel from $C$ to $B$, that is, a family of laws $K(c)$ on $B$ indexed by $c\in C$. The joint law $P\otimes K$ on $B\times C$ is
--   $$
--   (P\otimes K)(b,c)=P(c)\,K(c)(b),\qquad b\in B,\ c\in C .
--   $$
--   It is nonnegative and has total mass $\sum_{c}P(c)\sum_{b}K(c)(b)=1$.
--
--   This is the law of a pair $(X,Y)$ in which $Y\sim P$ is drawn first and $X$ is then drawn from $K(Y)$. In the compatibility argument a kernel acts as a predictor of one random variable from another. Comparing the true joint law of $(X,Y)$ with $Y_*P\otimes K$ in relative entropy bounds the conditional entropy $H(X\mid Y)$ by the cross-entropy $-\mathbb{E}[\log K(Y)(X)]$, provided the kernel gives positive probability to every pair of values that occurs.
--
--   **Formalization Note** The definition is `Law.kernelJoint P K : Law (β × γ)`. The kernel's output is the first coordinate and the conditioning variable is the second.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ConditionalEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ConditionalEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def kernelJoint (P : Law γ) (K : γ → Law β) : Law (β × γ) where
  mass a := P.mass a.2 * (K a.2).mass a.1
  nonneg a := mul_nonneg (P.nonneg a.2) ((K a.2).nonneg a.1)
  total := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.mul_sum, (K _).total, mul_one]
    exact P.total

end Law
end ThorpCompatibility

end OAI


