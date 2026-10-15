-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
-- name    : OAI_Probability_ThorpCompatibility_Entropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:13:13.718276+00:00
-- url     : https://prove2.me/theorems/5d41b93b-1b51-4b28-b1fc-bd89321cd9f6
-- title:
--   Shannon entropy, conditional mass and conditional entropy of finite laws
-- statement:
--   Let $P$ be a law (probability mass function) on a finite set $\Omega$, and let $X:\Omega\to B$ and $Y:\Omega\to C$ be maps into finite sets, viewed as random variables. Write $X_*P$ for the distribution of $X$ under $P$, and $(X,Y)_*P$ for the joint distribution of the pair.
--
--   1. *Entropy.* The Shannon entropy of $P$, in nats, is
--   $$
--   H(P)=-\mathbb{E}_P[\log P]=-\sum_{a\in\Omega}P(a)\log P(a).
--   $$
--   2. *Conditional mass.* For $a\in\Omega$,
--   $$
--   \pi_{X\mid Y}(a)=\frac{(X,Y)_*P\big(X(a),Y(a)\big)}{Y_*P\big(Y(a)\big)},
--   $$
--   the conditional probability that $X=X(a)$ given $Y=Y(a)$, evaluated at the outcome $a$.
--   3. *Conditional entropy.* $H_P(X\mid Y)=H\big((X,Y)_*P\big)-H\big(Y_*P\big)$, the conditional entropy defined through the chain rule.
--
--   The module also records that two laws with the same mass function are equal. Entropy and conditional entropy are the quantities tracked by the chain-rule bookkeeping of the compatibility argument. The conditional mass is the integrand of the pointwise formula $H_P(X\mid Y)=-\mathbb{E}_P[\log\pi_{X\mid Y}]$.
--
--   **Formalization Note** The definitions are `Law.entropy`, `Law.condMass` and `Law.condEntropy`, and the module also proves the extensionality lemma `Law.ext`. With $\log 0=0$, outcomes with $P(a)=0$ contribute nothing to the entropy. The denominator of `condMass` is positive whenever $P(a)>0$, and division by $0$ gives $0$ otherwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/Entropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Entropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

@[ext] lemma ext (P Q : Law α) (h : ∀ a, P.mass a = Q.mass a) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

noncomputable def entropy (P : Law α) : ℝ := -P.mean (fun a => Real.log (P.mass a))

noncomputable def condMass (P : Law α) (X : α → β) (Y : α → γ) : α → ℝ :=
  fun a => (P.map (fun b => (X b, Y b))).mass (X a, Y a) /
    (P.map Y).mass (Y a)

noncomputable def condEntropy (P : Law α) (X : α → β) (Y : α → γ) : ℝ :=
  (P.map (fun a => (X a, Y a))).entropy - (P.map Y).entropy

end Law
end ThorpCompatibility

end OAI


