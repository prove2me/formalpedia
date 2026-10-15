-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
-- name    : OAI_Probability_ThorpCompatibility_Prediction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:16:12.88098+00:00
-- url     : https://prove2.me/theorems/1e448260-a478-45e0-bba3-1bd28015a324
-- title:
--   Conditioning a finite law on an event and the conditional law of one variable given another
-- statement:
--   Let $P$ be a law (probability mass function) on a finite set $\Omega$, let $S\subseteq\Omega$ be an event, and let $X:\Omega\to B$ and $Y:\Omega\to C$ be maps into finite sets.
--
--   1. *Restriction.* If $P(S)>0$, the conditional law $P(\cdot\mid S)$ is
--   $$
--   P(a\mid S)=\frac{\mathbf 1[a\in S]\,P(a)}{P(S)},\qquad a\in\Omega,
--   $$
--   and if $P(S)=0$ the restriction is defined to be $P$ itself.
--   2. *Prediction.* For $y\in C$, the prediction of $X$ from $Y=y$ is the law on $B$
--   $$
--   \widehat P_{X\mid Y=y}=X_*\big(P(\cdot\mid Y=y)\big),\qquad\text{so that}\qquad \widehat P_{X\mid Y=y}(x)=P(X=x\mid Y=y).
--   $$
--   This is the conditional distribution of $X$ given $Y=y$. If $P(Y=y)=0$ it is the unconditional distribution $X_*P$.
--
--   The prediction is the canonical kernel from $C$ to $B$. Averaged over $Y$, its entropy equals the conditional entropy $H(X\mid Y)$. It is also the reference law against which the entry-by-entry entropy costs of the compatibility argument are measured.
--
--   **Formalization Note** The definitions are `Law.restrict P S` and `Law.predict P X Y y = (P.restrict (fun a => Y a = y)).map X`. The fallback for events of probability zero is a convention that keeps both operations total. It plays no role for values $y$ that occur with positive probability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/Prediction.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Prediction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def restrict (P : Law α) (S : α → Prop) : Law α :=
  if h : 0 < P.prob S then {
    mass := fun a => (if S a then P.mass a else 0) / P.prob S
    nonneg := fun a => div_nonneg (by split_ifs <;> simp_all [P.nonneg]) h.le
    total := by
      rw [← Finset.sum_div]
      have he : (∑ a, if S a then P.mass a else 0) = P.prob S := by
        unfold prob
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : S a <;> simp [h]
      rw [he, div_self h.ne']
  } else P

noncomputable def predict (P : Law α) (X : α → β) (Y : α → γ) (y : γ) : Law β :=
  (P.restrict (fun a => Y a = y)).map X

end Law
end ThorpCompatibility

end OAI


