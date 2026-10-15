-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
-- name    : OAI_Probability_ThorpCompatibility_LightRescaling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:14:49.655778+00:00
-- url     : https://prove2.me/theorems/e6f0d98b-3a20-4fad-82db-9e9e5d630791
-- title:
--   Event probabilities and the light-part rescaling of a finite law
-- statement:
--   Let $P$ be a law (probability mass function) on a finite set $\Omega$, and let $L,S\subseteq\Omega$ be events.
--
--   1. *Probability of an event.* $P(S)=\sum_{a\in S}P(a)$. It satisfies $P(S)\ge 0$ and $P(\Omega\setminus S)=1-P(S)$.
--   2. *Light rescaling.* If $P(L\cap S)>0$, the law $P^{L,S}$ on $\Omega$ is
--   $$
--   P^{L,S}(a)=\mathbf 1[a\in L\cap S]\;P(a)\,\frac{P(L)}{P(L\cap S)}+\mathbf 1[a\notin L]\;P(a),
--   $$
--   and if $P(L\cap S)=0$ one sets $P^{L,S}=P$.
--
--   In words, the mass $P(L)$ that $P$ assigns to the "light" event $L$ is redistributed proportionally onto $L\cap S$. Outcomes in $L\setminus S$ get mass $0$, and the mass outside $L$ is unchanged, so the total is $P(L)+P(\Omega\setminus L)=1$. On an outcome $a\in L\cap S$ with $P(a)>0$, the probability is multiplied by $P(L)/P(L\cap S)\ge 1$. The surprisal $-\log P(a)$ therefore drops by $-\log\big(P(L\cap S)/P(L)\big)\ge 0$. When used as a modified predictor, this rescaling turns the knowledge that the true value lies in $S$ into a quantitative decrease of conditional entropy.
--
--   **Formalization Note** Events are predicates `α → Prop`. The definitions are `Law.prob` and `Law.lightRescale`, and the module also proves the basic lemmas `Law.prob_nonneg` and `Law.prob_not`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/LightRescaling.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/LightRescaling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def prob (P : Law α) (S : α → Prop) : ℝ :=
  ∑ a, if S a then P.mass a else 0

lemma prob_nonneg (P : Law α) (S : α → Prop) : 0 ≤ P.prob S := by
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp_all [P.nonneg]

lemma prob_not (P : Law α) (S : α → Prop) : P.prob (fun a => ¬S a) = 1 - P.prob S := by
  have h : P.prob (fun a => ¬S a) + P.prob S = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← P.total]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : S a <;> simp [ha]
  linarith

noncomputable def lightRescale (P : Law α) (L S : α → Prop) : Law α :=
  if h : 0 < P.prob (fun a => L a ∧ S a) then {
    mass := fun a => (if L a ∧ S a then P.mass a else 0) *
      (P.prob L / P.prob (fun b => L b ∧ S b)) + (if ¬L a then P.mass a else 0)
    nonneg := fun a => add_nonneg
      (mul_nonneg (by split_ifs <;> simp_all [P.nonneg])
        (div_nonneg (P.prob_nonneg L) h.le))
      (by split_ifs <;> simp_all [P.nonneg])
    total := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have ha : (∑ a, if L a ∧ S a then P.mass a else 0) = P.prob (fun a => L a ∧ S a) := by
        unfold prob
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : L a ∧ S a <;> simp [ha]
      have hb : (∑ a, if ¬L a then P.mass a else 0) = P.prob (fun a => ¬L a) := by
        unfold prob
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : L a <;> simp [ha]
      rw [ha, hb, P.prob_not L]
      field_simp
      ring
  } else P

end Law
end ThorpCompatibility

end OAI


