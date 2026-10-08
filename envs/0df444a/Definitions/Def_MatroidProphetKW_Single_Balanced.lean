-- Prove2me | Definitions.Def_MatroidProphetKW_Single_Balanced
-- name    : MatroidProphetKW_Single_Balanced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:47.84141+00:00
-- url     : https://prove2.me/theorems/336583bd-a0b0-48e9-8b41-077ee0f61bbe
-- title:
--   Definition 1 — $\alpha$-balanced thresholds
-- statement:
--   Let $\mathcal M = (\mathcal U, \mathcal I)$ be a matroid, $F = (F_x)_{x \in \mathcal U}$ the weight distributions, and $w' \sim \bigotimes_x F_x$ the ghost sample with the sets $C(A)$, $R(A)$ of §3.2. For a parameter $\alpha > 0$, a threshold rule has **$\alpha$-balanced thresholds** if for every input sequence $\sigma$ (every input order and every non-negative weight vector), with $A = A(\sigma)$ the selected set, and every set $V$ disjoint from $A$ with $A \cup V \in \mathcal I$,
--   $$\sum_{x_i \in A} T_i(\sigma) \;\ge\; \frac1\alpha \cdot \mathbb E\big[w'(C(A))\big], \tag{2}$$
--   $$\sum_{x_i \in V} T_i(\sigma) \;\le\; \Big(1 - \frac1\alpha\Big) \cdot \mathbb E\big[w'(R(A))\big], \tag{3}$$
--   where the expectation is over the random choice of $w'$ only.
--
--   Condition (2) says the selected elements paid enough, compared with the part $C(A)$ of the optimum they displaced; condition (3) says that whatever could still have been added was offered thresholds that are not too high, compared with the part $R(A)$ the optimum could still add. Proposition 1 turns these two conditions into an approximation guarantee.
--
--   **Formalization Note** $T_i(\sigma)$ is the rule's threshold for $x_i$ evaluated at the prefix $x_1, \dots, x_{i-1}$ and at the selection $A_{i-1}$ the rule made on it. For $x_i \in A \cup V$ the set $A_{i-1} \cup \{x_i\}$ is independent, so these thresholds are finite. The expectations are Bochner integrals over $w' \sim \bigotimes_x F_x$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 6, Definition 1, (2)–(3)

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Online

namespace MatroidProphetKW.Single

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Definition 1 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 6): for `a > 0`, the threshold rule
`Thr` has `a`-balanced thresholds if for every input sequence `σ` (every input order `l` and every
non-negative weight vector `w`), with `A = A(σ)`, and every set `V` disjoint from `A` with
`A ∪ V ∈ ℐ`,
  `∑_{x_i ∈ A} T_i(σ) ≥ (1/a) · E[w′(C(A))]`          (2)
  `∑_{x_i ∈ V} T_i(σ) ≤ (1 − 1/a) · E[w′(R(A))]`      (3)
where the expectation is over `w′ ∼ Measure.pi F`. -/
def Balanced (M : Matroid α) (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ) (a : ℝ) : Prop :=
  ∀ l : List α, IsOrder l → ∀ w : α → ℝ, (∀ x, 0 ≤ w x) →
    ∀ V : Finset α, Disjoint V (run M Thr l w) → M.Indep (↑(run M Thr l w ∪ V) : Set α) →
      (1 / a) * ∫ w', wt w' (Cset M (run M Thr l w) w') ∂(Measure.pi F)
          ≤ ∑ x ∈ run M Thr l w, thrAt M Thr l w x ∧
        ∑ x ∈ V, thrAt M Thr l w x
          ≤ (1 - 1 / a) * ∫ w', wt w' (Rset M (run M Thr l w) w') ∂(Measure.pi F)

end MatroidProphetKW.Single


