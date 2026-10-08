-- Prove2me | Definitions.Def_BartlettNN_Sigmoid_Fat
-- name    : BartlettNN_Sigmoid_Fat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:15:27.828+00:00
-- url     : https://prove2.me/theorems/6de4df6d-1004-4b61-9da4-4a243bf57e49
-- title:
--   The pseudodimension dim_P(F) = lim_{γ→0} fat_F(γ) (p. 533)
-- statement:
--   Let $F$ be a class of real-valued functions and $\operatorname{fat}_F(\gamma)$ its fat-shattering dimension (p. 526). The paper recalls (p. 533) that the pseudodimension of $F$ can be defined as
--
--   $$\operatorname{dim}_P(F)=\lim_{\gamma\to0}\operatorname{fat}_F(\gamma).$$
--
--   Since $\operatorname{fat}_F$ is nonincreasing in $\gamma$, this limit as $\gamma$ decreases to $0$ equals $\sup_{\gamma>0}\operatorname{fat}_F(\gamma)$, which is the form used here. It bounds $\operatorname{fat}_F(\gamma)$ at every positive scale and enters Lemma 23.
--
--   **Formalization Note.** The value lies in $\mathbb N\cup\{\infty\}$, so an unbounded fat-shattering dimension gives $\infty$, not $0$. This is the paper's limit-of-fat definition, not the threshold-witness pseudodimension.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), pp. 526, 533, Section II and paragraph before Lemma 23; https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_Sigmoid_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering

namespace BartlettNN.Sigmoid

/-- The paper's `dim_P(F) = lim_{γ→0+} fat_F(γ)`, expressed as the supremum over positive scales. -/
noncomputable def pdim {X : Type*} (F : Set (X → ℝ)) : ℕ∞ :=
  ⨆ (γ : ℝ) (_ : 0 < γ), BartlettNN.Margin.fat F γ

end BartlettNN.Sigmoid


