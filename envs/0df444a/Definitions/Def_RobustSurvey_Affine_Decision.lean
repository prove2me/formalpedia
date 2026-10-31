-- Prove2me | Definitions.Def_RobustSurvey_Affine_Decision
-- name    : RobustSurvey_Affine_Decision
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:01:24.251053+00:00
-- url     : https://prove2.me/theorems/7644fbee-b1c5-4201-aa01-c9d128e7885b
-- title:
--   Full first-stage and affine-policy coefficient tuple
-- statement:
--   A decision is the entire tuple $\chi=(x_1,q,Q)$, where $x_1\in\mathbb R^{n_1}$, $q\in\mathbb R^{n_2}$, and $Q\in\mathbb R^{n_2\times L}$. All these coefficients are chosen before uncertainty is observed. Its second-stage policy is
--   $$x_2(u)=Qu+q=q^{(0)}+\sum_{l=1}^L u_lq^{(l)},$$
--   where $q^{(0)}=q$ and $q^{(l)}$ is column $l$ of $Q$. Evaluation reuses the published unrestricted affine-policy function in `BudgetedAffine_NetworkGap_LotSizing`. None of that module's separate lot-sizing feasibility conditions are part of this decision or its policy. There are no sign or integrality restrictions.
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; §4.3.1, printed pp. 23–25 / PDF pp. 24–26.

import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing

namespace RobustSurvey.Affine

/-- The entire decision tuple, fixed before uncertainty is revealed. -/
structure Decision (n₁ n₂ L : ℕ) where
  x : Fin n₁ → ℝ
  q : Fin n₂ → ℝ
  Q : Matrix (Fin n₂) (Fin L) ℝ

/-- Reuse the published unrestricted affine rule Q u + q. -/
noncomputable def Decision.policy {n₁ n₂ L : ℕ} (χ : Decision n₁ n₂ L)
    (u : Fin L → ℝ) : Fin n₂ → ℝ :=
  BudgetedAffine.NetworkGap.LotSizing.affinePolicy χ.Q χ.q u

end RobustSurvey.Affine


