-- Prove2me | Definitions.Def_CompDesign_Supplement_budgetSharePay
-- name    : CompDesign_Supplement_budgetSharePay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:49:44.953817+00:00
-- url     : https://prove2.me/theorems/89513830-b839-43ad-9e0a-1b18400cf2cb
-- title:
--   Budget-share payment rules and $\gamma$-marginal covering
-- statement:
--   A **budget-share payment rule** assigns nonnegative shares $y_i(S)$ to the selected agents with $\sum_{i\in S}y_i(S)\le1$ for every $S$, and pays $p_i(S)=B\,y_i(S)$ for $i\in S$ and $0$ for $i\notin S$. For $\gamma\in(0,1]$ it is **$\gamma$-marginal-covering** if for every $S$ with $v(S)>0$ and every $i\in S$,
--   $$y_i(S)\ \ge\ \gamma\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}.$$
--   The marginal-contribution rule (8) and the Shapley rule (7) are 1-marginal-covering; these rules are the subject of Theorems 5.6 and B.1.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Definitions 3.3–3.4, p.14 (PDF 17)

import Mathlib

namespace CompDesign.Supplement

/-- The payments of a budget-share rule with shares `y` (Definition 3.3, p.14, PDF 17, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)):
`p_i(S) = B y_i(S)` for `i ∈ S`, and `0` for `i ∉ S`. -/
def budgetSharePay {n : ℕ} (B : ℝ) (y : Finset (Fin n) → Fin n → ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ :=
  if i ∈ S then B * y S i else 0

/-- The shares of a budget-share payment rule (Definition 3.3, p.14, PDF 17, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)): nonnegative
shares `y_i(S)` for the selected agents with `∑_{i∈S} y_i(S) ≤ 1` for every `S`. -/
def IsBudgetShare {n : ℕ} (y : Finset (Fin n) → Fin n → ℝ) : Prop :=
  (∀ S, ∀ i ∈ S, 0 ≤ y S i) ∧ ∀ S, ∑ i ∈ S, y S i ≤ 1

/-- `γ`-marginal covering (Definition 3.4, p.14, PDF 17, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)): for every `S` with `v(S) > 0`
and every `i ∈ S`, `y_i(S) ≥ γ (v(S) − v(S ∖ {i}))/v(S)`. -/
def IsMarginalCovering {n : ℕ} (γ : ℝ) (v : Finset (Fin n) → ℝ)
    (y : Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ S, 0 < v S → ∀ i ∈ S, γ * (v S - v (S.erase i)) / v S ≤ y S i

end CompDesign.Supplement


