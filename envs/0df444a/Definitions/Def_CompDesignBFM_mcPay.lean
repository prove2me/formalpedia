-- Prove2me | Definitions.Def_CompDesignBFM_mcPay
-- name    : CompDesignBFM_mcPay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:33.575606+00:00
-- url     : https://prove2.me/theorems/0f632ab8-3722-4fc6-9702-e25b6f04d2fe
-- title:
--   Marginal-contribution payment rule
-- statement:
--   For a proxy $F$, a budget $B$ and a participating set $S$,
--
--   $$p^F_i(S)=B\,\frac{F(S)-F(S\setminus\{i\})}{F(S)}\quad\text{for } i\in S \text{ with } F(S)>0,$$
--
--   and zero otherwise. Each agent is paid in proportion to their marginal contribution, and the rule does not depend on the costs.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, eq. (7), p.14 (PDF 16)

import Mathlib

namespace CompDesignBFM

/-- The marginal-contribution payment rule (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, eq. (7), p.14, PDF 16; eq. (2), p.6, PDF 8):
`B (F S - F (S ∖ {i})) / F S` for `i ∈ S` with `F S > 0`, and zero otherwise. -/
noncomputable def mcPay {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ S ∧ 0 < F S then B * (F S - F (S.erase i)) / F S else 0

end CompDesignBFM


