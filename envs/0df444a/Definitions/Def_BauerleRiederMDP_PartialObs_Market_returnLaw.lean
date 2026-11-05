-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Market_returnLaw
-- name    : BauerleRiederMDP_PartialObs_Market_returnLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:22.423228+00:00
-- url     : https://prove2.me/theorems/2a39a516-b1c1-4ec4-9141-9474da63356d
-- title:
--   Law of the observed returns $(R_1,\dots,R_n)$
-- statement:
--   The law of the return path $(R_1,\dots,R_n)$ in the market of Chapter 6 when the hidden state starts from $Y_0\sim\rho$: the marginal on the returns of the joint law of $\big((R_1,\dots,R_n),Y_n\big)$. The market of the book is the case $\rho=Q_0$. The investor observes only these returns: the filtration of the portfolio problems is $\mathcal F_n=\mathcal F^S_n=\sigma(R_1,\dots,R_n)$.
-- source:
--   Bäuerle & Rieder (2011), eq. (6.1), p.175 (PDF 188); §6.1, p.176 (PDF 189)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_jointLaw

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The law of the observed return path `(R_1, …, R_n)`** when `Y_0 ~ ρ`.
Bäuerle & Rieder (2011), eq. (6.1), p.175 (PDF 188), and the probability measure `IP^π_x` of
p.150 (PDF 163) built from the prior `Q_0` and the transition law: the marginal of
`M.jointLaw ρ n` on the returns. The book's market is `M.returnLaw M.Q0`; the investor observes
only these returns (`F_n = F^S_n = σ(R_1, …, R_n)`, p.176). -/
noncomputable def Market.returnLaw {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (ρ : ProbabilityMeasure EY) (n : ℕ) : Measure (Fin n → Fin d → ℝ) :=
  (M.jointLaw ρ n).map Prod.fst

end BauerleRiederMDP.PartialObs


