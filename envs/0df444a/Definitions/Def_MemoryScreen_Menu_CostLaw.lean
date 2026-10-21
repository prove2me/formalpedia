-- Prove2me | Definitions.Def_MemoryScreen_Menu_CostLaw
-- name    : MemoryScreen_Menu_CostLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:40:35.215294+00:00
-- url     : https://prove2.me/theorems/20587df3-1d80-49c3-837c-d5428ee35d84
-- title:
--   Transaction-cost distribution, §2, p. 7 (PDF 8)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be a continuous nonnegative probability density with finite first moment. Its cumulative distribution is
--
--   $$F(x)=\int_{-\infty}^{x}f(b)\,db.$$
--
--   This is the transaction-cost distribution used throughout the screening model. The first-moment condition ensures the buyer's and seller's payoff integrals are finite.
--
--   **Formalization Note.** The paper permits an unbounded support and presupposes finite payoff integrals; the explicit finite-first-moment assumption supplies that condition. The CDF is derived from the density, not independent data.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), p. 7 (PDF 8), §2, distribution of transaction cost

import Mathlib

open MeasureTheory

namespace MemoryScreen.Menu

/-- A real-valued transaction cost represented by its density. -/
structure CostLaw where
  f : ℝ → ℝ

/-- A continuous probability density with finite first moment. -/
def CostLaw.Valid (D : CostLaw) : Prop :=
  Continuous D.f ∧ (∀ b : ℝ, 0 ≤ D.f b) ∧ Integrable D.f ∧
    (∫ b : ℝ, D.f b) = 1 ∧ Integrable (fun b : ℝ => b * D.f b)

/-- The cumulative distribution function determined by the density. -/
noncomputable def CostLaw.cdf (D : CostLaw) (x : ℝ) : ℝ :=
  ∫ b in Set.Iic x, D.f b

end MemoryScreen.Menu


