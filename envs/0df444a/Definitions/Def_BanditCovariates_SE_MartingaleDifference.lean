-- Prove2me | Definitions.Def_BanditCovariates_SE_MartingaleDifference
-- name    : BanditCovariates_SE_MartingaleDifference
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:48.975288+00:00
-- url     : https://prove2.me/theorems/f0cffc0f-1a0d-4af5-acb0-77ba74dcaefc
-- title:
--   Appendix p. 28 — martingale difference sequences
-- statement:
--   For a probability measure $P$ and a filtration $(\mathcal F_n)_{n\ge0}$, a real sequence $(Z_{n+1})_{n\ge0}$ is a martingale difference sequence here when each term is measurable, integrable, and adapted, its first term has mean zero, and
--
--   $$\mathbb E_P[Z_{n+2}\mid\mathcal F_n]=0\quad(n\ge0).$$
--
--   This is the stochastic object used in the appendix concentration bounds. The indexing starts at zero in Lean: `Z 0` denotes the paper's $Z_1$.
--
--   **Formalization Note** The paper's displayed definition omits $\mathbb E Z_1=0$; the appendix's first-round claims require it. The conditioning filtration may contain more information than the natural filtration of $Z$.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 28, Appendix, martingale difference sequence and Lemma A.1

import Mathlib

namespace BanditCovariates.SE

open MeasureTheory

/-- A martingale difference sequence, with the first variable centered as required by
the appendix's concentration bounds. `Z n` is the paper's `Z_(n+1)`. -/
structure MartingaleDifference {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) (ℱ : Filtration ℕ m) (Z : ℕ → Ω → ℝ) : Prop where
  measurable : ∀ n, Measurable (Z n)
  integrable : ∀ n, Integrable (Z n) P
  adapted : ∀ n, StronglyMeasurable[ℱ n] (Z n)
  initial_mean : ∫ ω, Z 0 ω ∂P = 0
  next_mean : ∀ n, P[Z (n + 1) | ℱ n] =ᵐ[P] 0

end BanditCovariates.SE


