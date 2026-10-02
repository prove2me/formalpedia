-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary
-- name    : MDPFinance_MeanVariance_MVAuxiliary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:06:57.763483+00:00
-- url     : https://prove2.me/theorems/05fe4616-4b0b-4c0f-855b-b19462c57dfa
-- title:
--   The one-period return moments $C_n$, $\mathbb{E}[R_n]$ and $\ell_n$ of Equation (4.34)
-- statement:
--   For the vector of relative risky returns $R_n\in\mathbb{R}^d$: the second-moment
--   matrix $C_n := \mathbb{E}[R_nR_n^\top]$ (`Cmat`), the mean vector $\mathbb{E}[R_n]$ (`Evec`),
--   and the scalar
--   $$\ell_n := \mathbb{E}[R_n]^\top C_n^{-1}\,\mathbb{E}[R_n]$$
--   (`ell`), all from Bäuerle–Rieder's Eq. (4.34). Under the market's non-degeneracy assumption
--   (FM) — $C_n$ positive definite — $\ell_n\in(0,1)$ is exactly what Lemma 4.6.4 needs to keep the
--   recursively-defined sequence $d_n := d_{n+1}(1-\ell_{n+1})$, $d_N:=1$, inside $(0,1)$.
--
--   **Formalization Note.** `Cmat n` is inverted with Mathlib's general (junk-valued-when-singular)
--   matrix inverse; every theorem that uses `(M.Cmat n)⁻¹` carries the positive-definiteness hypothesis
--   that makes the inverse the genuine one, matching how the book's own Assumption (FM)(ii) is stated
--   as a standing hypothesis of the section rather than re-derived per theorem.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 121, PDF 135, Equation (4.34)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `C_n := 𝔼[R_n R_n^⊤]` (Bäuerle–Rieder, Eq. (4.34), p. 121, PDF 135). -/
noncomputable def MVMarket.Cmat (M : MVMarket Ω d) (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => ∫ ω, M.R n ω j * M.R n ω k ∂M.measIP

/-- `𝔼[R_n] ∈ ℝ^d`. -/
noncomputable def MVMarket.Evec (M : MVMarket Ω d) (n : ℕ) : Fin d → ℝ :=
  fun j => ∫ ω, M.R n ω j ∂M.measIP

/-- `ℓ_n := 𝔼[R_n]^⊤ C_n^{-1} 𝔼[R_n]` (Bäuerle–Rieder, Eq. (4.34), p. 121, PDF 135). -/
noncomputable def MVMarket.ell (M : MVMarket Ω d) (n : ℕ) : ℝ :=
  dotProduct (M.Evec n) ((M.Cmat n)⁻¹.mulVec (M.Evec n))

end MDPFinance.MeanVariance


