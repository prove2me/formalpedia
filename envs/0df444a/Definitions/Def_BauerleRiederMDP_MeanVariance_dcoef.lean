-- Prove2me | Definitions.Def_BauerleRiederMDP_MeanVariance_dcoef
-- name    : BauerleRiederMDP_MeanVariance_dcoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:54.143931+00:00
-- url     : https://prove2.me/theorems/6b201d96-1e5d-4a47-bd5d-701928869a9d
-- title:
--   The coefficients $d_n$ of Eq. (4.34)
-- statement:
--   Consider the $N$-period market of §4.6 with $d$ risky assets whose relative risks $R_1,\dots,R_N\in\mathbb R^d$ are independent, and put
--
--   $$C_n:=\mathbb E\big[R_nR_n^{\top}\big],\qquad \ell_n:=\big(\mathbb E[R_n]\big)^{\top}C_n^{-1}\,\mathbb E[R_n],\qquad n=1,\dots,N.$$
--
--   The numbers $d_0,\dots,d_N$ are defined backwards by
--
--   $$d_N:=1,\qquad d_n:=d_{n+1}\,(1-\ell_{n+1}),\quad n=N-1,\dots,0,$$
--
--   equivalently $d_n=\prod_{k=n+1}^{N}(1-\ell_k)$.
--
--   They are the coefficients of the quadratic value functions of the auxiliary problem $QP(b)$ and determine the slope of the multiperiod efficient frontier; under Assumption (FM) each $\ell_k$ lies in $(0,1)$, so $0<d_n<1$ for $n<N$ (Lemma 4.6.4).
--
--   **Formalization Note** The recursion is written in its closed product form over $k\in\{n+1,\dots,N\}$, which gives $d_N=1$ and $d_n=d_{n+1}(1-\ell_{n+1})$ for every $n<N$; $C_n$ and $\ell_n$ are the platform's `MVMarket.Cmat` and `MVMarket.ell`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.34), p.121 (PDF p.135)

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.MeanVariance

open MDPFinance.MeanVariance

/-- The numbers `d_n` of Eq. (4.34) (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), eq. (4.34), p.121, PDF p.135): with
`C_n := 𝔼[R_n R_nᵀ]` and `ℓ_n := (𝔼[R_n])ᵀ C_n⁻¹ 𝔼[R_n]` (the platform's `MVMarket.Cmat`,
`MVMarket.ell`), the book defines `d_N := 1` and `d_n := d_{n+1}(1 - ℓ_{n+1})` for
`n = N-1, …, 0`.

**Formalization Note.** The backward recursion is written in its closed form
`d_n = ∏_{k=n+1}^{N} (1 - ℓ_k)`, a product over `Finset.Ioc n N`; it gives `d_N = 1` (empty
product) and `d_n = d_{n+1}(1 - ℓ_{n+1})` for every `n < N`, so it agrees with (4.34) at every
index `0 ≤ n ≤ N` the book uses. For `n > N` the value is `1` and is never used. -/
noncomputable def dcoef {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (n : ℕ) :
    ℝ :=
  ∏ k ∈ Finset.Ioc n M.N, (1 - M.ell k)

end BauerleRiederMDP.MeanVariance


