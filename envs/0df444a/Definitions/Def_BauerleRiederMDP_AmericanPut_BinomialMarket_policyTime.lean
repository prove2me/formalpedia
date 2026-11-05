-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_policyTime
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_policyTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:47.341604+00:00
-- url     : https://prove2.me/theorems/8e385668-e09a-4532-ad66-2257e13905e1
-- title:
--   Exercise time $\tau_\pi=\inf\{n\mid X_n\in A_n\}$ of a Markov exercise policy
-- statement:
--   For a Markov exercise policy $\pi=(f_0,f_1,\dots)$ with $f_n=1_{A_n}$, the exercise time is
--   $$\tau_\pi:=\inf\{n\in\mathbb N_0\mid X_n\in A_n\},\qquad \inf\emptyset=\infty.$$
--   For the stationary rule $A_n=E^*$ this is the time $\tau^*:=\inf\{n\in\mathbb N_0\mid X_n\in E^*\}$ of Theorem 11.1.3 d).
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §10.1, p.305, PDF 313 ($\tau_\pi$) and Theorem 11.1.3 d), p.337, PDF 345

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_stock

namespace BauerleRiederMDP.AmericanPut

/-- The **exercise time of a Markov exercise policy** `π = (f_0, f_1, …)`, `f_n = 1_{A_n}`: the first time
`n ∈ ℕ₀` at which `f_n(X_n) = 1`, i.e. `X_n = S_n ∈ A_n`, with `inf ∅ = ∞` (Bäuerle & Rieder, Markov
Decision Processes with Applications to Finance (2011), §10.1 (stopping problems as Markov Decision Models) and
Theorem 11.1.3 d), p.337, PDF 345: for the stationary rule `A_n = E*` this is
`τ* := inf{n ∈ ℕ₀ | X_n ∈ E*}`).

**Formalization Note.** Values in `ℕ∞` (`sInf ∅ = ⊤`, never exercised). The stock starts at `S_0 = x`. -/
noncomputable def BinomialMarket.policyTime (M : BinomialMarket) (x : ℝ) (A : ℕ → Set ℝ)
    (ω : ℕ → Bool) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | M.stock x k ω ∈ A k})

end BauerleRiederMDP.AmericanPut


