-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_IsStrategy
-- name    : BauerleRiederMDP_LQ_Supplement_CIRandom_IsStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:04:52.667307+00:00
-- url     : https://prove2.me/theorems/916b9371-4c6e-486b-90f6-15ae1b8ab806
-- title:
--   An admissible consumption-investment strategy for problem (9.1)
-- statement:
--   **An admissible consumption-investment strategy for problem (9.1)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.1, p.268, PDF 278): $(c_n, \varphi _n)$ is $(F_n)$-adapted with $0 \le  c_n \le  X_n$ for all $n$, and $X^{c,\varphi }_\tau  \in  dom U_p = [0, \infty )$ $\mathbb P $-a.s.
--
--   **Formalization Note.** Adaptedness is measurability of $c n$, $\varphi  n$ as functions of $(R_1, \dots , R_n)$, whose joint law is the product $\mu R^{\otimes n}$ (i.i.d.). The inequalities hold almost surely. Since $\tau $ is independent of the market and $\mathbb P (\tau  = n) > 0$ for every $n \ge  1$, $X_\tau  \ge  0$ a.s. is $X_n \ge  0$ a.s. for every $n \ge  1$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.1, p.268, PDF 278

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_wealth

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **An admissible consumption-investment strategy for problem (9.1)** (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), §9.1, p.268, PDF 278): `(c_n, φ_n)` is
`(F_n)`-adapted with `0 ≤ c_n ≤ X_n` for all `n`, and `X^{c,φ}_τ ∈ dom U_p = [0, ∞)` `ℙ`-a.s.

**Formalization Note.** Adaptedness is measurability of `c n`, `φ n` as functions of
`(R_1, …, R_n)`, whose joint law is the product `μR^{⊗n}` (i.i.d.). The inequalities hold almost
surely. Since `τ` is independent of the market and `ℙ(τ = n) > 0` for every `n ≥ 1`,
`X_τ ≥ 0` a.s. is `X_n ≥ 0` a.s. for every `n ≥ 1`. -/
def CIRandom.IsStrategy {d : ℕ} (C : CIRandom d) (x : ℝ) (c : (n : ℕ) → (Fin n → Fin d → ℝ) → ℝ)
    (φ : (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ) : Prop :=
  (∀ n, Measurable (c n) ∧ Measurable (φ n)) ∧
  (∀ n, ∀ᵐ r ∂(Measure.pi fun _ : Fin n => C.μR),
    0 ≤ c n r ∧ c n r ≤ CIRandom.wealth c φ x n r) ∧
  ∀ n, ∀ᵐ r ∂(Measure.pi fun _ : Fin (n + 1) => C.μR), 0 ≤ CIRandom.wealth c φ x (n + 1) r

end BauerleRiederMDP.LQ.Supplement


