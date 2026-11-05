-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
-- name    : BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:56.430374+00:00
-- url     : https://prove2.me/theorems/f3c2985d-1ab7-4fed-9f35-41fa8e9815e1
-- title:
--   No arbitrage in a one-period market: $\varphi\cdot R\ge0$ a.s. $\Rightarrow\varphi\cdot R=0$ a.s.
-- statement:
--   Let $R\in\mathbb R^d$ be the relative risk of $d$ risky assets over one period, with law $\mu$. The market has **no arbitrage opportunities** if for every portfolio $\varphi\in\mathbb R^d$
--
--   $$
--   \varphi\cdot R\ge 0\ \ \mathbb P\text{-a.s.}\quad\Longrightarrow\quad \varphi\cdot R=0\ \ \mathbb P\text{-a.s.}
--   $$
--
--   Equivalently, no $\varphi$ has $\varphi\cdot R\ge0$ a.s. and $\mathbb P(\varphi\cdot R>0)>0$. This is Assumption (FM)(i) of §4.4 for each environment state $j$ (with $R=R(j)$), and, by Theorem 3.1.5, the absence of arbitrage in the one-period market and in a multiperiod market with independent relative risks (applied to each $R_n$).
--
--   **Formalization Note** The condition depends on $R$ only through its law $\mu$ on $\mathbb R^d$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Assumption (FM)(i), p.101 (PDF p.115); Theorem 3.1.5, p.64 (PDF p.78)

import Mathlib
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- **No arbitrage in a one-period market** with relative risk `R ∈ ℝ^d` of law `μ`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Assumption (FM)(i), p.101, PDF p.115: "for all `φ ∈ ℝ^d` it holds:
`φ · R(j) ≥ 0` ℙ-a.s. ⇒ `φ · R(j) = 0` ℙ-a.s."; equivalently, by Theorem 3.1.5, p.64, no
portfolio `φ` has `φ · R ≥ 0` a.s. and `ℙ(φ · R > 0) > 0`).

**Formalization Note.** The condition depends on `R` only through its law `μ` on `ℝ^d`
(`Fin d → ℝ`), and `φ · z` is written `∑ k, φ k * z k`. For the multiperiod market of §4.3 with
independent relative risks `R_1, …, R_N` and `F_n = F^S_n`, no arbitrage is equivalent to this
condition for the law of every `R_n` (Theorem 3.1.5, local form). -/
def NoArbitrageLaw {d : ℕ} (μ : Measure (Fin d → ℝ)) : Prop :=
  ∀ φ : Fin d → ℝ, (∀ᵐ z ∂μ, 0 ≤ ∑ k, φ k * z k) → ∀ᵐ z ∂μ, ∑ k, φ k * z k = 0

end BauerleRiederMDP.RegimeSwitching


