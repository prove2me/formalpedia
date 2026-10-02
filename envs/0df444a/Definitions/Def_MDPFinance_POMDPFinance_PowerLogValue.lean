-- Prove2me | Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue
-- name    : MDPFinance_POMDPFinance_PowerLogValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:34:34.165294+00:00
-- url     : https://prove2.me/theorems/93364a38-9261-4d0b-85c2-2de27428c38a
-- title:
--   Closed-form auxiliary recursions for power and logarithmic utility under partial observation
-- statement:
--   For the power utility $U(x) = x^\gamma/\gamma$ ($0 < \gamma < 1$) and the logarithmic utility
--   $U(x) = \log(x)$, Theorems 6.1.2 and 6.1.7 show that the terminal-wealth value function factors
--   through a belief-only auxiliary function $d_k(\rho)$, avoiding the need to solve the full
--   $(x,\rho)$-Bellman equation directly.
--
--   For the power case, with admissible fractions $\tilde A := \{\alpha \in \mathbb R^d \mid 1+
--   \alpha\cdot R(y) \ge 0 \text{ a.s.}\}$ (independent of $y$ under Assumption FM(ii)), the
--   recursion (6.3) is, in stages-remaining form,
--   $$
--   d_0 \equiv \frac1\gamma, \qquad
--   d_{k+1}(\rho) = \sup_{\alpha \in \tilde A} \int d_k(\Phi(\rho,z))\,(1+\alpha\cdot z)^\gamma\,
--   d(\text{predictive}(\rho))(z).
--   $$
--   For the logarithmic case, with the strict admissible set $\tilde A := \{\alpha \mid 1+\alpha\cdot
--   R(y) > 0 \text{ a.s.}\}$, recursion (6.6) is
--   $$
--   d_0 \equiv 0, \qquad
--   d_{k+1}(\rho) = \log(1+i) + \sup_{\alpha \in \tilde A} \int \Big[\log(1+\alpha\cdot z) +
--   d_k(\Phi(\rho,z))\Big]\, d(\text{predictive}(\rho))(z).
--   $$
--   Both recursions are indexed by stages-remaining $k$, matching the book's own $d_n$ read backward
--   from the terminal condition.
--
--   **Formalization Note.** `AtildePow`'s inequality is non-strict ($\ge 0$) and `AtildeLog`'s is
--   strict ($>0$), exactly as the book distinguishes the two utilities' no-ruin conditions (power
--   utility tolerates $X_N=0$, logarithmic utility does not, since $\log 0 = -\infty$).
--
--   **Moderation note.** The logarithmic recursion (6.6) is in $[-\infty,\infty]$ and in the book's own form (the supremum over $\alpha$ of $\int\log(1+\alpha\cdot z)$ plus the separate continuation integral): $\mathbb E\log(1+\alpha\cdot R)$ can be $-\infty$ for an admissible $\alpha$, and a real Bochner integral recorded it as $0$, which changes the set of maximizers whenever the optimal value is $0$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 178/181, Eq. (6.3) and (6.6)

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

variable {EY : Type*} [MeasurableSpace EY] {d : ℕ}

/-- `\tilde A := \{α \in ℝ^d \mid 1+α\cdot R(y) \ge 0 \text{ a.s.}\}` for the power-utility case
(Bäuerle–Rieder, p. 178, PDF 191), independent of `y` by Assumption `FM`(ii); quantified over all
`y` for the same reason as `TerminalWealthMarket.D`. -/
def AtildePow (M : FilterMarket EY d) : Set (Fin d → ℝ) :=
  {a | ∀ y : EY, ∀ᵐ z ∂(M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)), 0 ≤ 1 + ∑ j, a j * z j}

/-- `\tilde A := \{α \mid 1+α\cdot R(y) > 0 \text{ a.s.}\}` for the logarithmic-utility case
(Bäuerle–Rieder, p. 181, PDF 195; the strict inequality, vs. `AtildePow`'s `≥`, is the book's own
distinction between the two utilities' admissible sets). -/
def AtildeLog (M : FilterMarket EY d) : Set (Fin d → ℝ) :=
  {a | ∀ y : EY, ∀ᵐ z ∂(M.lam.withDensity fun z => ENNReal.ofReal (M.qR y z)), 0 < 1 + ∑ j, a j * z j}

/-- The power-utility auxiliary recursion `(d_n)` of (6.3) (Bäuerle–Rieder, Theorem 6.1.2a, p.
178, PDF 191), indexed by stages-remaining `k` (`d_0 \equiv 1/γ`; `d_{k+1}(ρ) := \sup_{α \in
\tilde A} \int d_k(Φ(ρ,z))(1+α\cdot z)^γ \, d(\text{predictive }ρ)(z)`). -/
noncomputable def dPow (M : FilterMarket EY d) (Fd : FilterOp M) (γ : ℝ) :
    ℕ → Measure EY → ℝ
  | 0, _ => 1 / γ
  | (k + 1), ρ =>
      ⨆ a ∈ AtildePow M, ∫ z, dPow M Fd γ k (Fd.Phi ρ z) * (1 + ∑ j, a j * z j) ^ γ
        ∂(M.predictive ρ)

/-- The logarithmic-utility auxiliary recursion `(d_n)` of (6.6) (Bäuerle–Rieder, Theorem 6.1.7a,
p. 181, PDF 195), indexed by stages-remaining `k` (`d_0 \equiv 0`; `d_{k+1}(ρ) := \log(1+i) +
\sup_{α \in \tilde A} \int \log(1+α\cdot z) \, d(\text{predictive }ρ)(z) + \int d_k(Φ(ρ,z)) \,
d(\text{predictive }ρ)(z)`), in `[-∞,∞]`: `𝔼 \log(1+α\cdot R)` can be `-∞` for an admissible `α`,
and a real Bochner integral would record it as `0`. -/
noncomputable def dLog (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℝ) :
    ℕ → Measure EY → EReal
  | 0, _ => 0
  | (k + 1), ρ =>
      (Real.log (1 + i) : EReal) +
        (⨆ a ∈ AtildeLog M, erealIntegral (M.predictive ρ) fun z =>
          ((Real.log (1 + ∑ j, a j * z j) : ℝ) : EReal)) +
        erealIntegral (M.predictive ρ) fun z => dLog M Fd i k (Fd.Phi ρ z)

end MDPFinance.POMDPFinance


