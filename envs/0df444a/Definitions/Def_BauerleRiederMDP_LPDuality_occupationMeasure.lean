-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_occupationMeasure
-- name    : BauerleRiederMDP_LPDuality_occupationMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:49.147205+00:00
-- url     : https://prove2.me/theorems/e5e89acb-ad5b-40df-97f7-4e51f6f41fba
-- title:
--   Discounted occupation measure $\mu_\pi$ of a Markov policy
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a stationary Markov Decision Model, $p$ the initial distribution and $\pi=(f_k)\in F^\infty$ a Markov policy, with actions $A_k=f_k(X_k)$. The **discounted occupation measure** of $\pi$ is the measure on $D$
--   $$
--   \mu_\pi(B):=\mathbb E^\pi_p\Big[\sum_{k=0}^\infty \beta^k 1_B(X_k,A_k)\Big]=\sum_{k=0}^\infty \beta^k\,\mathbb P^\pi_p\big((X_k,A_k)\in B\big).
--   $$
--
--   Occupation measures are the feasible points of the dual linear program (D) of a contracting Markov Decision Problem; the occupation measure of an optimal stationary policy solves (D).
--
--   **Formalization Note** $\mu_\pi$ is the countable sum over $k$ of $\beta^k$ times the image of the law $p_k$ of $X_k$ (`stateLaw`) under $x\mapsto(x,f_k(x))$. It is a measure on $E\times A$; for a policy it is carried by $D$, which is how measures on $D$ are represented throughout the mission.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.2, p.215 (PDF 226), definition of μ_π

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_BauerleRiederMDP_LPDuality_stateLaw

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- The **discounted occupation measure** of a Markov policy `π = (f_k) ∈ F^∞` from the initial
distribution `p` (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), §7.5.2, p.215, PDF 226):
`μ_π(B) := 𝔼^π_p[∑_{k=0}^∞ β^k 1_B(X_k, A_k)] = ∑_{k=0}^∞ β^k ℙ^π_p((X_k, A_k) ∈ B)`,
where `A_k = f_k(X_k)`.

**Formalization Note** `μ_π` is the countable sum over `k` of `β^k` times the image of the law
`p_k` of `X_k` (`stateLaw`) under `x ↦ (x, f_k(x))`. It is a measure on `E × A`; for a policy it is
concentrated on `D` because every `f_k(x) ∈ D(x)`, so it is the book's measure on `D`. -/
noncomputable def occupationMeasure {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (π : ℕ → E → A) (p : Measure E) : Measure (E × A) :=
  Measure.sum fun k => ENNReal.ofReal (M.β ^ k) • (stateLaw M π p k).map fun x => (x, π k x)

end BauerleRiederMDP.LPDuality


