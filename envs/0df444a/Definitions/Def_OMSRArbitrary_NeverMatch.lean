-- Prove2me | Definitions.Def_OMSRArbitrary_NeverMatch
-- name    : OMSRArbitrary_NeverMatch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:23.635633+00:00
-- url     : https://prove2.me/theorems/a616722c-029f-439f-b98e-12226a3047f0
-- title:
--   The never-match probabilities $Q_t(A)$ and the ratios $\kappa_j$
-- statement:
--   Fix $i$ and the seeds $u$. For an arrival $t$ and a set $A$ of resources, $Q_t(A)$ is the probability, over $z_{\ge t}$, that the run of PG that starts at arrival $t$ with available set $A$ never matches $i$; $Q_t(A):=0$ if $i\notin A$, and $Q_{T+1}(A)=\mathbf 1\{i\in A\}$. In particular $Q_1(U)=\Pr[\mathrm{PG}(u)\text{ never matches }i]$. Further
--   $$\kappa_j=\frac{r_j(1-g(u_j))}{r_i(1-g(u_i))}\quad(j\ne i),\qquad \kappa_i:=1.$$
--
--   **Formalization Note** Arrivals are 0-based: the paper's $Q_1$ is `neverMatchProb … 0`, and $Q_{T+1}$ is `neverMatchProb … m`, where the run probes nothing. The probability is an integral over all thresholds $z\sim$ `seedLaw m`; the run from $(A,t)$ reads only $z_{\ge t}$.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §4.3, p.21 (κ_j); §5 (Notation), p.23 (κ_i := 1); §5.2 (Additional Notation), p.25 (Q_t(A))

import Mathlib
import Definitions.Def_OMSRArbitrary_PerturbedGreedy

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw)
noncomputable section

namespace OMSRArbitrary

variable {n m : ℕ}

open Classical in
/-- **`Q_t(A)`** (arXiv:2611.03598, §5.2, p.25), seeds `u` fixed: the probability, over the
thresholds, that the run of PG that starts at arrival `t` with available set `A` never matches
`i`; `Q_t(A) := 0` if `i ∉ A`, and `Q_{T+1}(A) = 1{i ∈ A}`.

**Formalization Note.** Arrivals are 0-based, so the paper's `Q_1(U)` is `neverMatchProb … 0 univ`
and the base case `Q_{T+1}` is `t = m`, where the run probes nothing and the integral is `1`.
The run from `(A, t)` reads only `z_{≥t}`, so integrating over all of `z ∼ seedLaw m` is the
probability over `z_{≥t}`. The override `0` for `i ∉ A` is the paper's (the run-based
probability would be `1` there). -/
def neverMatchProb (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (t : ℕ)
    (A : Finset (Fin n)) : ℝ :=
  if i ∈ A then
    ∫ z, (if pgMatches D g u A t (corrOutcome D z) i then (0 : ℝ) else 1) ∂seedLaw m
  else 0

/-- `κ_j := r_j(1 − g(u_j))/(r_i(1 − g(u_i)))` for `j ≠ i`, and `κ_i := 1`
(arXiv:2611.03598, §4.3, p.21; §5, p.23). -/
def kappa (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i j : Fin n) : ℝ :=
  if j = i then 1 else D.reward j * (1 - g (u j)) / (D.reward i * (1 - g (u i)))

end OMSRArbitrary


