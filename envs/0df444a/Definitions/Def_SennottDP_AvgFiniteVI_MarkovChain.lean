-- Prove2me | Definitions.Def_SennottDP_AvgFiniteVI_MarkovChain
-- name    : SennottDP_AvgFiniteVI_MarkovChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T08:49:25.227748+00:00
-- url     : https://prove2.me/theorems/f8e1b982-ba17-4386-ad79-1b69a878e4fa
-- title:
--   Finite Markov chains - transient states, unichain chains, aperiodic positive recurrent classes
-- statement:
--   For a Markov chain with transition matrix $Q$ on a finite state space $S$, using the $t$-step transition probabilities $P^{(t)}_{ij}$, the first passage times $T_{ij} = \min\{t \ge 1 : X_t = j\}$, positive recurrence, communicating classes and the steady state probabilities $\pi_j = 1/m_{jj}$ of the shared module:
--
--   1. a state $i$ is **transient** if the chain started at $i$ returns to $i$ with probability less than one, $P(T_{ii} < \infty) < 1$;
--   2. the chain is **unichain** if it has a single positive recurrent class: some state $x$ is positive recurrent and every positive recurrent state lies in the communicating class of $x$;
--   3. a positive recurrent class $R$ is **aperiodic** if
--   $$\pi_j = \lim_{n\to\infty} P^{(n)}_{ij} \qquad \text{for all } i, j \in R.$$
--
--   These are the notions used by Assumption OPA, Lemma 6.6.2 and Proposition 6.5.1.
--
--   **Formalization Note** Transition probabilities and the limit in the aperiodicity condition are in `ℝ≥0∞`; passage times count at least one transition, as in the book.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 292–295, Appendix C.1 (transience p. 293, aperiodicity p. 295); p. 107 (unichain)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_MarkovChain

namespace SennottDP.AvgFiniteVI

open scoped ENNReal

/-! Markov chains on a finite state space (Sennott, Appendix C.1–C.3, pp. 292–302): the notions
this chapter adds to the shared module `SennottDP.AvgFinite` (`nStep`, `commClass`, `reachProb`,
`PositiveRecurrent`, `steadyState`, …). A chain is given by its transition matrix
`Q : S → S → ℝ≥0∞`; the results that use these definitions always supply a stochastic `Q`. -/

variable {S : Type*} [Fintype S]

/-- State `i` is transient: the chain started at `i` returns to `i` with probability less than one
(p. 293). -/
def IsTransient (Q : S → S → ℝ≥0∞) (i : S) : Prop :=
  SennottDP.AvgFinite.reachProb Q {i} i ≠ 1

/-- A chain with a finite state space is unichain if it has a single positive recurrent class
(p. 107; Section C.3): some state is positive recurrent and every positive recurrent state lies in
its communicating class. -/
def IsUnichain (Q : S → S → ℝ≥0∞) : Prop :=
  ∃ x, SennottDP.AvgFinite.PositiveRecurrent Q x ∧ ∀ y, SennottDP.AvgFinite.PositiveRecurrent Q y → y ∈ SennottDP.AvgFinite.commClass Q x

/-- A positive recurrent class `R` is aperiodic if `π_j = lim_{n→∞} P^{(n)}_{ij}` for all
`i, j ∈ R` (Appendix C.1, p. 295). -/
def IsAperiodicClass (Q : S → S → ℝ≥0∞) (R : Set S) : Prop :=
  ∀ i ∈ R, ∀ j ∈ R, Filter.Tendsto (fun n : ℕ => SennottDP.AvgFinite.nStep Q n i j) Filter.atTop
    (nhds (SennottDP.AvgFinite.steadyState Q j))

end SennottDP.AvgFiniteVI


