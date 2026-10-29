-- Prove2me | Definitions.Def_PutermanMDP_SemiMarkov_Stationary
-- name    : PutermanMDP_SemiMarkov_Stationary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:04.497281+00:00
-- url     : https://prove2.me/theorems/7ac87af2-2e0b-4fbc-b5b8-e6a32ac1950f
-- title:
--   Stationary expected reward ratios, Cesaro limits, and evaluation equations
-- statement:
--   For a stationary randomized rule $d$, the embedded chain starts in $s$ and evolves by its mixed transition kernel. Let $P_d^n(s,j)$ be its epoch-$n$ law, and let $r_d$ and $y_d$ be its one-transition expected reward and holding-time vectors. Define
--   $$R_n^d(s)=\frac{\sum_{k=0}^{n}\sum_jP_d^k(s,j)r_d(j)}{\sum_{k=0}^{n-1}\sum_jP_d^k(s,j)y_d(j)},\qquad g^{d^\infty}(s)=\liminf_{n\to\infty}R_n^d(s).$$
--   The candidate Cesaro matrix $M_d^*$ is the entrywise liminf of $n^{-1}\sum_{k<n}P_d^k$. The probability-limit condition explicitly requires convergence to that matrix, nonnegative entries and row sums one. Separate finite-moment predicates assert absolute summability of the epoch and limiting matrix products with $r_d$ and $y_d$.
--
--   A state is recurrent when the expected total number of returns diverges. Unichain means there is a recurrent state and all recurrent states communicate; transient states are allowed. The evaluation equation is
--   $$h(s)=r_d(s)-g(s)y_d(s)+\sum_jm_d(j\mid s)h(j),$$
--   with the last sum absolutely convergent. Boundedness of $h$ is a separate predicate, not part of this equation.
--
--   These definitions distinguish a ratio of expectations from an expected ratio and from a calendar-time criterion.
--
--   **Formalization Note** Gain takes values in the extended real numbers so divergent countable-state liminfs are preserved. The numerator uses $n+1$ rewards, while the denominator uses $n$ holding-time means: the source sets $\tau_0=0$ and $\tau_{k+1}$ follows $X_k$. At $n=0$ the total denominator is zero and Lean assigns ratio zero; this isolated value does not affect the limit. The Cesaro matrix uses $n$ terms. The standalone definitions retain Lean's total-function defaults outside the explicitly stated moment and positivity conditions. The theorem domains exclude those undefined-expectation cases.
-- source:
--   Puterman, Markov Decision Processes, Wiley, 1994, https://doi.org/10.1002/9780470316887, pp. 548–553 (PDF 564–569), Eqs. (11.4.3), (11.4.9), (11.4.11)–(11.4.13), Appendix A

import Definitions.Def_PutermanMDP_SemiMarkov_Model

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PutermanMDP.SemiMarkov

variable {S : Type*}

/-- Distribution at epoch n, started in state s. -/
noncomputable def epochLaw (M : Model S) (d : Rule M) : ℕ → S → PMF S
  | 0, s => PMF.pure s
  | n + 1, s => (epochLaw M d n s).bind (embedded M d)

/-- Domain of the finite real expectations appearing in (11.4.11). -/
def FiniteEpochMoments (M : Model S) (d : Rule M) : Prop :=
  ∀ n s,
    Summable (fun j => (epochLaw M d n s j).toReal * ruleReward M d j) ∧
    Summable (fun j => (epochLaw M d n s j).toReal * ruleTime M d j)

noncomputable def expectedReward (M : Model S) (d : Rule M) (n : ℕ) (s : S) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ∑' j,
    (epochLaw M d k s j).toReal * ruleReward M d j

/-- Expected elapsed time ∑_{i=0}^n τ_i in (11.4.9). Since τ_0 = 0 and
τ_{k+1} is the sojourn following X_k, this has n terms, unlike expectedReward. -/
noncomputable def expectedTime (M : Model S) (d : Rule M) (n : ℕ) (s : S) : ℝ :=
  ∑ k ∈ Finset.range n, ∑' j,
    (epochLaw M d k s j).toReal * ruleTime M d j

noncomputable def rewardRatio (M : Model S) (d : Rule M) (n : ℕ) (s : S) : ℝ :=
  expectedReward M d n s / expectedTime M d n s

/-- Ratio-average gain, not the expectation of a ratio or calendar-time gain.
Extended values preserve divergent liminf values on a countable state space. -/
noncomputable def gain (M : Model S) (d : Rule M) (s : S) : EReal :=
  Filter.liminf (fun n => (rewardRatio M d n s : EReal)) Filter.atTop

noncomputable def cesaro (M : Model S) (d : Rule M) (n : ℕ) (s j : S) : ℝ :=
  (∑ k ∈ Finset.range n, (epochLaw M d k s j).toReal) / n

/-- Entries are bounded in [0,1]; liminf defines the candidate Cesaro limit.
CesaroProbability below explicitly requires convergence to it. -/
noncomputable def limitingMatrix (M : Model S) (d : Rule M) (s j : S) : ℝ :=
  Filter.liminf (fun n => cesaro M d n s j) Filter.atTop

def CesaroProbability (M : Model S) (d : Rule M) : Prop :=
  (∀ s j, Tendsto (fun n => cesaro M d n s j) atTop (𝓝 (limitingMatrix M d s j))) ∧
  (∀ s j, 0 ≤ limitingMatrix M d s j) ∧
  (∀ s, HasSum (limitingMatrix M d s) 1)

/-- Domain of the two finite matrix-vector products in (11.4.11). -/
def FiniteLimitMoments (M : Model S) (d : Rule M) : Prop :=
  ∀ s,
    Summable (fun j => limitingMatrix M d s j * ruleReward M d j) ∧
    Summable (fun j => limitingMatrix M d s j * ruleTime M d j)

noncomputable def limitingRatio (M : Model S) (d : Rule M) (s : S) : ℝ :=
  (∑' j, limitingMatrix M d s j * ruleReward M d j) /
  (∑' j, limitingMatrix M d s j * ruleTime M d j)

def Accessible (M : Model S) (d : Rule M) (s j : S) : Prop :=
  ∃ n, 0 < epochLaw M d n s j

/-- Recurrence via infinitely many expected visits, valid also on countable S. -/
def Recurrent (M : Model S) (d : Rule M) (s : S) : Prop :=
  (∑' n, epochLaw M d n s s) = ∞

/-- Exactly one recurrent communicating class, with transient states allowed. -/
def Unichain (M : Model S) (d : Rule M) : Prop :=
  (∃ s, Recurrent M d s) ∧
  ∀ s j, Recurrent M d s → Recurrent M d j → Accessible M d s j

/-- Evaluation equation (11.4.13). The transition expectation is required to
exist absolutely; h is not required to be bounded. -/
def EvaluationEquation (M : Model S) (d : Rule M) (g h : S → ℝ) : Prop :=
  ∀ s, Summable (fun j => (embedded M d s j).toReal * h j) ∧
    h s = ruleReward M d s - g s * ruleTime M d s +
      ∑' j, (embedded M d s j).toReal * h j

def BoundedBias (h : S → ℝ) : Prop := ∃ C : ℝ, ∀ s, |h s| ≤ C

end PutermanMDP.SemiMarkov


