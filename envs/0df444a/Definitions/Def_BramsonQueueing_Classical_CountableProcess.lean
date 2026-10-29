-- Prove2me | Definitions.Def_BramsonQueueing_Classical_CountableProcess
-- name    : BramsonQueueing_Classical_CountableProcess
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:08.128323+00:00
-- url     : https://prove2.me/theorems/e6f9b060-3dc7-4e61-9e63-c3729adb3eb0
-- title:
--   Countable Markov jump processes and invariant laws
-- statement:
--   Let $S$ be a countable state space and $q(x,y)$ its nonnegative jump rates. Diagonal values are ignored. The total exit rate is $r(x)=\sum_{y\ne x}q(x,y)$. Define the probability of exactly $n$ jumps by the exponential first-jump recursion, and let $P_t(x,y)$ be its sum over all $n\ge0$. Regularity requires finite exit rates and $\sum_yP_t(x,y)=1$ for every $t\ge0$; communication means that a finite path of positive off-diagonal rates joins any two states.
--
--   A probability mass $\pi$ is stationary precisely when
--   $$\sum_x\pi(x)=1,\qquad \sum_x\pi(x)P_t(x,y)=\pi(y)\quad(t\ge0).$$
--   The reversed-process predicate requires regular reversed rates, the identity $\pi(x)P_t(x,y)=\pi(y)\widehat P_t(y,x)$, and the corresponding off-diagonal small-time limits. The Markov product formula then identifies all reversed finite-dimensional distributions. This is reusable process infrastructure independent of queueing or any proposed invariant law. Nonnegative infinite sums and integrals take values in $[0,\infty]$.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Section 2.2, printed pp. 23-26 / PDF pp. 31-34

import Mathlib

namespace BramsonQueueing.Classical
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Nonnegative jump rates; diagonal entries are ignored. -/
def offRate {S : Type*} (q : S → S → ℝ≥0∞) (x y : S) : ℝ≥0∞ :=
  if x = y then 0 else q x y

def exitRate {S : Type*} (q : S → S → ℝ≥0∞) (x : S) : ℝ≥0∞ :=
  ∑' y, offRate q x y

/-- Probability of exactly n jumps by t, ending in y. The first-jump recursion
uses exponential holding times and the specified jump rates, not balance equations. -/
def jumpTerm {S : Type*} (q : S → S → ℝ≥0∞) : ℕ → ℝ → S → S → ℝ≥0∞
  | 0, t, x, y => if x = y then ENNReal.ofReal (Real.exp (-(exitRate q x).toReal * t)) else 0
  | n + 1, t, x, y => ∫⁻ s in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal (Real.exp (-(exitRate q x).toReal * s)) *
        ∑' z, offRate q x z * jumpTerm q n (t - s) z y

/-- The minimal countable-state transition semigroup. -/
def transition {S : Type*} (q : S → S → ℝ≥0∞) (t : ℝ) (x y : S) : ℝ≥0∞ :=
  ∑' n, jumpTerm q n t x y

/-- Finite holding rates and no loss of mass to explosion on any finite horizon. -/
def Regular {S : Type*} (q : S → S → ℝ≥0∞) : Prop :=
  (∀ x, exitRate q x ≠ ⊤) ∧ ∀ x t, 0 ≤ t → ∑' y, transition q t x y = 1

def Communicates {S : Type*} (q : S → S → ℝ≥0∞) : Prop :=
  ∀ x y, Relation.ReflTransGen (fun u v => 0 < offRate q u v) x y

/-- Stationarity is probability normalization and invariance at every time. -/
def Stationary {S : Type*} (q : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) : Prop :=
  (∑' x, π x = 1) ∧ ∀ t, 0 ≤ t → ∀ y, ∑' x, π x * transition q t x y = π y

/-- Transition probabilities of the reversed stationary process, including the
small-time identification of its off-diagonal rates. The semigroup identity gives
all reversed finite-dimensional distributions by the Markov product formula. -/
def ReversedProcess {S : Type*} (q qhat : S → S → ℝ≥0∞) (π : S → ℝ≥0∞) : Prop :=
  Regular qhat ∧
  (∀ t, 0 ≤ t → ∀ x y, π x * transition q t x y = π y * transition qhat t y x) ∧
  ∀ x y, x ≠ y → Filter.Tendsto
    (fun t : ℝ => (transition qhat t x y).toReal / t)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (qhat x y).toReal)

end
end BramsonQueueing.Classical


