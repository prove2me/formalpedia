-- Prove2me | Definitions.Def_SturtRobustStop_Structure_Policy
-- name    : SturtRobustStop_Structure_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:09:17.976798+00:00
-- url     : https://prove2.me/theorems/017ae432-84c3-4a0d-b623-e815aef2758b
-- title:
--   Finite-horizon measurable exercise policies and first stopping index
-- statement:
--   A policy on a measurable state space $X$ consists of measurable stopping regions $S_t\subseteq X$ for each period $t=1,\ldots,T$. It stops exactly when the current state belongs to the current region; otherwise it continues. Its stopping index on $y\in X^T$ is $\tau_\mu(y)=\min\{t:y_t\in S_t\}$, with value $\infty$ when no period stops. This is a separate general policy interface, with no reward, sample, stochastic law, or terminal-exercise requirement. The paper specializes it to the Borel space $\mathbb R^d$.
--
--   The helper firstIndex computes the least member of a finite predicate by a finite minimum. Lean period k denotes paper period k+1. Option.none represents infinity; Option.some represents the corresponding finite index. No order on Option is used.
-- source:
--   Bradley Sturt, A Nonparametric Algorithm for Optimal Stopping Based on Robust Optimization, arXiv:2103.03300v4, §2.1, exercise policies and stopping rule, printed p. 6, PDF p. 6. https://arxiv.org/abs/2103.03300v4

import Mathlib

namespace SturtRobustStop.Structure

/-- A finite-horizon measurable Markovian exercise policy, independently of any
sample or reward model. Period `t : Fin T` means source period `t.val + 1`.
Membership in `stop t` means Stop; its complement means Continue. -/
structure Policy (T : ℕ) (X : Type*) [MeasurableSpace X] where
  stop : Fin T → Set X
  measurable_stop : ∀ t, MeasurableSet (stop t)

/-- The first index satisfying a predicate; `none` means no such index (∞).
No ordering on `Option` is used. -/
noncomputable def firstIndex {T : ℕ} (p : Fin T → Prop) : Option (Fin T) := by
  classical
  let s := Finset.univ.filter p
  exact if h : s.Nonempty then some (s.min' h) else none

/-- First exercise on a path; the policy reads only the current state and time. -/
noncomputable def stoppingTime {T : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Policy T X) (y : Fin T → X) : Option (Fin T) :=
  firstIndex fun t => y t ∈ μ.stop t

end SturtRobustStop.Structure


