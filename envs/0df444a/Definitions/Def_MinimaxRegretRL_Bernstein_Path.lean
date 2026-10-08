-- Prove2me | Definitions.Def_MinimaxRegretRL_Bernstein_Path
-- name    : MinimaxRegretRL_Bernstein_Path
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:44:30.484681+00:00
-- url     : https://prove2.me/theorems/cfd98f89-a07f-4d3f-9669-ba7b42607ced
-- title:
--   Finite suffix path law for Eq. (26)
-- statement:
--   Fix a policy $\pi$, a starting step $h$, and a starting state $x$. A suffix path records the next state after each action from $h$ through the final step. Its probability is the product of the transition probabilities specified by $P$ and $\pi$.
--
--   The definitions give the realized remaining reward, the sum of conditional variances of the next-step value, and the finite expectation and variance of any statistic of the path. They express the two sides of Eq. (26) under the same path law.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 18, Eq. (26), aligned with Algorithm 2 on p. 4

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_Process

open scoped Classical

namespace MinimaxRegretRL.Bernstein

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- A suffix of one episode, beginning at step `h`, records the next state after
each remaining action. -/
abbrev Path (S : Type*) (H : ℕ) (h : Fin H) := Fin (H - h.val) → S

def pathState (x : S) {H : ℕ} {h : Fin H} (path : Path S H h)
    (t : Fin (H - h.val)) : S :=
  if ht : t.val = 0 then x else path ⟨t.val - 1, by omega⟩

def pathStep {H : ℕ} (h : Fin H) (t : Fin (H - h.val)) : Fin H :=
  ⟨h.val + t.val, by omega⟩

/-- The finite law of the suffix path under a fixed policy and fixed start state. -/
def pathProb (M : MinimaxRegretRL.Hoeffding.MDP S A) {H : ℕ} (π : MinimaxRegretRL.Hoeffding.Policy S A H)
    (h : Fin H) (x : S) (path : Path S H h) : ℝ :=
  ∏ t : Fin (H - h.val),
    M.P (pathState x path t) (π (pathState x path t) (pathStep h t)) (path t)

/-- Remaining realized reward from step `h` through the final step. -/
def pathReward (M : MinimaxRegretRL.Hoeffding.MDP S A) {H : ℕ} (π : MinimaxRegretRL.Hoeffding.Policy S A H)
    (h : Fin H) (x : S) (path : Path S H h) : ℝ :=
  ∑ t : Fin (H - h.val),
    M.R (pathState x path t) (π (pathState x path t) (pathStep h t))

/-- The sum of conditional variances of the next-step policy values. -/
noncomputable def pathVarianceSum (M : MinimaxRegretRL.Hoeffding.MDP S A) {H : ℕ} (π : MinimaxRegretRL.Hoeffding.Policy S A H)
    (h : Fin H) (x : S) (path : Path S H h) : ℝ :=
  ∑ t : Fin (H - h.val),
    transitionVar M (pathState x path t) (π (pathState x path t) (pathStep h t))
      (valueAt M π ((pathStep h t).val + 1))

/-- Expectation with respect to the constructed path law. -/
def pathExp (M : MinimaxRegretRL.Hoeffding.MDP S A) {H : ℕ} (π : MinimaxRegretRL.Hoeffding.Policy S A H)
    (h : Fin H) (x : S) (f : Path S H h → ℝ) : ℝ :=
  ∑ path : Path S H h, pathProb M π h x path * f path

/-- Variance of a path statistic under that finite path law. -/
def pathVar (M : MinimaxRegretRL.Hoeffding.MDP S A) {H : ℕ} (π : MinimaxRegretRL.Hoeffding.Policy S A H)
    (h : Fin H) (x : S) (f : Path S H h → ℝ) : ℝ :=
  pathExp M π h x (fun path => (f path) ^ 2) - (pathExp M π h x f) ^ 2

end MinimaxRegretRL.Bernstein


