-- Prove2me | Definitions.Def_GMRDiversity_value
-- name    : GMRDiversity_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:01.579208+00:00
-- url     : https://prove2.me/theorems/b76bbfd9-4407-4529-956f-5843e4ba2ded
-- title:
--   The value $V^\pi_T(\mathfrak G^{\mathrm{par}}_x)$ of a live-pool policy, averaged over $x$
-- statement:
--   For a live-pool policy $\pi$ and $T\in\mathbb N$, let $z_1,\dots,z_T$ be the first $T$ candidates it queries on the instance $\mathfrak G^{\mathrm{par}}_x$. The **value** of $\pi$ after $T$ queries is
--   $$
--   V^\pi_T:=\mathbb E\Big[\max_{t\in[T]}U_x(z_t)\Big],
--   $$
--   where the expectation is over the randomness of the operators and of the policy and also over the hidden target $x\sim\mathrm{Unif}(\{0,1\}^n)$, drawn independently of the policy. Since $U_x\in\{0,1\}$, $V^\pi_T$ is the probability that the policy queries a candidate with first coordinate $x$ within $T$ rounds.
--
--   **Formalization Note** The run of the policy for a fixed $x$ is the probability mass function `runLaw π x T` on (pool, success flag), built round by round with rounds numbered from $1$; `value π T` is $2^{-n}\sum_x$ of the probability of the flag. At $T=0$ the maximum over the empty set is $0$, so $V^\pi_0=0$.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), §2 'Query Complexity', p.4; §6, p.8

import Mathlib
import Definitions.Def_GMRDiversity_LivePoolPolicy

namespace GMRDiversity

open ExtremalForrelation.Nonadaptive

/-- The law of the candidate queried by an action: `Gen_x` for `none`, and the deterministic
`XOR(P[i], P[j]) = P[i] + P[j]` for `some (i, j)` (§6, p.8). -/
noncomputable def queryLaw {n : ℕ} (x : V n) (P : List (Cand n)) :
    Option (Fin P.length × Fin P.length) → PMF (Cand n)
  | none => genLaw x
  | some (i, j) => PMF.pure (P.get i + P.get j)

/-- One round `t` of a live-pool policy on the hidden target `x`, acting on the state
(pool, has the target been queried yet). -/
noncomputable def roundStep {n w : ℕ} (π : LivePoolPolicy n w) (x : V n) (t : ℕ)
    (s : List (Cand n) × Bool) : PMF (List (Cand n) × Bool) :=
  (π.act t s.1).bind fun a =>
    (queryLaw x s.1 a).bind fun z =>
      (π.keep t s.1 a z (hit x z)).map fun P' => (P', s.2 || hit x z)

/-- The law after `T` rounds of (pool `P_T`, `max_{t ∈ [T]} U_x(z_t) = 1`), starting from the
empty pool; round `T + 1` is the round with index `t = T + 1` (rounds are numbered from `1`). -/
noncomputable def runLaw {n w : ℕ} (π : LivePoolPolicy n w) (x : V n) :
    ℕ → PMF (List (Cand n) × Bool)
  | 0 => PMF.pure ([], false)
  | T + 1 => (runLaw π x T).bind (roundStep π x (T + 1))

/-- **The value `V^π_T(𝔊^par_x)`** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with
Optimization Guided Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, §2 "Query
Complexity", p.4, and §6, p.8): `V^π_T := E[max_{t ∈ [T]} U_x(z_t)]`, where "x ∼ Unif({0,1}ⁿ);
policies are chosen independently of x, and V^π_T also averages over the choice of x".

**Formalization Note.** Since `U_x ∈ {0,1}`, the expectation of the maximum is the probability that
some `z_t`, `t ≤ T`, has first coordinate `x`; it is computed from the run law of the policy for each
fixed `x` and averaged over the `2ⁿ` values of `x`. At `T = 0` the maximum over the empty set is
taken to be `0`, so `V^π_0 = 0`. -/
noncomputable def value {n w : ℕ} (π : LivePoolPolicy n w) (T : ℕ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, ((runLaw π x T).toOuterMeasure {s | s.2 = true}).toReal

end GMRDiversity


