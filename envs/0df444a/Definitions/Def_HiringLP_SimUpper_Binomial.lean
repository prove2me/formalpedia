-- Prove2me | Definitions.Def_HiringLP_SimUpper_Binomial
-- name    : HiringLP_SimUpper_Binomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:00.255643+00:00
-- url     : https://prove2.me/theorems/2d7c1772-9c46-4867-8e41-6ca7b3f7cc6e
-- title:
--   App. D.7, pp. ec19–ec20 — Binomial pmf, E[min{k, Bin(m, q)}] and P(Bin(m, q) > k)
-- statement:
--   For an integer $m \ge 0$ and $q \in [0,1]$, the Binomial pmf is
--   $$
--   \Pr[\mathrm{Bin}(m, q) = t] = \binom{m}{t} q^t (1-q)^{m-t}, \qquad 0 \le t \le m.
--   $$
--   From it we define the truncated mean $\mathbb{E}[\min\{k, \mathrm{Bin}(m,q)\}] = \sum_{t=0}^m \min\{t,k\} \Pr[\mathrm{Bin}(m,q) = t]$ and the upper tail $\Pr[\mathrm{Bin}(m,q) > k] = \sum_{t=k+1}^m \Pr[\mathrm{Bin}(m,q) = t]$.
--
--   These are the quantities in the proof of Theorem 4: when a value-ordered policy offers to $m$ type-1 candidates of the hard instance, the number of acceptances is $\mathrm{Bin}(m, k/j)$, and $A_j$ is the event $\{\mathrm{Bin}(m_j, k/j) > k\}$.
--
--   **Formalization Note.** All three are finite sums written by hand (Mathlib's `PMF.binomial` takes values in `ℝ≥0∞` on `Fin (m+1)`); they are polynomials in $q$ and make sense for every real $q$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, App. D.7, p. ec19 (PDF p. 51), event A_j and (EC.15); p. ec20 (PDF p. 52), (EC.16)–(EC.18)

import Mathlib

namespace HiringLP.SimUpper

open Finset

/-- The Binomial pmf `P(Bin(m, q) = t) = C(m, t) q^t (1 − q)^{m − t}`, for `t ≤ m`. -/
def binomPMF (m : ℕ) (q : ℝ) (t : ℕ) : ℝ :=
  (m.choose t : ℝ) * q ^ t * (1 - q) ^ (m - t)

/-- `E[min{k, Bin(m, q)}]`. -/
def expMinBinom (m : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ range (m + 1), min (t : ℝ) k * binomPMF m q t

/-- `P(Bin(m, q) > k)`. -/
def tailBinom (m : ℕ) (q : ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ range (m + 1), if k < t then binomPMF m q t else 0

end HiringLP.SimUpper


