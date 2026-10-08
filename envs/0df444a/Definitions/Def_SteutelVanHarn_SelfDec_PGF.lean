-- Prove2me | Definitions.Def_SteutelVanHarn_SelfDec_PGF
-- name    : SteutelVanHarn_SelfDec_PGF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:49.681984+00:00
-- url     : https://prove2.me/theorems/dff88515-5f9e-4a86-822d-5aef46bb6119
-- title:
--   Distributions on $\mathbb N_0$ and their probability generating functions
-- statement:
--   A **distribution on** $\mathbb N_0=\{0,1,2,\dots\}$ is a sequence $(p_n)_{n\ge0}$ of real numbers with $p_n\ge 0$ for every $n$ and $\sum_{n\ge0}p_n=1$. The **generating function** of a real sequence $(p_n)$ is
--   $$
--   P(z)=\sum_{n=0}^{\infty}p_n z^n ,
--   $$
--   and when $(p_n)$ is a distribution, $P$ is its **probability generating function** (p.g.f.). Following the paper, the generating functions of sequences $(a_n),(b_n),(g_n),\dots$ are written $A,B,G,\dots$.
--
--   These two objects are the vocabulary of every statement in the mission: self-decomposability, infinite divisibility and the canonical forms are all identities between p.g.f.'s.
--
--   **Formalization Note** A distribution is a function `p : ℕ → ℝ` with `∀ n, 0 ≤ p n` and `HasSum p 1`. The p.g.f. is the real function $z\mapsto\sum' p_n z^n$; for a distribution the series converges absolutely on $[-1,1]$, and the statements of the mission only evaluate it on $[0,1]$ or differentiate it inside $(-1,1)$. Outside the domain of convergence Lean's `tsum` returns $0$.
-- source:
--   Steutel & van Harn, Discrete analogues of self-decomposability and stability, Memorandum COSOR 78-07, TH Eindhoven (1978), p. 1, §1 (distributions on ℕ₀, p.g.f.'s, notation A, B for the generating functions of (a_n), (b_n))

import Mathlib

namespace SteutelVanHarn.SelfDec

/-- A probability distribution on `ℕ₀ = {0, 1, 2, …}` (Steutel & van Harn, Memorandum COSOR 78-07,
§1, p. 1): a sequence `p n ≥ 0` with `∑ p n = 1`. -/
def IsDistribution (p : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ HasSum p 1

/-- The generating function `P(z) = ∑ p n z ^ n` of a sequence `p` (§1, p. 1). For a distribution it
is the probability generating function (p.g.f.).

Formalization Note: `z` is real; for a distribution the series converges on `[-1, 1]`, and every
statement of the mission evaluates `pgf` only on `[0, 1]` (or on an open set inside `(-1, 1)` when
differentiating). Outside the domain of convergence `tsum` returns `0`. -/
noncomputable def pgf (p : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' n, p n * z ^ n

end SteutelVanHarn.SelfDec


