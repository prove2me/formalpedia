-- Prove2me | Definitions.Def_ServiceParts_Palm_LostSalesBalance
-- name    : ServiceParts_Palm_LostSalesBalance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T22:11:41.396247+00:00
-- url     : https://prove2.me/theorems/20d51a1a-e575-49a9-8bcf-6b26ae7e03d6
-- title:
--   Balance equations of the lost-sales (s–1, s) system with exponential resupply
-- statement:
--   Consider the lost-sales $(s-1,s)$ system: orders arrive at rate $\lambda$, each unit in resupply completes at rate $\beta$ (exponential resupply times with mean $\bar\tau = 1/\beta$), and an order that arrives when all $s$ units are in resupply is lost. A vector $(\pi_0, \dots, \pi_s)$ satisfies the **balance equations** when, for every state $0 \le j \le s$, the rate out of $j$ equals the rate into $j$:
--
--   1. for $j = 0$ (and $s \ge 1$): $\lambda \pi_0 = \beta \pi_1$ (3.26);
--   2. for $0 < j < s$: $0 = -(\lambda + j\beta)\pi_j + \lambda \pi_{j-1} + (j+1)\beta \pi_{j+1}$ (3.25);
--   3. for $j = s$: $s\beta\pi_s = \lambda \pi_{s-1}$ (3.32).
--
--   In one formula,
--   $$\big(\lambda\,[j<s] + j\beta\big)\pi_j = \lambda\,\pi_{j-1}[j>0] + (j+1)\beta\,\pi_{j+1}[j<s], \qquad 0 \le j \le s.$$
--
--   These are the equations whose normalized solution the proof of Theorem 8 computes as the steady-state distribution of the number of units in resupply.
--
--   **Formalization Note** The vector is a function on $\mathbb N$ of which only $\pi_0, \dots, \pi_s$ enter. The book writes (3.25) "for $0 \le j \le s$" with $\pi_{-1} = \pi_{s+1} = 0$; at $j = s$ that reading would keep the outflow $\lambda\pi_s$ of a lost order, which contradicts the book's own boundary equation (3.32). The definition follows (3.26), (3.25) for interior states and (3.32), which is what the proof uses. For $s = 0$ the only equation is $0 = 0$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 44-45, Section 3.1.2, Eqs. (3.24)-(3.26), (3.32)

import Mathlib

namespace ServiceParts.Palm

/-- The balance equations of the lost-sales (s–1, s) system with exponential resupply,
Muckstadt (2005), pp. 44–45, (3.25), (3.26), (3.32): orders arrive at rate `lam`, each unit in
resupply completes at rate `β`, and an order arriving when all `s` units are in resupply is
lost. For every state `0 ≤ j ≤ s`, the rate out of `j` equals the rate into `j`:
`((if j < s then λ else 0) + jβ) π_j = λ π_{j-1} [j > 0] + (j+1) β π_{j+1} [j < s]`.
For `0 < j < s` this is (3.25), for `j = 0` it is (3.26) `λ π_0 = β π_1`, and for `j = s` it is
(3.32) `s β π_s = λ π_{s-1}`. Only the values `π 0, …, π s` enter. -/
def LostSalesBalance (lam β : ℝ) (s : ℕ) (π : ℕ → ℝ) : Prop :=
  ∀ j, j ≤ s →
    ((if j < s then lam else 0) + (j : ℝ) * β) * π j =
      (if 0 < j then lam * π (j - 1) else 0) +
        (if j < s then ((j : ℝ) + 1) * β * π (j + 1) else 0)

end ServiceParts.Palm


