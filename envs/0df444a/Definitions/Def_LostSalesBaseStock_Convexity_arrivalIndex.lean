-- Prove2me | Definitions.Def_LostSalesBaseStock_Convexity_arrivalIndex
-- name    : LostSalesBaseStock_Convexity_arrivalIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:17:28.630727+00:00
-- url     : https://prove2.me/theorems/6fa3441f-8dd7-4ba3-82ec-03a7df658f47
-- title:
--   Arrival index $\lambda_n = \max\{t : t + L(t) \le n\}$ of a lead-time sample path
-- statement:
--   Consider a periodic-review inventory system over periods $n = 0, 1, \dots, N$. The order placed in period $t$ has a lead time $L(t) \in \{0, 1, 2, \dots\}$, so it arrives in period $t + L(t)$. The **arrival index** of period $n$ is the period index of the latest shipment that has arrived in or before period $n$:
--
--   $$
--   \lambda_n = \max\{\, t : t + L(t) \le n \,\}.
--   $$
--
--   Because $t + L(t) \le n$ forces $t \le n$, the maximum is over $t \in \{0, \dots, n\}$. When no order placed in periods $0, \dots, n$ has arrived yet, the value is $0$; in particular $\lambda_0 = 0$, which is the convention the paper adopts explicitly. This convention is harmless because the order placed in period $0$ has size $q_0 = 0$.
--
--   The arrival index is how the on-hand inventory of the base-stock system is expressed: when orders do not cross (Assumption 1: $n + L(n)$ is weakly increasing in $n$), exactly the orders placed in periods $\lambda_n < t \le n$ are still outstanding in period $n$.
--
--   **Formalization Note** The lead-time path is a function $L : \mathbb{N} \to \mathbb{N}$ and $\lambda_n$ is `Nat.findGreatest (fun t => t + L t ≤ n) n`. Assumption 1 is not built into this definition; the theorems that need it state it as a hypothesis.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 796, Section 3 (definition of lambda_n) and p. 797 (lambda_0 = 0)

import Mathlib

namespace LostSalesBaseStock.Convexity

/-- Arrival index of a lead-time sample path `L` (Janakiraman–Roundy 2004, §3, p. 796):
`λ_n = max {t : t + L(t) ≤ n}`, the period index of the latest shipment that arrived in or
before period `n`. Since `t + L(t) ≤ n` forces `t ≤ n`, the search runs over `t ∈ {0, …, n}`.
When no `t` qualifies the value is `0` (`Nat.findGreatest` of an empty search), which also
gives the paper's convention `λ_0 = 0` (p. 797); this is harmless because `q_0 = 0`. -/
def arrivalIndex (L : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun t => t + L t ≤ n) n

end LostSalesBaseStock.Convexity


