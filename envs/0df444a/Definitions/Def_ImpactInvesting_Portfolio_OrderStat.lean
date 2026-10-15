-- Prove2me | Definitions.Def_ImpactInvesting_Portfolio_OrderStat
-- name    : ImpactInvesting_Portfolio_OrderStat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:00.936646+00:00
-- url     : https://prove2.me/theorems/9c9496b0-2d30-4708-9bff-c9b79b93f0e5
-- title:
--   (6), p. 11 — order statistics X_{i:N} and induced order statistics α_[i:N] of a sample ranked by X
-- statement:
--   Let $x = (x_1, \dots, x_N)$ be a vector of real numbers and let $\pi$ be a permutation that sorts it increasingly, $x_{\pi(1)} \le x_{\pi(2)} \le \dots \le x_{\pi(N)}$ (ties broken by index). The **$i$-th order statistic** of $x$ is
--   $$X_{i:N} = x_{\pi(i)},$$
--   and, for a second vector $a = (a_1, \dots, a_N)$ attached to the same $N$ items, the **$i$-th induced order statistic** (or concomitant) is
--   $$a_{[i:N]} = a_{\pi(i)},$$
--   the entry of $a$ belonging to the item whose $x$-value has rank $i$. The order is induced by $x$: the vector $a$ is never sorted by its own values. For random vectors $X = (X_1, \dots, X_N)$ and $A = (A_1,\dots,A_N)$ on a common sample space the same construction, applied outcome by outcome, gives the random variables $X_{i:N}$ and $A_{[i:N]}$.
--
--   These are the objects of display (6) of the paper: an investor ranks $N$ securities by their impact factor $X_i$ and the excess return carried by the security of rank $i$ is $\alpha_{[i:N]}$. Every moment formula of the mission is about them.
--
--   **Formalization Note.** Ranks are 0-based: `orderStat x i` with `i : Fin N` is the paper's $X_{i+1:N}$, and `inducedOrderStat x a i` is $a_{[i+1:N]}$. Sorting uses Mathlib's `Tuple.sort`, which breaks ties by index; ties have probability zero under the mission's Gaussian assumption. `orderStatRV` and `inducedOrderStatRV` are the pointwise random-variable versions.
-- source:
--   Lo & Zhang, Quantifying the Impact of Impact Investing, SSRN 3944367 (draft of 29 June 2023), p. 11, §3.2, (6)

import Mathlib

namespace ImpactInvesting.Portfolio

/-- The `i`-th order statistic of a real tuple: `orderStat x i` is the value of rank `i` (0-based) when
the entries of `x` are sorted increasingly, i.e. `X_{i+1:N}` in the paper's 1-based notation (p. 11). -/
noncomputable def orderStat {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  x (Tuple.sort x i)

/-- The `i`-th induced order statistic (concomitant): the entry of `a` attached to the entry of `x` of
rank `i`, i.e. `α_[i+1:N]` of (6) (p. 11). The order is induced by `x`, never by `a`. -/
noncomputable def inducedOrderStat {N : ℕ} (x a : Fin N → ℝ) (i : Fin N) : ℝ :=
  a (Tuple.sort x i)

/-- `ω ↦ X_{i+1:N}(ω)` for a random sample `X 0, …, X (N-1)`. -/
noncomputable def orderStatRV {Ω : Type*} {N : ℕ} (X : Fin N → Ω → ℝ) (i : Fin N) : Ω → ℝ :=
  fun ω => orderStat (fun j => X j ω) i

/-- `ω ↦ A_[i+1:N](ω)`: the entry of `A` attached to the rank-`i` entry of `X`. -/
noncomputable def inducedOrderStatRV {Ω : Type*} {N : ℕ} (X A : Fin N → Ω → ℝ) (i : Fin N) : Ω → ℝ :=
  fun ω => inducedOrderStat (fun j => X j ω) (fun j => A j ω) i

end ImpactInvesting.Portfolio


