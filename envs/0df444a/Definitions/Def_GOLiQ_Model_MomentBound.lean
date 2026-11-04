-- Prove2me | Definitions.Def_GOLiQ_Model_MomentBound
-- name    : GOLiQ_Model_MomentBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:15.761194+00:00
-- url     : https://prove2.me/theorems/75db7433-62dd-4cc4-a763-ec5fe2fec46c
-- title:
--   The uniform moment bounds of Lemma 1 with constant $M$
-- statement:
--   For the queue operated in cycles of lengths $D_k$ under the policy $x_k=(\mu_k,p_k)$, the bounds of Lemma 1 hold with constant $M$ and exponent $\eta$ if for all $k\ge1$, $1\le n\le D_k$ and $1\le m\le4$,
--   $$\mathbb E[(W^k_n)^m],\quad \mathbb E[(X^k_n)^m],\quad \mathbb E[(Q_k)^m],\quad \mathbb E[e^{\eta W^k_n}],\quad \mathbb E[e^{\eta Q_k}]$$
--   are all at most $M$.
--
--   Lemma 1 asserts that one $M$ works for every policy; Corollary 1 and Theorem 2 use "the constant $M$ of Lemma 1".
--
--   **Formalization Note** The expectations are lower Lebesgue integrals in $[0,\infty]$, so the bound also asserts finiteness; $m$ is real; $Q_k$ takes values in $\mathbb N\cup\{\infty\}$.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Lemma 1, pp.17–18

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_CycleSystem

open MeasureTheory

namespace GOLiQ

/-- **The uniform moment bounds of Lemma 1, with constant `M`, for one queue operated in cycles**
(Chen, Liu, Hong, arXiv:2009.02911v3, Lemma 1, pp.17–18).

For the cycle system driven by the policy `xₖ = (µₖ, pₖ)` with cycle lengths `Dₖ`: for all `k ≥ 1`,
`1 ≤ n ≤ Dₖ` and `1 ≤ m ≤ 4`, the quantities

`E[(Wₙᵏ)^m]`, `E[(Xₙᵏ)^m]`, `E[(Qₖ)^m]`, `E[exp(ηWₙᵏ)]` and `E[exp(ηQₖ)]`

are all bounded by `M`.

**Formalization Note.** Expectations of these nonnegative quantities are lower Lebesgue integrals
in `[0, ∞]`, so a bound by the finite `M` also asserts finiteness. `m` is real. `Qₖ` takes values in
`ℕ ∪ {∞}`; the bound on `E[Qₖ]` makes it finite almost surely, so the natural number `Qₖ` in the
exponential moment is well defined almost surely. -/
def Model.MomentBound {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (D : ℕ → ℕ) (x : ℕ → Ω → Point) (η Mc : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 1 ≤ n → n ≤ D k → ∀ m : ℝ, 1 ≤ m → m ≤ 4 →
    ∫⁻ ω, ENNReal.ofReal ((M.system Pr D x ω).cycleWait k n ^ m) ∂Pr.P ≤ ENNReal.ofReal Mc ∧
    ∫⁻ ω, ENNReal.ofReal ((M.system Pr D x ω).cycleBusy k n ^ m) ∂Pr.P ≤ ENNReal.ofReal Mc ∧
    ∫⁻ ω, ((M.system Pr D x ω).leftover k : ENNReal) ^ m ∂Pr.P ≤ ENNReal.ofReal Mc ∧
    ∫⁻ ω, ENNReal.ofReal (Real.exp (η * (M.system Pr D x ω).cycleWait k n)) ∂Pr.P ≤
      ENNReal.ofReal Mc ∧
    ∫⁻ ω, ENNReal.ofReal (Real.exp (η * ((M.system Pr D x ω).leftover k).toNat)) ∂Pr.P ≤
      ENNReal.ofReal Mc

end GOLiQ


