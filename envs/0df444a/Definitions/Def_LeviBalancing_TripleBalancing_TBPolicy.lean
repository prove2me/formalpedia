-- Prove2me | Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy
-- name    : LeviBalancing_TripleBalancing_TBPolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:58:47.517282+00:00
-- url     : https://prove2.me/theorems/17100a64-aa6a-4aa5-abbc-4655e16b323e
-- title:
--   §6.1 — the triple-balancing policy TB, the marginal holding cost $H_s^B$ and the number of orders $N$
-- statement:
--   Fix a stochastic lot-sizing model and a conditional demand law $I=(I_s)_s$. For an order process $Q$ and a period $s$, let $s^*$ be the last period before $s$ in which $Q$ ordered ($Q_t>0$), with $s^*=0$ if there is none, and let $x_{s^*+1}$ be the inventory level at the beginning of period $s^*+1$. Write $D_{[a,b]}=\sum_{i=a}^b D_i$.
--
--   1. The **accumulated backlogging cost over $(s^*,s]$ without an order in $s$** is
--   $$\sum_{j=s^*+1}^{s} p_j\,\bigl(D_{[s^*+1,j]}-x_{s^*+1}\bigr)^+ .$$
--   2. The **marginal holding cost** over $[s,T]$ of $q$ units ordered in period $s$ at inventory level $x_s$ (Eq. (1) with $L=0$, $c=0$) is
--   $$H_s^B(q)=\sum_{j=s}^{T}h_j\,\bigl(q-(D_{[s,j]}-x_s)^+\bigr)^+ ,$$
--   and $E[H_s^B(q)\mid f_s]$ is its integral against the conditional demand law $I_s(\omega)$, with $x_s$ the current level.
--
--   $Q$ is the **triple-balancing policy** TB when it is a feasible policy and, in every period $s=1,\dots,T$:
--
--   - *Rule 1 (when to order).* An order is placed in period $s$ if and only if the accumulated backlogging cost over $(s^*,s]$ without an order in $s$ exceeds $K$ (strictly); otherwise $Q_s=0$.
--   - *Rule 2 (how much).* If an order is placed in period $s<T$, then
--   $$Q_s=q_s^B:=\max\{q\ge 0:\ E[H_s^B(q)\mid f_s]\le K\};$$
--   if an order is placed in period $T$, it covers all current backorders and the demand $d_T$: $Q_T=D_T-x_T$.
--
--   Finally $N=\#\{t\in\{1,\dots,T\}: Q_t>0\}$ is the number of orders placed.
--
--   The rules determine $Q_1,\dots,Q_T$ recursively and uniquely, so this is the policy of the paper, not a class of policies.
--
--   **Formalization Note** The conditional expectation in Rule 2 is the lower Lebesgue integral in $[0,\infty]$ against the kernel $I_s(\omega)$, so no junk value of a conditional expectation can make the constraint hold vacuously. Whether the maximum in Rule 2 exists is a separate theorem (it needs some positive holding cost on $[s,T]$).
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 299 (PDF 16), §6.1 Rules 1–2 and §6.2 (N); p. 291 (PDF 8), Eq. (1)

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy

open MeasureTheory ProbabilityTheory

noncomputable section

namespace LeviBalancing.TripleBalancing

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `s*`: the latest period `t < s` in which `Q` placed an order (`Q t > 0`), and `0` if no order
has been placed before period `s` (§6.1, Rule 1). -/
def lastOrder (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) : ℕ :=
  ((Finset.Ico 1 s).filter (fun t => 0 < Q t ω)).sup id

/-- The accumulated backlogging cost over `(s*, s]` if no order is placed in period `s`:
`∑_{j=s*+1}^{s} p_j (D_{[s*+1, j]} − x_{s*+1})⁺`, where `x_{s*+1}` is the inventory level at the
beginning of period `s* + 1` (§6.1, Rule 1). -/
def accBacklog (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc (lastOrder Q s ω + 1) s,
    M.p j * max ((∑ i ∈ Finset.Icc (lastOrder Q s ω + 1) j, M.D i ω)
      - levelBefore M Q (lastOrder Q s ω + 1) ω) 0

/-- The marginal holding cost `H_s(q) = ∑_{j=s}^{T} h_j (q − (D_{[s, j]} − x)⁺)⁺` over `[s, T]` of `q`
units ordered in period `s` at inventory level `x`, evaluated on the demand path `d`
(Eq. (1), p. 291, with `L = 0`, `c = 0`, `α = 1`). -/
def marginalHolding (M : LotSizingModel Ω) (s : ℕ) (q x : ℝ) (d : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc s M.T, M.h j * max (q - max ((∑ i ∈ Finset.Icc s j, d i) - x) 0) 0

/-- `E[H_s(q) | f_s]`: the conditional expectation, given the information at the beginning of
period `s`, of the marginal holding cost of `q` units ordered in period `s` at the policy's current
level `x_s`, computed with the conditional demand law `I s ω` (in `ℝ≥0∞`). -/
def condMarginalHolding (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (Q : ℕ → Ω → ℝ) (s : ℕ) (q : ℝ) (ω : Ω) : ENNReal :=
  ∫⁻ d, ENNReal.ofReal (marginalHolding M s q (levelBefore M Q s ω) d) ∂(I s ω)

/-- `Q` is the triple-balancing policy TB (§6.1, p. 299) for the conditional demand law `I`:
it is a feasible policy, and in every period `s = 1, …, T` and every outcome,
* Rule 1: an order is placed in period `s` if and only if the accumulated backlogging cost over
  `(s*, s]` without an order in `s` exceeds `K` (otherwise `Q_s = 0`);
* Rule 2: if an order is placed in period `s < T`, then `Q_s = q_s^B` is the largest `q ≥ 0` with
  `E[H_s(q) | f_s] ≤ K`; if an order is placed in period `T`, it covers all current backorders and
  the demand `d_T`, i.e. `Q_T = D_T − x_T`. -/
def IsTripleBalancing (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (Q : ℕ → Ω → ℝ) : Prop :=
  IsFeasiblePolicy M Q ∧
  ∀ s ∈ Finset.Icc 1 M.T, ∀ ω,
    (accBacklog M Q s ω ≤ M.K → Q s ω = 0) ∧
    (M.K < accBacklog M Q s ω →
      (s < M.T → IsGreatest
          {q : ℝ | 0 ≤ q ∧ condMarginalHolding M I Q s q ω ≤ ENNReal.ofReal M.K} (Q s ω)) ∧
      (s = M.T → Q s ω = M.D s ω - levelBefore M Q s ω))

/-- `N`: the number of periods `t ∈ {1, …, T}` in which `Q` places an order. -/
def numOrders (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω) : ℕ :=
  ((Finset.Icc 1 M.T).filter (fun t => 0 < Q t ω)).card

end LeviBalancing.TripleBalancing

end


