-- Prove2me | Definitions.Def_BilateralProfitLB_Stochastic
-- name    : BilateralProfitLB_Stochastic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:31.979297+00:00
-- url     : https://prove2.me/theorems/639a6c12-0115-4ab4-a5fb-f19bdddc4b33
-- title:
--   §2, §7 — the stochastic setting with two-bit feedback: randomized policies, runs, regret against a comparator, and expected visit counts
-- statement:
--   In the **stochastic setting** of bilateral trade, the valuation pairs $(s_t,b_t)$, $t=1,\dots,T$, are drawn i.i.d. from a fixed unknown law $\mathcal D$ on $\mathbb R^2$. In each round the learner posts a seller price $p_t$ and a buyer price $q_t$, with $(p_t,q_t)\in[0,1]^2$, and earns $\mathrm{Profit}_t(p_t,q_t)=(q_t-p_t)\,\mathbb 1\{s_t\le p_t\}\,\mathbb 1\{q_t\le b_t\}$.
--
--   With **two-bit feedback** the learner observes, after round $t$, the pair $\big(\mathbb 1\{s_t\le p_t\},\ \mathbb 1\{q_t\le b_t\}\big)$: separately whether the seller and the buyer accepted. A **policy** draws a seed $\omega$ once from a probability space $(\Omega,P)$ and chooses $(p_t,q_t)$ as a function of $\omega$ and of the feedback pairs of rounds $1,\dots,t-1$, measurably in $\omega$. A **one-bit** policy (the model of §2) is one whose prices depend on each past pair only through the trade bit $z_t=\mathbb 1\{s_t\le p_t\}\mathbb 1\{q_t\le b_t\}$. A **deterministic** algorithm is a policy whose seed space has a single point.
--
--   The run of horizon $T$ has seed $\omega\sim P$ independent of $v_1,\dots,v_T$ i.i.d. $\sim\mathcal D$. For a comparator $(p,q)$ the regret is
--   $$\sum_{t=1}^T\Big(\mathbb E[\mathrm{Profit}_t(p,q)]-\mathbb E[\mathrm{Profit}_t(p_t,q_t)]\Big),$$
--   whose supremum over $(p,q)\in[0,1]^2$ is the paper's $R_T(\mathcal A,\mathcal D)$. For a set $I$ of buyer prices, $\mathbb E[N]$ is the expected number of rounds with $q_t\in I$.
--
--   Finally, an independent bilateral-trade environment (independent seller and buyer with densities strictly positive on their supports) has **unit support** if both supports are $[0,1]$.
--
--   These objects carry the lower bound of Theorem 7.1 and its Claims 3.6 and the regret display of §7.
--
--   **Formalization Note** The feedback history is a list of pairs of booleans, oldest first; its length is the round index, and rounds are numbered $0,\dots,T-1$. A policy may depend on the horizon $T$ by being chosen after $T$. The run's law is the product of $P$ with the $T$-fold product of $\mathcal D$. All integrands are bounded and measurable, so the expectations are genuine when $P$ and $\mathcal D$ are probability measures.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §2, pp.3–4 (PDF 5–6); §7, proof of Theorem 7.1, p.49 (PDF 51) (two-bit feedback); p.51 (PDF 53) (N_j)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_MechanismDesign_BilateralTrade_Model

namespace BilateralProfitLB

open MeasureTheory BilateralProfit

/-! # The stochastic setting with two-bit feedback: policies, runs, regret and counts

Brüstle, di Gregorio, Fusco, Leonardi, *Regret Bounds for Profit Maximization in Bilateral
Trade: Learning the Best Posted-Price Mechanism* (manuscript, sha256 e91e8127…), §2, pp.3–4
(PDF 5–6): the stochastic setting (valuations i.i.d. from a fixed unknown law `𝒟`), the regret
`R_T(𝒜, 𝒮) = sup_{(p,q)∈[0,1]²} Σ_{t=1}^T E[Profit_t(p, q) − Profit_t(p_t, q_t)]`; §7, p.49
(PDF 51): "algorithms that receive two bits of information at each step, indicating separately
whether the seller and the buyer accepted the corresponding prices"; p.51 (PDF 53): `N_j`,
the number of rounds in which the algorithm posts a buyer price in a set.

**Formalization Note.**
1. A *policy* (learning algorithm) draws a seed `ω` from a probability space `(Ω, P)` once and,
   in round `t`, posts the price pair `price ω h ∈ [0,1]²`, where `h` is the list of the
   feedback pairs of rounds `0, …, t − 1` (oldest first; its length is `t`). Past prices are
   functions of `ω` and of past feedback, so they are not passed separately. The price is
   measurable in the seed for every fixed history. The round index is the length of the
   history, so a policy may depend on the horizon `T` only by being chosen after `T`.
2. The per-round feedback is the pair of bits `(1{s_t ≤ p_t}, 1{q_t ≤ b_t})` (`true` = the
   agent accepts). A *one-bit* policy (the paper's §2 model) is one whose prices depend on each
   past pair only through the trade bit `z_t = 1{s_t ≤ p_t} 1{q_t ≤ b_t}` (`OneBit`).
3. Rounds are `Fin T`, 0-based (the paper's rounds `1, …, T`). The valuations
   `v : Fin T → ℝ × ℝ` are i.i.d. with law `D` and independent of the seed: the run lives on
   `Ω × (Fin T → ℝ × ℝ)` with the law `P ⊗ D^{⊗T}` (`runMeasure`).
4. `regret π P D T a` is the sum over rounds of `E[Profit_t(a)] − E[Profit_t(p_t, q_t)]` for one
   fixed comparator `a`; the paper's `R_T` is its supremum over `a ∈ [0,1]²`. All integrands are
   bounded and measurable (the prices take finitely many measurable branches), so no integral is
   a junk value when `P` and `D` are probability measures.
5. A *deterministic* algorithm is a policy on the one-point seed space `Unit` with
   `P = dirac ()`. -/

/-- The two feedback bits of round `t` for valuations `v = (s, b)` and prices `a = (p, q)`:
`(1{s ≤ p}, 1{q ≤ b})` (§7, p.49; ties are acceptances, §2, p.3). -/
noncomputable def feedback (v a : ℝ × ℝ) : Bool × Bool :=
  (decide (v.1 ≤ a.1), decide (a.2 ≤ v.2))

/-- The trade bit `z = 1{s ≤ p} · 1{q ≤ b}` recovered from the two bits. -/
def tradeOf (z : Bool × Bool) : Bool := z.1 && z.2

/-- A randomized, non-anticipating posted-price policy with two-bit feedback on the seed space
`(Ω, P)`: in the round following the feedback history `h` it posts `price ω h ∈ [0,1]²`. -/
structure Policy (Ω : Type) [MeasurableSpace Ω] where
  /-- the price pair `(p_t, q_t)` posted after the feedback history `h` (oldest first) -/
  price : Ω → List (Bool × Bool) → ℝ × ℝ
  price_mem : ∀ ω h, price ω h ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  price_measurable : ∀ h, Measurable fun ω => price ω h

variable {Ω : Type} [MeasurableSpace Ω]

/-- A one-bit policy (§2, p.4: "the learner receives only the trade bit `z_t`"): its prices
depend on the feedback history only through the trade bits. -/
def Policy.OneBit (π : Policy Ω) : Prop :=
  ∀ ω (h h' : List (Bool × Bool)), h.map tradeOf = h'.map tradeOf → π.price ω h = π.price ω h'

/-- The feedback history before round `t` (a list of length `min t T`) of the policy `π` with
seed `ω` on the valuation sequence `v`. -/
noncomputable def hist (π : Policy Ω) (ω : Ω) {T : ℕ} (v : Fin T → ℝ × ℝ) :
    ℕ → List (Bool × Bool)
  | 0 => []
  | t + 1 =>
      if ht : t < T then hist π ω v t ++ [feedback (v ⟨t, ht⟩) (π.price ω (hist π ω v t))]
      else hist π ω v t

/-- The price pair `(p_t, q_t)` posted in round `t`. -/
noncomputable def act (π : Policy Ω) (ω : Ω) {T : ℕ} (v : Fin T → ℝ × ℝ) (t : Fin T) :
    ℝ × ℝ :=
  π.price ω (hist π ω v t)

/-- The law of a run of horizon `T`: seed `ω ∼ P`, independent of the valuations
`v_0, …, v_{T−1}` i.i.d. `∼ D`. -/
noncomputable def runMeasure (P : Measure Ω) (D : Measure (ℝ × ℝ)) (T : ℕ) :
    Measure (Ω × (Fin T → ℝ × ℝ)) :=
  P.prod (Measure.pi fun _ : Fin T => D)

/-- `E[Profit_t(p_t, q_t)]`, the expected profit of the policy in round `t`. -/
noncomputable def expProfit (π : Policy Ω) (P : Measure Ω) (D : Measure (ℝ × ℝ)) (T : ℕ)
    (t : Fin T) : ℝ :=
  ∫ x, profit (x.2 t) (act π x.1 x.2 t) ∂(runMeasure P D T)

/-- The regret of the policy against the fixed comparator `a = (p, q)`:
`Σ_{t} (E[Profit_t(p, q)] − E[Profit_t(p_t, q_t)])` (§2, p.4, before the supremum over
`(p, q) ∈ [0,1]²`). -/
noncomputable def regret (π : Policy Ω) (P : Measure Ω) (D : Measure (ℝ × ℝ)) (T : ℕ)
    (a : ℝ × ℝ) : ℝ :=
  ∑ t : Fin T, ((∫ v, profit v a ∂D) - expProfit π P D T t)

/-- `E[N]`, the expected number of rounds `t` in which the policy posts a buyer price
`q_t ∈ I` (p.51: `N_j` for `I = I_j`). -/
noncomputable def expCount (π : Policy Ω) (P : Measure Ω) (D : Measure (ℝ × ℝ)) (T : ℕ)
    (I : Set ℝ) : ℝ := by
  classical
  exact ∫ x, (((Finset.univ : Finset (Fin T)).filter fun t => (act π x.1 x.2 t).2 ∈ I).card : ℝ)
    ∂(runMeasure P D T)

/-- An independent bilateral-trade environment (`MechanismDesign.BilateralTrade.Environment`:
independent seller and buyer with densities strictly positive on their supports) whose supports
are both `[0, 1]`, as in §2, p.4 ("strictly positive probability densities `f_s` and `f_b` on
`[0, 1]`"). -/
def UnitSupport (E : MechanismDesign.BilateralTrade.Environment) : Prop :=
  E.loS = 0 ∧ E.hiS = 1 ∧ E.loB = 0 ∧ E.hiB = 1

end BilateralProfitLB


