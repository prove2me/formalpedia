-- Prove2me | Definitions.Def_BilateralProfitRegular_Stochastic
-- name    : BilateralProfitRegular_Stochastic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:33.4517+00:00
-- url     : https://prove2.me/theorems/b27b0a21-f81b-4bf1-8fee-e18d5a3f5531
-- title:
--   §2 — the stochastic setting: randomized one-bit policies, the i.i.d. run and the regret $R_T$
-- statement:
--   In the **stochastic setting** a seller and a buyer arrive in each round $t=1,\dots,T$ with valuations $(s_t,b_t)\in[0,1]^2$ drawn i.i.d. from a fixed unknown law $\mathcal D$. Here $\mathcal D$ is the joint law of an `Environment` $E$: independent seller and buyer values with measurable densities $f_s,f_b$ strictly positive on their supports. The predicate **OnUnit** says both supports are $[0,1]$, and **RegularUnit** adds regularity: the virtual cost $\psi(s)=s+F_s(s)/f_s(s)$ and the virtual value $\phi(b)=b-(1-F_b(b))/f_b(b)$ are nondecreasing on $[0,1]$ (Definitions 2.1–2.2).
--
--   A **policy** for horizon $T$ draws a seed $\omega$ once from a probability space $(\Omega,P)$. In round $t$ it posts a price pair $(p_t,q_t)\in[0,1]^2$ that depends on $\omega$ and on the feedback of the earlier rounds. The feedback of a round is the pair $(\mathbb 1\{s_t\le p_t\},\mathbb 1\{q_t\le b_t\})$. The policy is **one-bit** when its prices depend on each past pair only through the trade bit $z_t=\mathbb 1\{s_t\le p_t\}\mathbb 1\{q_t\le b_t\}$.
--
--   The run lives on $\Omega\times([0,1]^2)^T$ with law $P\otimes\mathcal D^{\otimes T}$. The **regret** against a comparator $(p,q)$ is
--   $$\sum_{t=1}^T\Big(\mathbb E\big[\mathrm{Profit}_t(p,q)\big]-\mathbb E\big[\mathrm{Profit}_t(p_t,q_t)\big]\Big),\qquad \mathrm{Profit}_t(p,q)=(q-p)\,\mathbb 1\{s_t\le p\}\,\mathbb 1\{q\le b_t\}.$$
--   The paper's $R_T(\mathcal A,\mathcal D)$ is its supremum over $(p,q)\in[0,1]^2$.
--
--   **Formalization Note** Rounds are indexed $0,\dots,T-1$, and the history is the list of past feedback pairs, oldest first. For every history the price is a measurable function of the seed.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §2, pp.3–4 (PDF 5–6): protocol, stochastic setting, regret, Definitions 2.1–2.2

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_MechanismDesign_BilateralTrade_Model

namespace BilateralProfitRegular

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

/-! # The stochastic setting: environments, randomized one-bit policies, the run and the regret

Brüstle, di Gregorio, Fusco, Leonardi, *Regret Bounds for Profit Maximization in Bilateral
Trade: Learning the Best Posted-Price Mechanism* (manuscript, sha256 e91e8127…), §2, pp.3–4
(PDF 5–6): the protocol, the stochastic setting, the regret `R_T(𝒜, 𝒮)`, Definitions 2.1–2.2.

**Formalization Note.**
* The seller/buyer laws are those of a published `MechanismDesign.BilateralTrade.Environment`
  `E` (independent values with measurable densities strictly positive on the closed supports),
  with supports `[0, 1]` (`OnUnit E`); regularity is `E.Regular` (Definition 2.2: the virtual
  cost `ψ` and the virtual value `ϕ` of Definition 2.1 nondecreasing on `[0,1]`). The joint law of
  one round's valuation pair `(s, b)` is `E.prior`.
* Rounds are `Fin T` (0-based). A policy draws a seed `ω` once from a probability space
  `(Ω, P)`; in round `t` it posts `price t ω h ∈ [0,1]²`, where `h` is the list of the feedback
  pairs `(1{s ≤ p}, 1{q ≤ b})` of the rounds before `t`, oldest first. Past prices are functions
  of `ω` and past feedback, so they are not passed. `OneBit` says the prices see each past pair
  only through the trade bit `z = 1{s ≤ p}·1{q ≤ b}`.
* The valuations of the `T` rounds are i.i.d. with law `E.prior`, independent of the seed: the
  run lives on `Ω × (Fin T → ℝ × ℝ)` with law `P ⊗ E.prior^T`.
* The regret against a fixed comparator `a ∈ [0,1]²` is
  `∑_t (E[Profit_t(a)] − E[Profit_t(p_t, q_t)])`; the paper's `R_T` is its supremum over
  `a ∈ [0,1]²`, so an upper bound on `R_T` is a bound for every `a`. -/

/-- The valuation laws have supports `[0, 1]` on both sides (§2, p.4: "strictly positive
probability densities `f_s` and `f_b` on `[0, 1]`"). -/
def OnUnit (E : Environment) : Prop :=
  E.loS = 0 ∧ E.hiS = 1 ∧ E.loB = 0 ∧ E.hiB = 1

/-- Independent regular seller and buyer distributions on `[0, 1]` with strictly positive
densities (§2, p.4, Definitions 2.1–2.2). -/
def RegularUnit (E : Environment) : Prop := OnUnit E ∧ E.Regular

/-- The feedback pair `(1{s ≤ p}, 1{q ≤ b})` of a round with valuations `v = (s, b)` and prices
`a = (p, q)`. -/
noncomputable def feedback (v a : ℝ × ℝ) : Bool × Bool :=
  (decide (v.1 ≤ a.1), decide (a.2 ≤ v.2))

/-- A randomized non-anticipating policy for horizon `T` with seed space `Ω`. -/
structure Policy (T : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  /-- the price pair posted in round `t`, given the seed and the past feedback (oldest first) -/
  price : Fin T → Ω → List (Bool × Bool) → ℝ × ℝ
  /-- every posted pair lies in `[0,1]²` -/
  price_mem : ∀ t ω h, price t ω h ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  /-- for each round and each feedback history, the price is a measurable function of the seed -/
  measurable_price : ∀ t h, Measurable fun ω => price t ω h

/-- One-bit feedback: the prices depend on each past feedback pair only through the trade bit
`z = 1{s ≤ p}·1{q ≤ b}` (§2, p.4). -/
def Policy.OneBit {T : ℕ} {Ω : Type} [MeasurableSpace Ω] (π : Policy T Ω) : Prop :=
  ∀ t ω (h h' : List (Bool × Bool)),
    h.map (fun z => z.1 && z.2) = h'.map (fun z => z.1 && z.2) → π.price t ω h = π.price t ω h'

/-- The feedback history after the first `t` rounds of the run with seed `ω` and valuations `v`
(oldest first). -/
noncomputable def Policy.hist {T : ℕ} {Ω : Type} [MeasurableSpace Ω] (π : Policy T Ω)
    (ω : Ω) (v : Fin T → ℝ × ℝ) : ℕ → List (Bool × Bool)
  | 0 => []
  | t + 1 =>
    if ht : t < T then
      π.hist ω v t ++ [feedback (v ⟨t, ht⟩) (π.price ⟨t, ht⟩ ω (π.hist ω v t))]
    else π.hist ω v t

/-- The price pair `(p_t, q_t)` posted in round `t` of the run. -/
noncomputable def Policy.action {T : ℕ} {Ω : Type} [MeasurableSpace Ω] (π : Policy T Ω)
    (t : Fin T) (ω : Ω) (v : Fin T → ℝ × ℝ) : ℝ × ℝ :=
  π.price t ω (π.hist ω v t)

/-- The expected regret of the policy against the fixed comparator `a`:
`∑_{t} (E[Profit_t(a)] − E[Profit_t(p_t, q_t)])`, the valuations i.i.d. with law `D`,
independent of the seed `ω ∼ P` (§2, p.4). -/
noncomputable def Policy.regret {T : ℕ} {Ω : Type} [MeasurableSpace Ω] (π : Policy T Ω)
    (P : Measure Ω) (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : ℝ :=
  ∑ t : Fin T, ((∫ v, profit v a ∂D) -
    ∫ x, profit (x.2 t) (π.action t x.1 x.2) ∂(P.prod (Measure.pi fun _ : Fin T => D)))

end BilateralProfitRegular


