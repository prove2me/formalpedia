-- Prove2me | Definitions.Def_BilateralProfitMHR_Model
-- name    : BilateralProfitMHR_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:18:26.44395+00:00
-- url     : https://prove2.me/theorems/53a7aa44-6918-4414-9144-8b7776a99169
-- title:
--   §2 — the stochastic setting: MHR laws on $[0,1]$, randomized one-bit pricing policies, the run and the regret $R_T(\mathcal A,\mathcal D)$
-- statement:
--   This file sets up the stochastic setting of the paper for independent valuations with the monotone hazard rate property.
--
--   **Valuation laws.** A seller value $s$ and a buyer value $b$ are independent, with probability densities $f_s$ and $f_b$ that are strictly positive on $[0,1]$ and integrate to $1$ there; $F_s$, $F_b$ are their distribution functions, and $\mathcal D=\mathcal D_s\times\mathcal D_b$ is the product law. This is the published bilateral trade environment with both supports equal to $[0,1]$ (**UnitSupport**). The pair is **MHR** (Definition 2.3) if the seller's hazard rate $f_s/F_s$ is nonincreasing on $(0,1]$ and the buyer's hazard rate $f_b/(1-F_b)$ is nondecreasing on $[0,1)$.
--
--   **Expected profit.** With $P(p,q)=\Pr_{(s,b)\sim\mathcal D}(s\le p,\ b\ge q)$, the expected profit is $\mu(p,q)=(q-p)P(p,q)$, its optimum is $\mu^\star=\sup_{(p,q)\in[0,1]^2}\mu(p,q)$, and the loss of Proposition 3.2 is $L(p,q)=-\log\mu(p,q)$. The open triangle $\{(p,q):0<p<q<1\}$ is the interior of $\mathcal T=\{(p,q)\in[0,1]^2:p\le q\}$.
--
--   **Algorithms.** A pricing algorithm for horizon $T$ draws a seed $\omega$ once from a probability space $(\Omega,P)$ and, in each round $t$, posts a price pair $(p_t,q_t)\in[0,1]^2$ that is a function of $\omega$ and of the feedback of the earlier rounds, measurable in $\omega$. The feedback of a round is the pair of bits $(\mathbb 1\{s_t\le p_t\},\mathbb 1\{q_t\le b_t\})$; the algorithm has **one-bit feedback** if its prices depend on each past round only through the trade bit $z_t=\mathbb 1\{s_t\le p_t\}\mathbb 1\{q_t\le b_t\}$.
--
--   **Regret.** The valuations $(s_t,b_t)$ of the $T$ rounds are i.i.d. with law $\mathcal D$ and independent of the seed. The regret against a comparator $(p,q)$ is
--   $$\sum_{t=1}^T\Big(\mathbb E[\mathrm{Profit}_t(p,q)]-\mathbb E[\mathrm{Profit}_t(p_t,q_t)]\Big),$$
--   and $R_T(\mathcal A,\mathcal D)$ is its supremum over $(p,q)\in[0,1]^2$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** Price and valuation pairs are points of $\mathbb R^2$ (seller coordinate first); rounds are indexed $0,\dots,T-1$. Past prices are functions of the seed and the past feedback, so a policy is given by these alone. Logarithms are natural.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §2, pp.3–4 (PDF 5–6): learning protocol, stochastic setting, regret, Definitions 2.1–2.3; Proposition 3.2, p.11 (PDF 13)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_MechanismDesign_BilateralTrade_Model

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

/-! # The stochastic setting of §2 for independent MHR valuations

Brüstle, di Gregorio, Fusco, Leonardi, *Regret Bounds for Profit Maximization in Bilateral
Trade: Learning the Best Posted-Price Mechanism* (manuscript, sha256 e91e8127…), §2, pp.3–4
(PDF 5–6): the learning protocol, the stochastic setting, the regret `R_T(𝒜, 𝒟)`, the expected
profit `µ`, its optimum `µ⋆`, Definition 2.3 (MHR) and the loss `L = −log µ` of Proposition 3.2.

The trade model (`Trades`, `profit`, `Ptrade`, `muP`) is the published `BilateralProfit.Model`.
The independent seller/buyer laws with densities strictly positive on their supports are the
published `MechanismDesign.BilateralTrade.Environment`; this paper's class is the case
`loS = loB = 0`, `hiS = hiB = 1` (`UnitSupport`), and its valuation law is `E.prior`.

**Formalization Note.** Price pairs and valuation pairs are points of `ℝ × ℝ` (seller first).
Rounds are `Fin T` (0-based). A randomized algorithm is a seed `ω` drawn once from a probability
space `(Ω, P)` and, in each round `t`, a price pair that is a function of the seed and of the
feedback of rounds `< t` (its past prices are functions of these, so they are not passed).
The feedback of a round is the pair of bits `(1{s ≤ p}, 1{q ≤ b})`; a *one-bit* algorithm reads
each past pair only through the product `z = 1{s ≤ p}·1{q ≤ b}`. The valuations of the `T`
rounds are i.i.d. with law `D`, independent of the seed. Logarithms are natural. -/

/-- The supports of the seller's and the buyer's values are both `[0, 1]` (§2, p.4: "strictly
positive probability densities `f_s` and `f_b` on `[0, 1]`"). -/
def UnitSupport (E : Environment) : Prop :=
  E.loS = 0 ∧ E.hiS = 1 ∧ E.loB = 0 ∧ E.hiB = 1

/-- **Definition 2.3 (MHR)**, p.4 (PDF 6), for both agents: the seller's hazard rate
`f_s/F_s` is nonincreasing on `(0, 1]` and the buyer's hazard rate `f_b/(1 − F_b)` is
nondecreasing on `[0, 1)`. The condition is imposed on the density functions `fS`, `fB` of the
environment, pointwise, as the paper's `ψ`, `ϕ` and hazard rates are. -/
def IsMHR (E : Environment) : Prop :=
  AntitoneOn (fun x => E.fS x / E.cdfS x) (Set.Ioc 0 1) ∧
    MonotoneOn (fun y => E.fB y / (1 - E.cdfB y)) (Set.Ico 0 1)

/-- The square `[0, 1]²` of price pairs. -/
def unitSq : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- The interior `{(p, q) : 0 < p < q < 1}` of the triangle `𝒯 = {(p, q) ∈ [0,1]² : p ≤ q}`. -/
def intT : Set (ℝ × ℝ) := {a | 0 < a.1 ∧ a.1 < a.2 ∧ a.2 < 1}

/-- The optimal expected profit `µ⋆ = sup_{(p,q) ∈ [0,1]²} µ(p, q)` (p.4). The set is nonempty and
bounded (`|µ| ≤ 1`), so this is the true supremum (attained on `𝒯`, p.4). -/
noncomputable def muStar (D : Measure (ℝ × ℝ)) : ℝ := sSup (muP D '' unitSq)

/-- The loss `L(p, q) = −log µ(p, q)` of Proposition 3.2 (p.11). Only used where `µ > 0`. -/
noncomputable def lossL (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : ℝ := -Real.log (muP D a)

/-- The two feedback bits `(1{s ≤ p}, 1{q ≤ b})` of a round with valuations `v = (s, b)` and
prices `a = (p, q)`; their product is the trade bit `z`. -/
noncomputable def feedback (v a : ℝ × ℝ) : Bool × Bool := (decide (v.1 ≤ a.1), decide (a.2 ≤ v.2))

/-- A randomized, non-anticipating pricing algorithm for horizon `T` with seed space `Ω`: in round
`t` it posts `price t ω h ∈ [0,1]²`, where `ω` is the seed and `h` the feedback of rounds `< t`.
Measurable in the seed for every fixed history. -/
structure Policy (T : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  /-- the price pair posted in round `t` given the seed and the past feedback -/
  price : (t : Fin T) → Ω → (Fin t → Bool × Bool) → ℝ × ℝ
  price_mem : ∀ t ω h, price t ω h ∈ unitSq
  price_measurable : ∀ t h, Measurable fun ω => price t ω h

variable {T : ℕ} {Ω : Type} [MeasurableSpace Ω]

/-- One-bit feedback (p.4: "the learner receives only the trade bit `z_t`"): the prices depend on
each past round's feedback only through the trade bit `z = 1{s ≤ p}·1{q ≤ b}`. -/
def Policy.OneBit (π : Policy T Ω) : Prop :=
  ∀ (t : Fin T) (ω : Ω) (h h' : Fin t → Bool × Bool),
    (∀ i, ((h i).1 && (h i).2) = ((h' i).1 && (h' i).2)) → π.price t ω h = π.price t ω h'

/-- The feedback history of the first `t` rounds of the run with seed `ω` and valuations `v`. -/
noncomputable def Policy.hist (π : Policy T Ω) (ω : Ω) (v : Fin T → ℝ × ℝ) :
    (t : ℕ) → t ≤ T → (Fin t → Bool × Bool)
  | 0, _ => Fin.elim0
  | t + 1, ht =>
      Fin.snoc (α := fun _ => Bool × Bool) (π.hist ω v t (Nat.le_of_succ_le ht))
        (feedback (v ⟨t, ht⟩) (π.price ⟨t, ht⟩ ω (π.hist ω v t (Nat.le_of_succ_le ht))))

/-- The price pair `(p_t, q_t)` posted in round `t` of the run with seed `ω` and valuations `v`. -/
noncomputable def Policy.runPrice (π : Policy T Ω) (ω : Ω) (v : Fin T → ℝ × ℝ) (t : Fin T) :
    ℝ × ℝ :=
  π.price t ω (π.hist ω v t t.isLt.le)

/-- The law of the run: the seed `ω ∼ P`, independent of the i.i.d. valuations `v_t ∼ D`. -/
noncomputable def runLaw (T : ℕ) (P : Measure Ω) (D : Measure (ℝ × ℝ)) :
    Measure (Ω × (Fin T → ℝ × ℝ)) :=
  P.prod (Measure.pi fun _ : Fin T => D)

/-- `E[Profit_t(p_t, q_t)]`: the expected profit of the algorithm in round `t`, over the seed and
the valuations. -/
noncomputable def Policy.expProfit (π : Policy T Ω) (P : Measure Ω) (D : Measure (ℝ × ℝ))
    (t : Fin T) : ℝ :=
  ∫ x, profit (x.2 t) (π.runPrice x.1 x.2 t) ∂(runLaw T P D)

/-- `E[Profit_t(p, q)]`: the expected profit of the fixed price pair `a = (p, q)` in a round. -/
noncomputable def fixedProfit (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : ℝ :=
  ∫ v, profit v a ∂D

/-- `∑_{t=1}^T E[Profit_t(p, q) − Profit_t(p_t, q_t)]`, the regret against the comparator `a`;
`R_T(𝒜, 𝒟)` (p.4) is its supremum over `a ∈ [0,1]²`. -/
noncomputable def Policy.regret (π : Policy T Ω) (P : Measure Ω) (D : Measure (ℝ × ℝ))
    (a : ℝ × ℝ) : ℝ :=
  ∑ t : Fin T, (fixedProfit D a - π.expProfit P D t)

end BilateralProfitMHR


