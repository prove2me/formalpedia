-- Prove2me | Definitions.Def_HiddenRebate_Fixed_Model
-- name    : HiddenRebate_Fixed_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:17:20.118727+00:00
-- url     : https://prove2.me/theorems/0ea66325-7302-4a32-bffd-90d8a5987d4b
-- title:
--   §3, §5.1, pp. 6–12 — hidden-rebate procurement: iid costs, quotes, deterministic contracts ⟨A, F⟩, payoff (1), IC (13), cost (14), r̄ (fn. 15), contract (15)
-- statement:
--   **Hidden-rebate procurement with partial verification** (Fan, Chen & Tang, §3 and §5.1).
--
--   A retailer buys through an intermediary from two manufacturers: $S$, known to be ethical, and $W$, who pays the intermediary a hidden rebate $r \ge 0$ whenever $W$ wins the order. The manufacturers' original prices $x_S, x_W \ge 0$ are independent draws from a common distribution $\mu$ with a density $g$ on $[0,\infty)$; $\bar G(t) = \mu((t,\infty))$ is its survival function. The true quotes are
--   $$q = (q_S, q_W) = (x_S,\; x_W + r).$$
--
--   1. **Contracts.** A deterministic contract $\langle A, F\rangle$ consists of a selection rule $A : \mathbb R^2 \to \{S, W\}$ and a service fee $F : \mathbb R^2 \to \mathbb R$, both functions of the intermediary's reported quotes $z = (z_S, z_W)$. It is *admissible* when $F \ge 0$ (p. 8) and the region $\{A = S\}$ and the fee $F$ are measurable. Write $z_{A(z)}$ for the reported quote of the selected manufacturer.
--   2. **Payoff (1).** Reporting $z$ when the true quotes are $q$ earns the intermediary
--   $$\pi(z; \langle A,F\rangle) = \big(r\,\mathbf 1_{A(z)=W} + F(z)\big)\,\mathbf 1_{z_{A(z)} = q_{A(z)}},$$
--   since the retailer verifies only the selected manufacturer's quote and pays nothing after a failed check.
--   3. **Incentive compatibility (13).** $\langle A,F\rangle$ is IC when, for every cost pair $x_S, x_W \ge 0$ and every report $z \in \mathbb R^2$, $\pi(q; \langle A,F\rangle) \ge \pi(z; \langle A,F\rangle)$ with $q = (x_S, x_W + r)$. The inequality is weak: an indifferent intermediary reports truthfully (p. 7).
--   4. **Retailer's cost (14).** Under truthful reporting the retailer pays $q_{A(q)} + F(q)$, and
--   $$E\,C(q;\langle A,F\rangle) = \int \big(q_{A(q)} + F(q)\big)\, g(q)\, dq,$$
--   written as an integral over the costs $(x_S, x_W) \sim \mu \otimes \mu$.
--   5. **The contract (15).** $A^*(z) = S$ if $z_S \le z_W - r$ and $W$ otherwise; $F^*(z) = r$ if $A^*(z) = S$ and $0$ otherwise.
--   6. **The threshold $\bar r$ (footnote 15).**
--   $$\bar r = \min\Big\{ \inf_{a>0,\,T\ge a} \frac{E\big((x_S-x_W)\mathbf 1_{x_S>x_W>T}\big) + E\big((x_W-x_S)\mathbf 1_{T>x_W>x_S>a}\big)}{\bar G(T)\,\bar G(a)},\ \inf_{T\ge 0} \Big[E\big(x_W \mathbf 1_{x_W<T}\big) + E(x_S)\,\bar G(T) - E\big(\min\{x_S,x_W\}\big)\Big] \Big\}.$$
--
--   These objects are shared by every statement of the mission: Theorem 1 says that for $r < \bar r$ the contract (15) is IC and minimizes (14) over all admissible IC contracts.
--
--   **Formalization Note** The standing assumptions are bundled in `Standing μ r`: $\mu$ is a probability measure, $\mu((-\infty,0)) = 0$, $\mu \ll$ Lebesgue (the density $g$), and two disclosed additions, $E[x_S] < \infty$ and $r \ge 0$. Reports range over all of $\mathbb R^2$. The cost (14) is a Bochner integral over $\mu \otimes \mu$ with the contract evaluated at $q = (x_S, x_W + r)$. Each "min" of footnote 15 is read as an infimum (`sInf`), and pairs $(a, T)$ with $\bar G(T)\bar G(a) = 0$ are excluded from the first infimum so that no division by zero enters. The second term is stated exactly as printed (not divided by $\bar G(T)$).
-- source:
--   Fan, Chen & Tang, Mechanism design for managing hidden rebates and inflated quotes of a procurement service provider, SSRN preprint 3514358, pp. 6–12, §3, §5.1, (1), (13), (14), (15), footnote 15

import Mathlib

namespace HiddenRebate.Fixed

open MeasureTheory

/-- The two manufacturers: `S` (designated, ethical) and `W` (unethical, pays the hidden rebate). -/
inductive Supplier
  | S
  | W
  deriving DecidableEq

/-- Standing assumptions of §3 (pp. 6–8) on the common cost law `μ` of `xS, xW` and the rebate `r`:
`μ` is a probability law with a density (`μ ≪ volume`) on `[0, ∞)`; added: `E[xS] < ∞` and `0 ≤ r`. -/
def Standing (μ : Measure ℝ) (r : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ μ ≪ volume ∧ Integrable id μ ∧ 0 ≤ r

/-- True quotes from costs: `(qS, qW) = (xS, xW + r)` (p. 7). -/
def quote (r : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1, x.2 + r)

/-- The coordinate of supplier `s` in a pair of quotes: `z_S = z.1`, `z_W = z.2`. -/
def sel (s : Supplier) (z : ℝ × ℝ) : ℝ :=
  match s with
  | .S => z.1
  | .W => z.2

/-- Ex post payoff (1) of the intermediary reporting `z` when the true quotes are `q`:
`π(z; ⟨A, F⟩) = (r · 1[A(z) = W] + F(z)) · 1[z_{A(z)} = q_{A(z)}]`. -/
noncomputable def payoff (r : ℝ) (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ) (z q : ℝ × ℝ) : ℝ :=
  ((if A z = .W then r else 0) + F z) * (if sel (A z) z = sel (A z) q then 1 else 0)

/-- Truth-telling incentive compatibility (13): for every cost pair `xS, xW ≥ 0`, with true quotes
`q = (xS, xW + r)`, and every report `z ∈ ℝ²`, `π(q; q) ≥ π(z; q)`. -/
def IsIC (r : ℝ) (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ) : Prop :=
  ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 → ∀ z : ℝ × ℝ,
    payoff r A F z (quote r x) ≤ payoff r A F (quote r x) (quote r x)

/-- Admissible deterministic contracts: non-negative fee (p. 8), measurable selection region and fee. -/
def Feasible (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ) : Prop :=
  (∀ z, 0 ≤ F z) ∧ MeasurableSet {z | A z = .S} ∧ Measurable F

/-- Retailer's ex post cost under truthful reporting at cost pair `x`: `q_{A(q)} + F(q)` with
`q = (xS, xW + r)`. -/
noncomputable def costIntegrand (r : ℝ) (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  sel (A (quote r x)) (quote r x) + F (quote r x)

/-- The retailer's objective (14): `E[C(q; ⟨A, F⟩)] = ∫ (q_{A(q)} + F(q)) g(q) dq`, written as an
integral over the iid costs `(xS, xW) ∼ μ ⊗ μ`. -/
noncomputable def cost (μ : Measure ℝ) (r : ℝ) (A : ℝ × ℝ → Supplier) (F : ℝ × ℝ → ℝ) : ℝ :=
  ∫ x, costIntegrand r A F x ∂(μ.prod μ)

/-- The selection rule `A∗` of (15): `S` iff `zS ≤ zW − r` (ties to `S`). -/
noncomputable def selStar (r : ℝ) (z : ℝ × ℝ) : Supplier :=
  if z.1 ≤ z.2 - r then .S else .W

/-- The fee `F∗` of (15): `r` if `S` is selected, `0` otherwise. -/
noncomputable def feeStar (r : ℝ) (z : ℝ × ℝ) : ℝ :=
  if selStar r z = .S then r else 0

/-- The contract `⟨A∗, F∗⟩` of (15). -/
noncomputable def contractStar (r : ℝ) : (ℝ × ℝ → Supplier) × (ℝ × ℝ → ℝ) :=
  (selStar r, feeStar r)

/-- Survival function `Ḡ(t) = μ((t, ∞))`. -/
noncomputable def Gbar (μ : Measure ℝ) (t : ℝ) : ℝ := (μ (Set.Ioi t)).toReal

/-- Numerator of the first term of footnote 15:
`E((xS − xW) 1[xS > xW > T]) + E((xW − xS) 1[T > xW > xS > a])`. -/
noncomputable def rbarNum₁ (μ : Measure ℝ) (a T : ℝ) : ℝ :=
  (∫ x, (if x.1 > x.2 ∧ x.2 > T then x.1 - x.2 else 0) ∂(μ.prod μ)) +
  (∫ x, (if T > x.2 ∧ x.2 > x.1 ∧ x.1 > a then x.2 - x.1 else 0) ∂(μ.prod μ))

/-- Second term of footnote 15, as printed (not divided by `Ḡ(T)`):
`E(xW 1[xW < T]) + E(xS) Ḡ(T) − E(min{xS, xW})`. -/
noncomputable def rbarTerm₂ (μ : Measure ℝ) (T : ℝ) : ℝ :=
  (∫ y, (if y < T then y else 0) ∂μ) + (∫ y, y ∂μ) * Gbar μ T -
  ∫ x, min x.1 x.2 ∂(μ.prod μ)

/-- The threshold `r̄` of footnote 15 (p. 12), with each "min" read as an infimum and the guard
`Ḡ(T)Ḡ(a) > 0` on the first quotient. -/
noncomputable def rbar (μ : Measure ℝ) : ℝ :=
  min (sInf {ρ | ∃ a T : ℝ, 0 < a ∧ a ≤ T ∧ 0 < Gbar μ T * Gbar μ a ∧
                  ρ = rbarNum₁ μ a T / (Gbar μ T * Gbar μ a)})
      (sInf {ρ | ∃ T : ℝ, 0 ≤ T ∧ ρ = rbarTerm₂ μ T})

end HiddenRebate.Fixed


