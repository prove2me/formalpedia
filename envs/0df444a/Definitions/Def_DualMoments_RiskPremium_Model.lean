-- Prove2me | Definitions.Def_DualMoments_RiskPremium_Model
-- name    : DualMoments_RiskPremium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:53.993311+00:00
-- url     : https://prove2.me/theorems/8eef56b0-5324-4ce0-b31c-b5b3b5e40fca
-- title:
--   §2–§4, pp. 3–8 — finite lotteries, the RDU/DT evaluation (4.1)/(3.1), unconditional variance and maxiance, the lotteries A, B, C, D
-- statement:
--   The model of Eeckhoudt and Laeven, *Dual Moments and Risk Attitudes*, §2–§4.
--
--   **Finite lotteries.** A lottery (or risk) with $n$ states lists outcomes $x_1 \le x_2 \le \dots \le x_n$ in increasing order together with unconditional probability masses $\pi_1, \dots, \pi_n$. The masses need not sum to one: the risks $\tilde\varepsilon_1$ and $\tilde\varepsilon_{12}$ below are *sub-probability* risks, effective only on an intermediate branch of a lottery. Write $F_i = \pi_1 + \dots + \pi_i$ for the cumulative mass up to and including state $i$, and $F_{i-1}$ for the mass strictly before it ($F_0 = 0$).
--
--   **Evaluation.** A rank-dependent utility (RDU) decision-maker with utility $U$ and probability weighting function $h$ evaluates a lottery with cumulative distribution function $F$ by (4.1):
--   $$\int U(x)\,\mathrm dh(F(x)) \;=\; \sum_{i=1}^n U(x_i)\,\bigl(h(F_i) - h(F_{i-1})\bigr).$$
--   Cumulative (not decumulative) probabilities are distorted (footnote 13). The dual-theory (DT) evaluation (3.1) is the case $U(x) = x$.
--
--   **Moments.** The total unconditional mass is $\Pr = \sum_i \pi_i$, the mean is $m = \sum_i \pi_i x_i = \int x\,\mathrm dF(x)$, the unconditional variance is
--   $$m_2 = \int (x - m)^2\,\mathrm dF(x) = \sum_i \pi_i (x_i - m)^2,$$
--   and the unconditional **maxiance** (second dual moment about the mean, p. 3) is
--   $$\bar m_2 = \int (x - m)\,\mathrm d(F(x))^2 = \sum_i (x_i - m)\bigl(F_i^2 - F_{i-1}^2\bigr).$$
--
--   **Lotteries.** With initial wealth $w_0$ added to every outcome (as in (3.2) and (4.2)):
--   1. $A$: $w_0 - 1$ with probability $p_0$, $w_0 + 1$ with probability $1 - p_0$ (Figure 1);
--   2. $B$: $w_0 - 1$ with $p_0 - \varepsilon_1$, $w_0 + x$ with $2\varepsilon_1$, $w_0 + 1$ with $1 - p_0 - \varepsilon_1$ (Figure 2);
--   3. $C$: $w_0 - \varepsilon_2$ with $p_0$, $w_0 + \varepsilon_2$ with $1 - p_0$ (Figure 4);
--   4. $D$: $w_0 - \varepsilon_2$ with $p_0 - \varepsilon_1$, $w_0 + y$ with $2\varepsilon_1$, $w_0 + \varepsilon_2$ with $1 - p_0 - \varepsilon_1$ (Figure 5).
--
--   The risk $\tilde\varepsilon_1$ takes the values $\pm1$, and $\tilde\varepsilon_{12}$ the values $\pm\varepsilon_2$, each with unconditional probability $\varepsilon_1$.
--
--   **Standing assumptions.** $U$ is twice continuously differentiable with $U' > 0$ (footnote 1). The weighting function $h : [0,1] \to [0,1]$ is twice continuously differentiable on $[0,1]$ with $h(0) = 0$, $h(1) = 1$ and $h' > 0$ (p. 5, footnote 12). The parameters satisfy $0 < p_0 < 1$ (footnote 15) and $0 < \varepsilon_1 < \min\{p_0, 1 - p_0\}$ (footnote 16); the predicate *Feasible* collects these.
--
--   **Risk premia.** A number $\rho$ is a DT risk premium if $x = 0 - \rho$ satisfies $-1 < x < 1$ and the DT decision-maker is indifferent between $A$ and $B$ (p. 5). A number $\lambda$ is an RDU risk premium if $y = 0 - \lambda$ satisfies $-\varepsilon_2 < y < \varepsilon_2$ and the RDU decision-maker is indifferent between $C$ and $D$ (pp. 7–8).
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** All quantities are real numbers; a lottery is a pair of vectors indexed by $\mathrm{Fin}\,n$. The finite-sum evaluation equals the Stieltjes integral (4.1) only when outcomes are listed in increasing order, so the premium predicates keep the page's ranges $-1 < x < 1$ and $-\varepsilon_2 < y < \varepsilon_2$, which make $B$ and $D$ ordered. $h$ is a function $\mathbb R \to \mathbb R$ whose values matter only on $[0,1]$; its positive derivative is the one-sided derivative within $[0,1]$, so that it is meaningful at the endpoints. The requirement that $h$ maps $[0,1]$ into $[0,1]$ is stated, although it follows from the other properties.
-- source:
--   Eeckhoudt & Laeven, Dual Moments and Risk Attitudes, arXiv:1612.03347v2, §2–§4, pp. 3–8, (2.1) and the Stieltjes forms p. 3, (3.1) p. 4, (4.1) p. 8, Figures 1, 2, 4, 5 (pp. 5, 7), footnotes 1 (p. 2), 12, 13, 15, 16 (p. 5), 19 (p. 7)

import Mathlib

namespace DualMoments.RiskPremium

/-- A finite (sub-probability) lottery or risk with `n` states: outcomes `outcome i`, listed in
increasing order, and unconditional probability masses `prob i`. -/
structure Lottery (n : ℕ) where
  outcome : Fin n → ℝ
  prob : Fin n → ℝ

variable {n : ℕ}

/-- The cumulative mass `F(xᵢ) = π₁ + ⋯ + πᵢ` up to and including state `i`. -/
def Lottery.cum (L : Lottery n) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (· ≤ i), L.prob j

/-- The cumulative mass `F(xᵢ⁻) = π₁ + ⋯ + π_{i−1}` strictly before state `i`. -/
def Lottery.cumBefore (L : Lottery n) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (· < i), L.prob j

/-- The rank-dependent evaluation (4.1) `∫ U(x) dh(F(x))` of a lottery whose outcomes are listed in
increasing order: `∑ᵢ U(xᵢ) (h(F(xᵢ)) − h(F(xᵢ⁻)))`. The dual-theory evaluation (3.1) is `U = id`. -/
def rduValue (U h : ℝ → ℝ) (L : Lottery n) : ℝ :=
  ∑ i, U (L.outcome i) * (h (L.cum i) - h (L.cumBefore i))

/-- The total unconditional probability mass `Pr = ∑ᵢ πᵢ`. -/
def Lottery.mass (L : Lottery n) : ℝ := ∑ i, L.prob i

/-- The unconditional mean `m = ∫ x dF(x) = ∑ᵢ πᵢ xᵢ`. -/
def Lottery.mean (L : Lottery n) : ℝ := ∑ i, L.prob i * L.outcome i

/-- The unconditional variance `m₂ = ∫ (x − m)² dF(x) = ∑ᵢ πᵢ (xᵢ − m)²`. -/
def Lottery.variance (L : Lottery n) : ℝ := ∑ i, L.prob i * (L.outcome i - L.mean) ^ 2

/-- The unconditional maxiance (second dual moment about the mean)
`m̄₂ = ∫ (x − m) d(F(x))² = ∑ᵢ (xᵢ − m)(F(xᵢ)² − F(xᵢ⁻)²)`, for outcomes in increasing order. -/
def Lottery.maxiance (L : Lottery n) : ℝ :=
  ∑ i, (L.outcome i - L.mean) * (L.cum i ^ 2 - L.cumBefore i ^ 2)

/-- Lottery `A` (Figure 1) shifted by initial wealth `w0`: `w0 − 1` w.p. `p0`, `w0 + 1` w.p. `1 − p0`. -/
def lotA (p0 w0 : ℝ) : Lottery 2 := ⟨![w0 - 1, w0 + 1], ![p0, 1 - p0]⟩

/-- Lottery `B` (Figure 2) shifted by `w0`: `w0 − 1` w.p. `p0 − ε₁`, `w0 + x` w.p. `2ε₁`,
`w0 + 1` w.p. `1 − p0 − ε₁`. -/
def lotB (p0 ε₁ w0 x : ℝ) : Lottery 3 :=
  ⟨![w0 - 1, w0 + x, w0 + 1], ![p0 - ε₁, 2 * ε₁, 1 - p0 - ε₁]⟩

/-- Lottery `C` (Figure 4) shifted by `w0`: `w0 − ε₂` w.p. `p0`, `w0 + ε₂` w.p. `1 − p0`. -/
def lotC (p0 ε₂ w0 : ℝ) : Lottery 2 := ⟨![w0 - ε₂, w0 + ε₂], ![p0, 1 - p0]⟩

/-- Lottery `D` (Figure 5) shifted by `w0`: `w0 − ε₂` w.p. `p0 − ε₁`, `w0 + y` w.p. `2ε₁`,
`w0 + ε₂` w.p. `1 − p0 − ε₁`. -/
def lotD (p0 ε₁ ε₂ w0 y : ℝ) : Lottery 3 :=
  ⟨![w0 - ε₂, w0 + y, w0 + ε₂], ![p0 - ε₁, 2 * ε₁, 1 - p0 - ε₁]⟩

/-- The risk `ε̃₁` (Figure 3), unconditionally: `±1`, each with probability `ε₁`. -/
def risk1 (ε₁ : ℝ) : Lottery 2 := ⟨![-1, 1], ![ε₁, ε₁]⟩

/-- The risk `ε̃₁₂` (§4), unconditionally: `±ε₂`, each with probability `ε₁`. -/
def risk12 (ε₁ ε₂ : ℝ) : Lottery 2 := ⟨![-ε₂, ε₂], ![ε₁, ε₁]⟩

/-- Footnote 1: the utility `U` is twice continuously differentiable with positive first
derivative. -/
def UtilityStanding (U : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 U ∧ ∀ w, 0 < deriv U w

/-- p. 5 and footnote 12: the probability weighting function `h : [0, 1] → [0, 1]` is twice
continuously differentiable on `[0, 1]`, with `h(0) = 0`, `h(1) = 1` and `h′(p) > 0` (one-sided at
the endpoints). -/
def WeightingStanding (h : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 h (Set.Icc 0 1) ∧ Set.MapsTo h (Set.Icc 0 1) (Set.Icc 0 1) ∧
    h 0 = 0 ∧ h 1 = 1 ∧ ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 < derivWithin h (Set.Icc 0 1) p

/-- Footnotes 15 and 16: `0 < p0 < 1` and `0 < ε₁ < min {p0, 1 − p0}`. -/
def Feasible (p0 ε₁ : ℝ) : Prop :=
  0 < p0 ∧ p0 < 1 ∧ 0 < ε₁ ∧ ε₁ < min p0 (1 - p0)

/-- `ρ` is a DT risk premium (§3, p. 5): `x = 0 − ρ` lies in `(−1, 1)` and the DT decision-maker
with weighting function `h` and initial wealth `w0` is indifferent between `A` and `B`. -/
def IsDTPremium (h : ℝ → ℝ) (p0 w0 ε₁ ρ : ℝ) : Prop :=
  -1 < -ρ ∧ -ρ < 1 ∧ rduValue id h (lotA p0 w0) = rduValue id h (lotB p0 ε₁ w0 (-ρ))

/-- `lam` is an RDU risk premium (§4, pp. 7–8): `y = 0 − λ` lies in `(−ε₂, ε₂)` and the RDU
decision-maker `(U, h)` with initial wealth `w0` is indifferent between `C` and `D`. -/
def IsRDUPremium (U h : ℝ → ℝ) (p0 w0 ε₁ ε₂ lam : ℝ) : Prop :=
  -ε₂ < -lam ∧ -lam < ε₂ ∧ rduValue U h (lotC p0 ε₂ w0) = rduValue U h (lotD p0 ε₁ ε₂ w0 (-lam))

end DualMoments.RiskPremium


