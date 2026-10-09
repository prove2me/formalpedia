-- Prove2me | Definitions.Def_MultiItemRev_Decomp_Model
-- name    : MultiItemRev_Decomp_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:48.660554+00:00
-- url     : https://prove2.me/theorems/d173baa1-a230-4fe9-98d8-1e24f9415966
-- title:
--   §2.1, pp. 11–14 and p. 19 — mechanisms on ℝ^k_+, IC, IR, NPT, R(µ;X), Rev, SRev, BRev, product laws, X·1_A, Val
-- statement:
--   This module sets up the single-buyer, multi-good revenue maximization model of Hart and Nisan.
--
--   A seller offers a finite nonempty set $I$ of $k$ goods to one buyer whose values are additive. A **valuation** is a vector $x = (x_i)_{i \in I} \in \mathbb{R}^k_+$, and a **$k$-good random valuation** $X$ is described by its law $\mu$, a probability measure on $\mathbb{R}^k_+$.
--
--   1. A **mechanism** $M = (q, s)$ consists of an allocation $q : \mathbb{R}^k_+ \to [0,1]^k$ ($q_i(x)$ is the probability that the buyer gets good $i$) and a payment $s : \mathbb{R}^k_+ \to \mathbb{R}$. The buyer's payoff is $b(x) = q(x) \cdot x - s(x) = \sum_i q_i(x) x_i - s(x)$.
--   2. $M$ is **incentive compatible (IC)** if $b(x) \ge q(\tilde x) \cdot x - s(\tilde x)$ for all $x, \tilde x \in \mathbb{R}^k_+$; **individually rational (IR)** if $b(x) \ge 0$ for all $x$; and has **no positive transfer (NPT)** if $s(x) \ge 0$ for all $x$.
--   3. The class $\mathcal{M}$ consists of the IC and IR mechanisms with measurable payment $s$.
--   4. The **expected revenue** of $M \in \mathcal M$ from $X$ is $R(M; X) = \mathbb{E}[s(X)] \in (-\infty, +\infty]$, and the **optimal revenue** is
--   $$
--   \mathrm{Rev}(X) = \sup_{M \in \mathcal M} R(M; X) \in [0, \infty].
--   $$
--   5. The **separate** and **bundled** revenues are $\mathrm{SRev}(X) = \mathrm{Rev}(X_1) + \dots + \mathrm{Rev}(X_k)$ and $\mathrm{BRev}(X) = \mathrm{Rev}(X_1 + \dots + X_k)$, each computed in the one-good model.
--   6. For independent random valuations $Y$ (on goods $I_1$) and $Z$ (on goods $I_2$), the law of $(Y, Z)$ on $\mathbb{R}^{I_1 \sqcup I_2}_+$ is the product of their laws. For a set $A$, the law of $X \mathbf{1}_{X \in A}$ is the image of the law of $X$ under $x \mapsto x\,\mathbf 1_{x \in A}$.
--   7. $\mathrm{Val}(X) = \mathbb{E}[\sum_i X_i] \in [0, \infty]$. For $x = (y, z)$ the module also names $\sum_i y_i$, $\sum_j z_j$ and the block $z$.
--
--   These definitions support the paper's revenue comparisons, including Theorem 7 for two independent groups of goods.
--
--   **Formalization Note** A random valuation is represented by its law `μ : Measure (ι → ℝ≥0)`, since every quantity of the paper depends on $X$ only through its distribution; one good is `ι = Unit`. The module allows an empty finite index type, while statements corresponding to the paper's $k\ge1$ setting must use a nonempty type. Measurability of $s$ is part of the class $\mathcal M$ (`IsAdmissible`), as footnote 12 of the paper allows without loss of generality (Hart and Reny 2015a, Prop. 16); $q$ is not required to be measurable. $R(M;X)$ is computed in `EReal` as $\int s^+ - \int s^-$ with lower Lebesgue integrals, so that $\mathbb{E}[s(X)] = +\infty$ is represented; for an IC mechanism $s \ge s(0)$, so the negative part is finite. `Rev` takes the supremum of `toENNReal` of these values; negative revenues are clipped to $0$, which does not change the supremum because the zero mechanism is in $\mathcal M$ with revenue $0$. `lawOn μ A` is the image law under `A.indicator id`; theorems using it assume $A$ measurable.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 11–14, §2.1 (definitions of mechanism, IC, IR, 𝓜, R(µ;X), Rev, SRev, BRev, NPT; footnote 12); p. 18 (independence of Y and Z); p. 19 (Val)

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

/-- A (direct) mechanism for the goods `ι`: allocation `q` and payment `s` (§2.1, p. 11). -/
structure Mechanism (ι : Type*) where
  q : (ι → ℝ≥0) → ι → ℝ
  s : (ι → ℝ≥0) → ℝ

/-- The buyer's payoff `b(x) = q(x) · x - s(x)` (p. 11). -/
def buyerPayoff {ι : Type*} [Fintype ι] (M : Mechanism ι) (x : ι → ℝ≥0) : ℝ :=
  ∑ i, M.q x i * (x i : ℝ) - M.s x

/-- `q : ℝ^k_+ → [0,1]^k` (p. 11). -/
def IsFeasible {ι : Type*} (M : Mechanism ι) : Prop :=
  ∀ x i, 0 ≤ M.q x i ∧ M.q x i ≤ 1

/-- Incentive compatibility (p. 12). -/
def IsIC {ι : Type*} [Fintype ι] (M : Mechanism ι) : Prop :=
  ∀ x x', ∑ i, M.q x' i * (x i : ℝ) - M.s x' ≤ buyerPayoff M x

/-- Individual rationality (p. 12). -/
def IsIR {ι : Type*} [Fintype ι] (M : Mechanism ι) : Prop :=
  ∀ x, 0 ≤ buyerPayoff M x

/-- No positive transfer (p. 14). -/
def IsNPT {ι : Type*} (M : Mechanism ι) : Prop :=
  ∀ x, 0 ≤ M.s x

/-- The class `𝓜` of IC and IR mechanisms (p. 12), with measurable payment (footnote 12). -/
def IsAdmissible {ι : Type*} [Fintype ι] (M : Mechanism ι) : Prop :=
  IsFeasible M ∧ IsIC M ∧ IsIR M ∧ Measurable M.s

/-- The expected revenue `R(µ; X) = E[s(X)]` (p. 12), in `EReal`. -/
noncomputable def expRevenue {ι : Type*} (μ : Measure (ι → ℝ≥0)) (M : Mechanism ι) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-M.s x) ∂μ : ℝ≥0∞) : EReal)

/-- The optimal revenue `Rev(X) = sup_{µ ∈ 𝓜} R(µ; X)` (p. 12). -/
noncomputable def Rev {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  ⨆ (M : Mechanism ι) (_ : IsAdmissible M), (expRevenue μ M).toENNReal

/-- A one-dimensional law, viewed as the law of a one-good valuation. -/
noncomputable def oneGood (ν : Measure ℝ≥0) : Measure (Unit → ℝ≥0) :=
  ν.map (fun t _ => t)

/-- The optimal revenue from one good with law `ν`. -/
noncomputable def Rev1 (ν : Measure ℝ≥0) : ℝ≥0∞ := Rev (oneGood ν)

/-- `SRev(X) = Rev(X₁) + ⋯ + Rev(X_k)` (p. 12). -/
noncomputable def SRev {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  ∑ i, Rev1 (μ.map (fun x => x i))

/-- `BRev(X) = Rev(X₁ + ⋯ + X_k)` (p. 13). -/
noncomputable def BRev {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  Rev1 (μ.map (fun x => ∑ i, x i))

/-- The law of `(Y, Z)` for independent `Y` (law `μY`) and `Z` (law `μZ`). -/
noncomputable def jointLaw {ι₁ ι₂ : Type*} (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0)) :
    Measure (ι₁ ⊕ ι₂ → ℝ≥0) :=
  (μY.prod μZ).map (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ≥0)).symm

/-- The law of `X · 1_{X ∈ A}` when `X` has law `μ`. -/
noncomputable def lawOn {ι : Type*} (μ : Measure (ι → ℝ≥0)) (A : Set (ι → ℝ≥0)) :
    Measure (ι → ℝ≥0) :=
  μ.map (A.indicator id)

/-- `Val(X) = E[∑ᵢ Xᵢ]` (p. 19). -/
noncomputable def Val {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  ∫⁻ x, ∑ i, (x i : ℝ≥0∞) ∂μ

/-- `∑ᵢ yᵢ` for `x = (y, z)`. -/
def sumY {ι₁ ι₂ : Type*} [Fintype ι₁] (x : ι₁ ⊕ ι₂ → ℝ≥0) : ℝ≥0 :=
  ∑ i, x (Sum.inl i)

/-- `∑ⱼ zⱼ` for `x = (y, z)`. -/
def sumZ {ι₁ ι₂ : Type*} [Fintype ι₂] (x : ι₁ ⊕ ι₂ → ℝ≥0) : ℝ≥0 :=
  ∑ j, x (Sum.inr j)

/-- The `z`-block of `x = (y, z)`. -/
def zPart {ι₁ ι₂ : Type*} (x : ι₁ ⊕ ι₂ → ℝ≥0) : ι₂ → ℝ≥0 :=
  fun j => x (Sum.inr j)

end MultiItemRev.Decomp


