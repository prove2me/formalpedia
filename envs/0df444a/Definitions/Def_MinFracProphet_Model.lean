-- Prove2me | Definitions.Def_MinFracProphet_Model
-- name    : MinFracProphet_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:46.595837+00:00
-- url     : https://prove2.me/theorems/0fb0daae-dbcc-437f-9d89-24b881307837
-- title:
--   The minimization fractional prophet problem with in-house production: $\mathrm{OPT}$, policies, $\mathrm{CR}_{\text{in-house}}$, the NA value (8) and the power mean $M_q$
-- statement:
--   These are the objects of the minimization fractional prophet inequality of Qin, Vardi and Wierman (§1.2, pp.3–4; §3, pp.11–12).
--
--   A buyer must procure one unit of a divisible commodity from $n\ge1$ sellers who arrive in sequence. Seller $i$ quotes a random price coefficient $C_i$, and buying the amount $x_i\in[0,1]$ from seller $i$ costs $C_ix_i^p$, with $p>1$. The prices $C_1,\dots,C_n$ are independent, $C_i\sim D_i$.
--
--   1. **Feasible allocations and the prophet's cost** (2), p.3. The feasible allocations are $\Delta_n=\{x\in[0,1]^n:\sum_{i}x_i=1\}$. For prices $c\in\mathbb R^n$,
--   $$
--   \mathrm{OPT}(c,p)=\inf_{x\in\Delta_n}\sum_{i=1}^n c_ix_i^p .
--   $$
--   2. **Policies** (p.3). A policy decides $x_i=\pi_i(c_1,\dots,c_i)\in[0,1]$ after seeing the prices up to and including $c_i$, with $\sum_i x_i=1$. Its cost is $\mathrm{ALG}^\pi(c,p)=\sum_i c_ix_i^p$ (1).
--   3. **Instances with in-house production** (pp.3–4). Seller $1$ is the buyer's own production at the constant price $1$ ($\mathbb P[C_1=1]=1$); the laws $D_2,\dots,D_n$ are arbitrary probability distributions on $\mathbb R$ with support in $[\ell,\infty)$.
--   4. **Competitive ratio with in-house production** (p.3):
--   $$
--   \mathrm{CR}_{\text{in-house}}(F,n)=\inf_{\pi}\ \sup_{D_2,\dots,D_n\in\mathcal D}\frac{\mathbb E[\mathrm{ALG}^\pi(C,p)]}{\mathbb E[\mathrm{OPT}(C,p)]}.
--   $$
--   The infimum over policies is outside the supremum over the distributions: the policy may not depend on them.
--   5. **The non-adaptive value** (8), p.11: $\min_{x\in\Delta_n}\sum_i x_i^p\,\mathbb E[C_i]$, the expected cost of the non-adaptive algorithm NA, which fixes its purchases in advance.
--   6. **Power mean** (p.12): for positive reals $c_1,\dots,c_n$ and $q\ne0$, $M_q(c)=\bigl(\tfrac1n\sum_{i=1}^n c_i^q\bigr)^{1/q}$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Sellers are `Fin n`; Lean's seller `0` is the paper's seller $1$, the in-house option. A policy is a family of measurable maps `x i : (Fin n → ℝ) → ℝ` on all of $\mathbb R^n$ that depend only on $c_0,\dots,c_i$, take values in $[0,1]$ and sum to $1$ for every price vector (`IsPolicy`); a policy defined on the supports extends to $\mathbb R^n$ without changing its cost. An instance (`IsInHouseInstance`) is a family of probability measures with `ν 0 = dirac 1` and $\nu_i((-\infty,\ell))=0$ for $i\ne0$; no moment condition is imposed. The joint law is the product measure `Measure.pi ν`. Expectations are lower Lebesgue integrals in $[0,\infty]$, and the ratio is computed in $[0,\infty]$, so $\mathbb E[\mathrm{ALG}^\pi]=\infty$ is allowed. $\mathrm{OPT}$ is the real infimum (Lemma 1 shows it is attained for positive prices); in the NA value the product $x_i^p\cdot\mathbb E[C_i]$ is taken in $[0,\infty]$, which is the paper's convention $0\cdot\infty=0$.
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), §1.2, pp.3–4: (1), (2), CR(F,n) and CR_in-house(F,n); §3, p.11: (8); p.12: power mean M_q

import Mathlib

open MeasureTheory

namespace MinFracProphet

/-! # The minimization fractional prophet inequality with in-house production

J. Qin, S. Vardi, A. Wierman, *Minimization Fractional Prophet Inequalities for Sequential
Procurement*, author manuscript (INFORMS template, sha256 672fa87c…79125d3), §1.2, pp.3–4
(model, (1), (2), CR_in-house), §3, pp.11–12 (algorithm NA (8), power mean `M_q`).

**Formalization Note**
* Sellers are `Fin n`; Lean's seller `0` is the paper's seller `1`, the in-house option (R2).
* A policy is a family of measurable, non-anticipative maps `x i : (Fin n → ℝ) → ℝ` on all of
  `ℝ^n` with values in `[0,1]` summing to `1` (R3). The paper's `π_i` live on the supports
  `𝒞_1 × ⋯ × 𝒞_i`; every such policy extends to `ℝ^n` with the same cost on every instance.
  Measurability is the standing convention under which `E[ALG_π]` is defined.
* Expectations are lower Lebesgue integrals (`lintegral`) of `ENNReal.ofReal` of the cost, and the
  competitive ratio is computed in `ℝ≥0∞` (R4); `E[ALG_π] = ∞` is allowed.
* "Support contained in `[ℓ,∞)`" is `ν (Set.Iio ℓ) = 0`, with no moment condition (R5).
* The independent prices `C_1, …, C_n` have the product law `Measure.pi ν`. -/

/-- The feasible allocations of (2), p.3: `x ∈ [0,1]^n` with `∑ i, x i = 1`. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = 1}

/-- The procurement cost `∑_i c_i x_i^p` of the allocation `x` at prices `c` ((1) and (2), p.3).
`x i ^ p` is `Real.rpow`; allocations are in `[0,1]`. -/
noncomputable def procCost {n : ℕ} (p : ℝ) (c x : Fin n → ℝ) : ℝ :=
  ∑ i, c i * x i ^ p

/-- The prophet's cost `OPT(c,p)`, the optimal value of (2), p.3 (minimum over `x`; the page's
"min over c" is a typo). Written as the real infimum of the cost over the feasible set; Lemma 1
(`lemma_1`) shows it is attained for positive prices. -/
noncomputable def OPT {n : ℕ} (p : ℝ) (c : Fin n → ℝ) : ℝ :=
  sInf (procCost p c '' simplex n)

/-- The cost `ALG^π(c,p) = ∑_i c_i x_i^p` of a policy, (1), p.3, where `x_i = π_i(c_1,…,c_i)`. -/
noncomputable def ALG {n : ℕ} (p : ℝ) (x : Fin n → (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) : ℝ :=
  procCost p c (fun i => x i c)

/-- A (deterministic, causal) policy, p.3: `x i c` is the amount bought from seller `i`; it is
measurable, depends only on the prices `c_0, …, c_i` seen so far (the current price included),
lies in `[0,1]`, and the amounts sum to `1` for every price vector. -/
structure IsPolicy (n : ℕ) (x : Fin n → (Fin n → ℝ) → ℝ) : Prop where
  measurable : ∀ i, Measurable (x i)
  nonanticipative : ∀ i (c c' : Fin n → ℝ), (∀ j, j ≤ i → c j = c' j) → x i c = x i c'
  nonneg : ∀ i c, 0 ≤ x i c
  le_one : ∀ i c, x i c ≤ 1
  sum_eq_one : ∀ c, ∑ i, x i c = 1

/-- An instance with in-house production, pp.3–4 and Theorem 2: every seller's price law is a
probability measure on `ℝ`; seller `0` (the paper's seller 1) has the point mass at `1`
(`ℙ[C_1 = 1] = 1`), and every other seller's law has support in `[ℓ, ∞)`, i.e. gives no mass to
`(-∞, ℓ)`. No moment condition is imposed (infinite means are allowed). -/
structure IsInHouseInstance (n : ℕ) (ℓ : ℝ) (ν : Fin n → Measure ℝ) : Prop where
  prob : ∀ i, IsProbabilityMeasure (ν i)
  inHouse : ∀ h : 0 < n, ν ⟨0, h⟩ = Measure.dirac 1
  support : ∀ i : Fin n, i.val ≠ 0 → ν i (Set.Iio ℓ) = 0

/-- `E[ALG^π(C,p)]` for independent prices `C_i ∼ ν i`, as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def EALG {n : ℕ} (p : ℝ) (x : Fin n → (Fin n → ℝ) → ℝ) (ν : Fin n → Measure ℝ) :
    ENNReal :=
  ∫⁻ c, ENNReal.ofReal (ALG p x c) ∂(Measure.pi ν)

/-- `E[OPT(C,p)]` for independent prices `C_i ∼ ν i`, as a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def EOPT {n : ℕ} (p : ℝ) (ν : Fin n → Measure ℝ) : ENNReal :=
  ∫⁻ c, ENNReal.ofReal (OPT p c) ∂(Measure.pi ν)

/-- The competitive ratio with in-house production, p.3:
`CR_in-house(F,n) = inf_π sup_{D_2,…,D_n ∈ 𝒟} E[ALG^π(C,p)] / E[OPT(C,p)]`, with `𝒟` the
distributions supported in `[ℓ,∞)`. The infimum over policies is outside the supremum over
instances: the policy may depend on `n`, `p`, `ℓ`, not on the distributions. -/
noncomputable def CRinHouse (n : ℕ) (p ℓ : ℝ) : ENNReal :=
  ⨅ (x : Fin n → (Fin n → ℝ) → ℝ) (_ : IsPolicy n x),
    ⨆ (ν : Fin n → Measure ℝ) (_ : IsInHouseInstance n ℓ ν), EALG p x ν / EOPT p ν

/-- The value of the non-adaptive problem (8), p.11: `min_{x ∈ simplex} E[∑_i C_i x_i^p]
= min_x ∑_i x_i^p E[C_i]`, computed in `ℝ≥0∞` with `E[C_i] = ∫⁻ ofReal c ∂ν_i`. Since
`x_i^p = 0` iff `x_i = 0`, the product implements the paper's convention `0 · ∞ = 0` (p.12). -/
noncomputable def NAvalue {n : ℕ} (p : ℝ) (ν : Fin n → Measure ℝ) : ENNReal :=
  ⨅ x ∈ simplex n, ∑ i, ENNReal.ofReal (x i ^ p) * ∫⁻ c, ENNReal.ofReal c ∂(ν i)

/-- The power mean `M_q(c) = ((1/n) ∑_{i=1}^n c_i^q)^{1/q}`, p.12, of a vector of (positive) reals. -/
noncomputable def powerMean {n : ℕ} (q : ℝ) (c : Fin n → ℝ) : ℝ :=
  ((1 / (n : ℝ)) * ∑ i, c i ^ q) ^ (1 / q)

end MinFracProphet


