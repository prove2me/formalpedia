-- Prove2me | Definitions.Def_LeviBalancing_TripleBalancing_Model
-- name    : LeviBalancing_TripleBalancing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:21:44.936407+00:00
-- url     : https://prove2.me/theorems/6ecff92c-7371-4079-bce1-627283eb5cc4
-- title:
--   §2 and §6 preamble — the stochastic lot-sizing model and its conditional demand law $I_s$
-- statement:
--   This file fixes the **stochastic lot-sizing problem** of Levi, Pál, Roundy and Shmoys (2007, §6), a periodic-review inventory model with a fixed ordering cost and correlated, nonstationary demand.
--
--   A probability space $(\Omega,\mathcal F,\mu)$ carries an information filtration $(\mathcal F_t)_t$: $\mathcal F_t$ is the information available at the beginning of period $t$ (the paper's information set $f_t$, which may contain past demands and arbitrary external information). There are $T$ periods $t=1,\dots,T$. The data are
--
--   1. a fixed ordering cost $K\ge 0$, charged in every period with a positive order (the per-unit ordering cost is $c_t=0$, the lead time is $L=0$ and there is no discounting, $\alpha=1$);
--   2. per-unit holding costs $h_t\ge0$ and backlogging penalties $p_t\ge0$;
--   3. a deterministic initial inventory level $x_1\in\mathbb R$;
--   4. nonnegative demands $D_t$, where $D_t$ is $\mathcal F_t$-measurable: the demand of period $t$ is known at the beginning of period $t$, the defining assumption of the stochastic lot-sizing problem.
--
--   The paper assumes that at the beginning of each period $s$ there is a known conditional joint distribution $I_s=I_s(f_s)$ of the demands. A family of kernels $I=(I_s)_s$ from $\Omega$ to demand paths $d=(d_t)_t\in\mathbb R^{\mathbb N}$ is a **conditional demand law** for the model when
--
--   1. each $I_s(\omega)$ is a probability measure;
--   2. $\omega\mapsto I_s(\omega)(A)$ is $\mathcal F_s$-measurable for every measurable $A$;
--   3. $I_s$ is a regular conditional distribution of the demand path given $\mathcal F_s$:
--   $$\mu\bigl(B\cap\{(D_t)_t\in A\}\bigr)=\int_B I_s(\omega)(A)\,\mu(d\omega)\qquad (B\in\mathcal F_s,\ A \text{ measurable});$$
--   4. under $I_s(\omega)$ the demand of period $s$ equals $D_s(\omega)$ almost surely ("$D_s$ is known deterministically");
--   5. under $I_s(\omega)$ all demands are nonnegative almost surely;
--   6. under $I_s(\omega)$ every $d_t$ with $1\le s\le t\le T$ is integrable, i.e. $E[D_t\mid f_s]$ is finite, the paper's only assumption on the demands.
--
--   Apart from these, the demands may be arbitrarily correlated and nonstationary, and the information is independent of the policy being used.
--
--   **Formalization Note** The conditional distributions are model data, as in the paper; properties 1, 4, 5 and 6 are required for every outcome $\omega$ rather than almost surely, which a suitable version of any regular conditional distribution satisfies. Values of the data at indices outside $1,\dots,T$ are never used.
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, pp. 288–289 (PDF 5–6), §2; p. 299 (PDF 16), §6 preamble

import Mathlib

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- The data of the stochastic lot-sizing problem of Levi, Pál, Roundy & Shmoys (2007), §2 and the
preamble of §6 (pp. 288–289, 299): a probability space `μ` with an information filtration `ℱ`
(`ℱ t` is the information available at the beginning of period `t`, i.e. the information set
`f_t`), a horizon of `T` periods numbered `1, …, T`, a fixed ordering cost `K ≥ 0` (the per-unit
ordering cost is `c_t = 0`, the lead time is `L = 0`, the discount factor is `α = 1`), holding costs
`h t ≥ 0`, backlogging penalties `p t ≥ 0`, a deterministic initial inventory level `x₁`, and
nonnegative demands `D t`.  The §6 assumption that the demand of period `t` is known at the
beginning of period `t` is `D_known`: `D t` is `ℱ t`-measurable.  Values at indices outside
`1, …, T` are never used. -/
structure LotSizingModel (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  /-- the probability measure -/
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  /-- `ℱ t`: the information available at the beginning of period `t` -/
  ℱ : Filtration ℕ mΩ
  /-- number of periods -/
  T : ℕ
  /-- fixed ordering cost -/
  K : ℝ
  K_nonneg : 0 ≤ K
  /-- per-unit holding cost of period `t` -/
  h : ℕ → ℝ
  /-- per-unit backlogging penalty of period `t` -/
  p : ℕ → ℝ
  h_nonneg : ∀ t, 0 ≤ h t
  p_nonneg : ∀ t, 0 ≤ p t
  /-- initial inventory level at the beginning of period 1 -/
  x₁ : ℝ
  /-- demand of period `t` -/
  D : ℕ → Ω → ℝ
  D_nonneg : ∀ t ω, 0 ≤ D t ω
  /-- the demand of period `t` is known at the beginning of period `t` -/
  D_known : ∀ t, Measurable[ℱ t] (D t)

attribute [instance] LotSizingModel.isProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The demand path `ω ↦ (D_t(ω))_t`. -/
def LotSizingModel.demandPath (M : LotSizingModel Ω) (ω : Ω) : ℕ → ℝ := fun t => M.D t ω

/-- `I` is a version of the paper's conditional joint distribution `I_s = I_s(f_s)` of the demands
given the information at the beginning of period `s` (p. 288), with the properties the paper
assumes of it:
1. each `I s ω` is a probability measure on demand paths;
2. `ω ↦ I s ω A` is `ℱ s`-measurable (it is determined by the information set `f_s`);
3. it is a regular conditional distribution of the demand path given `ℱ s`:
   `μ (B ∩ {D ∈ A}) = ∫_B I s ω A dμ` for every `ℱ s`-measurable `B`;
4. the demand `D_s` is known deterministically under `I_s` (§6, p. 299);
5. demands are nonnegative under `I_s`;
6. the conditional expectation `E[D_t | f_s]` is finite for `1 ≤ s ≤ t ≤ T` (p. 288). -/
def LotSizingModel.IsCondDemandLaw (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ)) : Prop :=
  (∀ s, IsMarkovKernel (I s)) ∧
  (∀ s (A : Set (ℕ → ℝ)), MeasurableSet A → Measurable[M.ℱ s] (fun ω => I s ω A)) ∧
  (∀ s (A : Set (ℕ → ℝ)) (B : Set Ω), MeasurableSet A → MeasurableSet[M.ℱ s] B →
      M.μ (B ∩ M.demandPath ⁻¹' A) = ∫⁻ ω in B, I s ω A ∂M.μ) ∧
  (∀ s ω, ∀ᵐ d ∂(I s ω), d s = M.D s ω) ∧
  (∀ s ω, ∀ᵐ d ∂(I s ω), ∀ t, 0 ≤ d t) ∧
  (∀ s t ω, 1 ≤ s → s ≤ t → t ≤ M.T → Integrable (fun d : ℕ → ℝ => d t) (I s ω))

end LeviBalancing.TripleBalancing


