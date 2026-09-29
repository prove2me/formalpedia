-- Prove2me | Definitions.Def_XinGoldbergTBS_Asymptotic_Witness
-- name    : XinGoldbergTBS_Asymptotic_Witness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:21:02.132545+00:00
-- url     : https://prove2.me/theorems/e3d25a79-5ddf-4733-9543-2284887fe780
-- title:
--   Theorem 2's stationary-like vector $(\chi^{*,L}, q^{*,L}, \mathcal I^{*,L})$ and $r_L = \mathbb E[\chi^{*,L}_1]$
-- statement:
--   Properties (i)–(vi) of Theorem 2 (p. 442), as a predicate on a probability space carrying an $(L - L_0 - 1)$-dimensional random vector $\chi$, an $(L-L_0)$-dimensional random vector $q$, a random variable $\mathcal I$, and i.i.d. demands $\{D_i, i \ge 1\}$ distributed as $D$:
--
--   1. w.p.1 $(\chi, q)$ is nonnegative; $(\chi, \mathcal I)$ is independent of $\{D_i, i \ge 1\}$; $q_i$ is independent of $\{D_j, j \ge i\}$ for $i \in [1, L - L_0]$;
--   2. $\chi_i \sim \chi_1$ for $i \in [1, L-L_0-1]$ and $q_i \sim q_1$ for $i \in [1, L - L_0]$;
--   3. for all $k \in [1, L - L_0]$,
--   $$\mathcal I + \sum_{i=1}^{k-1}(q_i + \chi_i - D_i) + q_k - \sum_{i=k}^{k+L_0} D_i \ \sim\ \mathcal I + q_1 - \sum_{i=1}^{L_0+1} D_i;$$
--   4. $(\chi, q, \mathcal I)$ has finite mean;
--   5. $\mathbb E[\chi_1] + \mathbb E[q_1] = \mathbb E[D]$;
--   6. $\mathrm{OPT}(L) \ge c(\mathbb E[D] - \mathbb E[\chi_1]) + \mathbb E\big[G(\mathcal I + q_1 - \sum_{i=1}^{L_0+1} D_i)\big]$.
--
--   For such a witness, $r_L = \mathbb E[\chi_1]$. The intended interpretation: $\chi$ is the steady-state truncated regular pipeline, $q$ the steady-state vector of the next $L - L_0$ expedited orders, and $\mathcal I$ the steady-state expedited inventory position under an optimal policy.
--
--   Theorem 2 asserts that a witness exists. The results that follow hold for every witness, and $r_L$ depends on the witness, not on $L$ alone.
--
--   **Formalization Note** Coordinates are 0-based ($\chi$'s coordinate $j$ is $\chi_{j+1}$). "$X \sim Y$" is equality in distribution (`IdentDistrib`). In (vi) the first term is nonnegative (by (i) and (v)), so both sides are computed in $[0,\infty]$ without loss. Measurability of all random objects is part of the predicate.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 442, Theorem 2 and definition of r_L

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model

/-!
# The stationary-like vector of Theorem 2 (p. 442) and `r_L` (p. 442)

`IsStationaryWitness P μ κ L₀ L χ q 𝓘 D` says that, on the probability space `(Ω, P)`, the
`(L - L₀ - 1)`-dimensional vector `χ = χ^{*,L}`, the `(L - L₀)`-dimensional vector
`q = q^{*,L}`, the random variable `𝓘 = 𝓘^{*,L}` and the i.i.d. demands `D_i ∼ D` satisfy
properties (i)–(vi) of Theorem 2. Indices are 0-based: coordinate `j` of `χ` or `q` is the
paper's index `j + 1`, and `D j` is the paper's `D_{j+1}`. `chiN`/`qN` extend the vectors by
`0` outside their range; they are only evaluated inside it.

Theorem 2 asserts existence of such a witness; the later results hold for every witness,
and `r_L = 𝔼[χ_1^{*,L}]` is attached to the witness, not to `L` alone.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- `χ_{j+1}`, extended by `0` for `j ≥ L - L₀ - 1`. -/
def chiN {Ω : Type*} (L₀ L : ℕ) (χ : Ω → Fin (L - L₀ - 1) → ℝ) (ω : Ω) (j : ℕ) : ℝ :=
  if h : j < L - L₀ - 1 then χ ω ⟨j, h⟩ else 0

/-- `q_{j+1}`, extended by `0` for `j ≥ L - L₀`. -/
def qN {Ω : Type*} (L₀ L : ℕ) (q : Ω → Fin (L - L₀) → ℝ) (ω : Ω) (j : ℕ) : ℝ :=
  if h : j < L - L₀ then q ω ⟨j, h⟩ else 0

/-- Properties (i)–(vi) of Theorem 2, together with "`{D_i, i ≥ 1}` i.i.d. distributed as `D`"
and measurability of all the random objects. -/
structure IsStationaryWitness {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ) :
    Prop where
  isProb : IsProbabilityMeasure P
  measurable_chi : Measurable χ
  measurable_q : Measurable q
  measurable_I : Measurable I
  measurable_D : ∀ j, Measurable (D j)
  /-- `D_i ∼ D`. -/
  law_D : ∀ j, P.map (D j) = μ.law
  /-- The `D_i` are mutually independent. -/
  indep_D : iIndepFun D P
  /-- (i) w.p.1 `(χ, q)` is nonnegative. -/
  nonneg : ∀ᵐ ω ∂P, (∀ j, 0 ≤ χ ω j) ∧ ∀ j, 0 ≤ q ω j
  /-- (i) `(χ, 𝓘)` is independent of `{D_i, i ≥ 1}`. -/
  indep_chi_I : IndepFun (fun ω => (χ ω, I ω)) (fun ω j => D j ω) P
  /-- (i) `q_i` is independent of `{D_j, j ≥ i}`, `i ∈ [1, L - L₀]`. -/
  indep_q : ∀ k : Fin (L - L₀), IndepFun (fun ω => q ω k) (fun ω j => D (k.val + j) ω) P
  /-- (ii) `χ_i ∼ χ_1`. -/
  ident_chi : ∀ i j : Fin (L - L₀ - 1), IdentDistrib (fun ω => χ ω i) (fun ω => χ ω j) P P
  /-- (ii) `q_i ∼ q_1`. -/
  ident_q : ∀ i j : Fin (L - L₀), IdentDistrib (fun ω => q ω i) (fun ω => q ω j) P P
  /-- (iii) for all `k ∈ [1, L - L₀]`,
  `𝓘 + ∑_{i=1}^{k-1}(q_i + χ_i - D_i) + q_k - ∑_{i=k}^{k+L₀} D_i ∼ 𝓘 + q_1 - ∑_{i=1}^{L₀+1} D_i`. -/
  stationary : ∀ k : Fin (L - L₀), IdentDistrib
    (fun ω => I ω + ∑ i ∈ Finset.range k.val, (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω)
      + q ω k - ∑ i ∈ Finset.range (L₀ + 1), D (k.val + i) ω)
    (fun ω => I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω) P P
  /-- (iv) `(χ, q, 𝓘)` has finite mean. -/
  integrable_chi : ∀ j, Integrable (fun ω => χ ω j) P
  integrable_q : ∀ j, Integrable (fun ω => q ω j) P
  integrable_I : Integrable I P
  /-- (v) `𝔼[χ_1] + 𝔼[q_1] = 𝔼[D]`. -/
  mean_eq : (∫ ω, chiN L₀ L χ ω 0 ∂P) + (∫ ω, qN L₀ L q ω 0 ∂P) = μ.mean
  /-- (vi) `OPT(L) ≥ c(𝔼[D] - 𝔼[χ_1]) + 𝔼[G(𝓘 + q_1 - ∑_{i=1}^{L₀+1} D_i)]`. -/
  opt_ge : ENNReal.ofReal (κ.c * (μ.mean - ∫ ω, chiN L₀ L χ ω 0 ∂P)) +
      ∫⁻ ω, ENNReal.ofReal (G κ (I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω)) ∂P
    ≤ OPT μ κ L₀ L

/-- `r_L = 𝔼[χ_1^{*,L}]` for a given witness. -/
def rL {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L₀ L : ℕ)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) : ℝ :=
  ∫ ω, chiN L₀ L χ ω 0 ∂P

end XinGoldbergTBS.Asymptotic


