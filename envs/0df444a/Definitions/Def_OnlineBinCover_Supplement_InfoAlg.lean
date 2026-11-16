-- Prove2me | Definitions.Def_OnlineBinCover_Supplement_InfoAlg
-- name    : OnlineBinCover_Supplement_InfoAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:36:42.825435+00:00
-- url     : https://prove2.me/theorems/81ed5a96-1f7b-420d-8982-39548c6c3406
-- title:
--   Randomized online algorithms as measurable rules, and their expected values
-- statement:
--   For the lower bounds an online algorithm has no computational restriction. A **randomized online algorithm** is a probability space $(\Omega,P)$ and a rule that labels item $t$ with a bin, as a function of $\omega\in\Omega$ and the sizes $x_0,\dots,x_t$ seen so far.
--
--   1. A rule **not told the input length** is one rule $\rho(\omega,t,x_0,\dots,x_t)$ for every length, so $A(I_k)$ is the count after the first $k$ arrivals of one run.
--   2. A rule **given moment information** also receives $n$ and the table $\mathrm{mom}_{ij}=\int x^{j}\,dD_i$, $1\le j\le K$, before the first item, and no samples.
--
--   $I_n$ denotes $n$ independent $\mathrm{Unif}[0,1]$ sizes; $\mathbb E[A(\cdot)]$ and $\mathbb E[\mathrm{OPT}(\cdot)]$ are taken over $P$ and the law of the input.
--
--   **Formalization Note** Theorems require each map $(\omega,\text{sizes})\mapsto\text{label}$ to be measurable, so that the expectations are ordinary expectations; labels are natural numbers.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.5, p.6 (PDF p.7) and Section F, p.41 (PDF p.42); Theorem 1.6, p.43 (PDF p.44) and Section G, p.45 (PDF p.46)

import Mathlib
import Definitions.Def_OnlineBinCover_Supplement_Prophet

namespace OnlineBinCover.Supplement

/-!
# Randomized online algorithms without a machine (for the lower bounds)

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), Theorem 1.5 (p.6, PDF p.7; Section F, p.41)
and Theorem 1.6 (p.6, restated p.43; Section G, p.45).

The lower bounds hold for "every possibly randomized online bin covering algorithm", with no
computational restriction, so here an algorithm is a rule, not a program.

**Formalization Note.**
* *Randomized online algorithm.* A probability space `(Ω, P)` (`Ω : Type`) and a rule giving the
  bin label (in `ℕ`) of item `t` as a function of `ω ∈ Ω` and the sizes of items `0, …, t` only
  (`prefixOf x t`). Theorems require each map `(ω, sizes) ↦ label` to be measurable, so that
  `E[A(·)]` is an expectation; `ℕ` carries the discrete σ-algebra.
* *Not told the input length* (Theorem 1.5). The rule `ρ ω t` does not receive `n`: one rule
  serves every length, so `A(I_k)` is the count after the first `k` arrivals of one run.
* *Moment information* (Theorem 1.6). The rule also receives `n` and the table
  `mom i j = ∫ x^{j+1} dD_i` (`j < K`), before the first item, and no samples.
* *Objective.* The count is the published `covered` of the labelling of the `n` items.
* *Instances.* `unifIID n`: `n` independent `Unif[0, 1]` sizes (product of Lebesgue measure on
  `[0, 1]`). For Theorem 1.6, `n` independent sizes `X_i ∼ D_i` arriving in index order.
* *Expectations.* Lower Lebesgue integrals of `ofReal` of counts at most `n`, converted to reals,
  over `P` times the law of the input; with the measurability hypotheses of the theorems these are
  ordinary expectations.
-/

open MeasureTheory

/-- The sizes of items `0, …, t` of the sequence `x`. -/
def prefixOf {n : ℕ} (x : Fin n → ℝ) (t : Fin n) : Fin (t.val + 1) → ℝ :=
  fun j => x ⟨j.val, by omega⟩

/-- `I_n`: the law of `n` independent `Unif[0, 1]` sizes. -/
noncomputable def unifIID (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Icc 0 1)

/-- `A(x)` for a length-oblivious rule `ρ` on randomness `ω`: covered bins of the labels
`ρ ω t (x_0, …, x_t)`. -/
noncomputable def noLenCount {Ω : Type} (ρ : Ω → (t : ℕ) → (Fin (t + 1) → ℝ) → ℕ) (ω : Ω)
    {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  covered x (fun t => ρ ω t.val (prefixOf x t))

/-- `E[A(I_n)]` for a length-oblivious rule. -/
noncomputable def noLenExp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : Ω → (t : ℕ) → (Fin (t + 1) → ℝ) → ℕ) (n : ℕ) : ℝ :=
  (∫⁻ z, ENNReal.ofReal (noLenCount ρ z.1 z.2 : ℝ) ∂(P.prod (unifIID n))).toReal

/-- `E[OPT(I_n)]` for `n` independent `Unif[0, 1]` sizes. -/
noncomputable def unifOptExp (n : ℕ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (OPT x : ℝ) ∂(unifIID n)).toReal

/-- The first `K` moments of each distribution: `mom i j = ∫ x^{j+1} dD_i`. -/
noncomputable def moments (K : ℕ) {n : ℕ} (D : Fin n → ProbabilityMeasure ℝ) :
    Fin n → Fin K → ℝ :=
  fun i j => ∫ x, x ^ (j.val + 1) ∂(D i : Measure ℝ)

/-- `A(X)` for a rule told `n` and the moment table `mom`. -/
noncomputable def momCount {Ω : Type} {K : ℕ}
    (ρ : Ω → (n : ℕ) → (Fin n → Fin K → ℝ) → (t : Fin n) → (Fin (t.val + 1) → ℝ) → ℕ)
    (ω : Ω) {n : ℕ} (mom : Fin n → Fin K → ℝ) (x : Fin n → ℝ) : ℕ :=
  covered x (fun t => ρ ω n mom t (prefixOf x t))

/-- `E[A(X)]` for `X_i ∼ D_i` independent, the rule told `n` and the first `K` moments. -/
noncomputable def momExp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (ρ : Ω → (n : ℕ) → (Fin n → Fin K → ℝ) → (t : Fin n) → (Fin (t.val + 1) → ℝ) → ℕ)
    {n : ℕ} (D : Fin n → ProbabilityMeasure ℝ) : ℝ :=
  (∫⁻ z, ENNReal.ofReal (momCount ρ z.1 (moments K D) z.2 : ℝ) ∂(P.prod (piLaw D))).toReal

end OnlineBinCover.Supplement


