-- Prove2me | Definitions.Def_IncrementalER_mwuWeight
-- name    : IncrementalER_mwuWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:14.242206+00:00
-- url     : https://prove2.me/theorems/e87bf3e7-bca1-41f9-b861-39f3a86f05b4
-- title:
--   Multiplicative-weights distributions and conditional independence of a sequence
-- statement:
--   Given increments $h_t(v)$ ($t\ge1$, $v\in V$) and a step size $\eta$, the multiplicative-weights update has weights $w_0\equiv1$, $w_t(v)=w_{t-1}(v)\exp(\eta h_t(v))$, that is $w_t(v)=\exp(\eta\sum_{s=1}^th_s(v))$, and distributions
--
--   $$p_t(v)=\frac{w_{t-1}(v)}{\sum_uw_{t-1}(u)}\qquad(t\ge1).$$
--
--   Real random variables $Y_1,Y_2,\dots$ are **conditionally independent given a σ-algebra $\mathcal G$** if for every finite set $I$ of indices and Borel sets $B_i$,
--
--   $$\mathbb P\Big(\bigcap_{i\in I}\{Y_i\in B_i\}\,\Big|\,\mathcal G\Big)=\prod_{i\in I}\mathbb P(Y_i\in B_i\mid\mathcal G)\quad\text{a.s.}$$
--
--   These are the update of Lemmas 4.3 and 4.11 and the independence assumption of Lemma 4.11.
--
--   **Formalization Note** Conditional independence is stated directly with conditional expectations of indicators; Mathlib's `iCondIndepFun` would require a standard Borel sample space, which the paper does not assume.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.3, p.16; Lemma 4.11 and (12), pp.22–23; Appendix A.1, p.59

import Mathlib

namespace IncrementalER

/-!
# Multiplicative weights, and conditional independence of a sequence of random variables

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.3 (p.16),
Lemma 4.11 and (12) (pp.22–23), and its proof in Appendix A.1 (pp.59–61).

**Formalization Note.**
* `w_0(v) = 1` and `w_t(v) = w_{t−1}(v) exp(η h_t(v))`, written in closed form
  `w_t(v) = exp(η ∑_{s=1}^t h_s(v))`; `p_t(v) = w_{t−1}(v) / ∑_u w_{t−1}(u)` for rounds `t ≥ 1`.
  For Lemma 4.3 the increment is the feedback `h_t = g_t`; for Lemma 4.11 it is the realized
  stochastic sum `h_t(v) = ∑_{i=1}^{N_t} Y_{t,i}(v)` of (12).
* `CondIndepSeq m μ Y`: the random variables `Y i` (`i ∈ ℕ`) are conditionally independent given
  the σ-algebra `m`, in the standard sense that for every finite set of indices and Borel sets the
  conditional probability of the intersection is a.e. the product of the conditional
  probabilities. Mathlib's `iCondIndepFun` needs a standard Borel sample space, which the paper does
  not assume, so this is stated directly.
-/

/-- The weights `w_t(v) = exp(η ∑_{s=1}^t h_s(v))`, `w_0(v) = 1`. -/
noncomputable def mwuWeight {V : Type*} (η : ℝ) (h : ℕ → V → ℝ) (t : ℕ) (v : V) : ℝ :=
  Real.exp (η * ∑ s ∈ Finset.Icc 1 t, h s v)

/-- The distribution `p_t(v) = w_{t−1}(v) / ∑_u w_{t−1}(u)` of round `t ≥ 1`. -/
noncomputable def mwuDist {V : Type*} [Fintype V] (η : ℝ) (h : ℕ → V → ℝ) (t : ℕ) (v : V) : ℝ :=
  mwuWeight η h (t - 1) v / ∑ u, mwuWeight η h (t - 1) u

/-- The real random variables `Y i`, `i ∈ ℕ`, are conditionally independent given `m`. -/
def CondIndepSeq {Ω : Type*} {mΩ : MeasurableSpace Ω} (m : MeasurableSpace Ω)
    (μ : @MeasureTheory.Measure Ω mΩ) (Y : ℕ → Ω → ℝ) : Prop :=
  ∀ (I : Finset ℕ) (B : ℕ → Set ℝ), (∀ i, MeasurableSet (B i)) →
    MeasureTheory.condExp m μ (fun ω => ∏ i ∈ I, (Y i ⁻¹' B i).indicator (fun _ => (1 : ℝ)) ω)
      =ᵐ[μ] fun ω => ∏ i ∈ I,
        MeasureTheory.condExp m μ ((Y i ⁻¹' B i).indicator (fun _ => (1 : ℝ))) ω

end IncrementalER


