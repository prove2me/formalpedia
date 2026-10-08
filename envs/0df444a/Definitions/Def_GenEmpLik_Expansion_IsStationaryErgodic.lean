-- Prove2me | Definitions.Def_GenEmpLik_Expansion_IsStationaryErgodic
-- name    : GenEmpLik_Expansion_IsStationaryErgodic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:01:42.393167+00:00
-- url     : https://prove2.me/theorems/a956dcbf-f4a8-4e13-a448-682c26ca993c
-- title:
--   Strictly stationary ergodic sequence of real random variables
-- statement:
--   Let $Z_1,Z_2,\dots$ be real random variables on a probability space $(\Omega,\mathcal F,\mathbb P)$ and let $\mu_Z$ be the law of the path $(Z_1,Z_2,\dots)$ on $\mathbb R^{\mathbb N}$ with the product $\sigma$-algebra. Let $\theta$ be the left shift, $\theta(s_1,s_2,\dots)=(s_2,s_3,\dots)$. The sequence is **strictly stationary and ergodic** if
--
--   1. each $Z_i$ is measurable;
--   2. $\mu_Z\circ\theta^{-1}=\mu_Z$ (strict stationarity: every finite-dimensional law is shift invariant);
--   3. every measurable set $A\subseteq\mathbb R^{\mathbb N}$ with $\theta^{-1}A=A$ has $\mu_Z(A)\in\{0,1\}$ (ergodicity).
--
--   Every i.i.d. sequence is stationary and ergodic (Kolmogorov's 0–1 law), and so is every stationary sequence satisfying the mixing condition displayed in §2.2 of the paper. This is the hypothesis of the paper's Lemma 1.
--
--   **Formalization Note** The definition is Mathlib's `Ergodic seqShift μ_Z`, which contains `MeasurePreserving seqShift μ_Z μ_Z`; `μ_Z` is `P.map (fun ω k => Z k ω)` and Lean's `Z 0` is the paper's $Z_1$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 7, §2.2 (definition before Lemma 1) and Lemma 1

import Mathlib

open MeasureTheory

namespace GenEmpLik.Expansion

/-- The left shift `(s₀, s₁, s₂, …) ↦ (s₁, s₂, …)` on real sequences. -/
def seqShift (s : ℕ → ℝ) : ℕ → ℝ := fun k => s (k + 1)

/-- A sequence of real random variables `Z 0, Z 1, …` on `(Ω, P)` is strictly stationary and
ergodic (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 7, the hypothesis of Lemma 1): each `Z i`
is measurable, and the law `μ_Z` of the whole path `ω ↦ (Z 0 ω, Z 1 ω, …)` on `ℕ → ℝ` (product
σ-algebra) is invariant under the left shift (strict stationarity) and every shift-invariant
measurable set of paths has `μ_Z`-measure `0` or `1` (ergodicity). This is Mathlib's
`Ergodic seqShift μ_Z`, which includes `MeasurePreserving seqShift μ_Z μ_Z`. -/
def IsStationaryErgodic {Ω : Type*} [MeasurableSpace Ω] (Z : ℕ → Ω → ℝ) (P : Measure Ω) :
    Prop :=
  (∀ i, Measurable (Z i)) ∧ Ergodic seqShift (P.map (fun ω k => Z k ω))

end GenEmpLik.Expansion


