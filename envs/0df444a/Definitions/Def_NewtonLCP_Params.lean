-- Prove2me | Definitions.Def_NewtonLCP_Params
-- name    : NewtonLCP_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:00.947141+00:00
-- url     : https://prove2.me/theorems/3f3b1340-5449-40ef-ae42-a185aa18fdab
-- title:
--   The parameter rule (54): $\beta_N(\kappa)$ and $\delta_N(\kappa)$
-- statement:
--   For a dimension $N$ and a guess $\kappa\ge1$ on the handicap number, the neighbourhood size $\beta_N(\kappa)$ and the step size $\delta_N(\kappa)$ may be any values with
--
--   $$\beta_N(\kappa)\in\begin{cases}\big[\tfrac1{8(1+\kappa)},\tfrac1{4(1+\kappa)}\big]&\kappa^4\le N^5\\[2pt]\big[\tfrac1{8192N^{3/2}},\tfrac1{4096N^{3/2}}\big]&\kappa^4>N^5\end{cases}\qquad
--   \delta_N(\kappa)\in\begin{cases}\big[\tfrac1{32\sqrt N(1+\kappa)},\tfrac1{16\sqrt N(1+\kappa)}\big]&\kappa^4\le N^5\\[2pt]\big[\tfrac1{2436N^{9/8}\sqrt{1+\kappa}},\tfrac1{1218N^{9/8}\sqrt{1+\kappa}}\big]&\kappa^4>N^5\end{cases}\qquad(54)$$
--
--   The first branch is the setting of Theorem 4.2, the second that of Theorem 6.4; the switch at $\kappa^4=N^5$ selects the better of the two iteration bounds.
--
--   **Formalization Note** A parameter choice is a pair of functions $(N,\kappa)\mapsto\beta_N(\kappa),\delta_N(\kappa)$; the rule is imposed for $N\ge1$ (at $N=0$ the intervals divide by zero).
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), display (54), p.31

import Mathlib

namespace NewtonLCP

/-!
# The parameter rule (54)

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), display (54), p.31.

For dimension `N` and a guess `κ ≥ 1`, (54) lets `β_N(κ)` and `δ_N(κ)` be any values in
* `β ∈ [1/(8(1+κ)), 1/(4(1+κ))]`, `δ ∈ [1/(32√N(1+κ)), 1/(16√N(1+κ))]` if `κ⁴ ≤ N⁵`;
* `β ∈ [1/(8192N^{3/2}), 1/(4096N^{3/2})]`, `δ ∈ [1/(2436N^{9/8}√(1+κ)), 1/(1218N^{9/8}√(1+κ))]`
  if `κ⁴ > N⁵`.

**Formalization Note.** A parameter choice is a pair of functions `β δ : ℕ → ℝ → ℝ` (dimension,
guess); `AdmissibleParams β δ` says every value lies in its interval of (54). The rule is imposed
for `N ≥ 1` only: at `N = 0` the intervals divide by zero. Powers `N^{3/2}`, `N^{9/8}` are real
powers (`Real.rpow`).
-/

/-- `β`, `δ` obey (54) for every dimension `N ≥ 1` and every guess `κ ≥ 1`. -/
def AdmissibleParams (β δ : ℕ → ℝ → ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ κ : ℝ, 1 ≤ κ →
    (κ ^ 4 ≤ (N : ℝ) ^ 5 →
      1 / (8 * (1 + κ)) ≤ β N κ ∧ β N κ ≤ 1 / (4 * (1 + κ)) ∧
      1 / (32 * Real.sqrt N * (1 + κ)) ≤ δ N κ ∧ δ N κ ≤ 1 / (16 * Real.sqrt N * (1 + κ))) ∧
    ((N : ℝ) ^ 5 < κ ^ 4 →
      1 / (8192 * (N : ℝ) ^ ((3 : ℝ) / 2)) ≤ β N κ ∧
        β N κ ≤ 1 / (4096 * (N : ℝ) ^ ((3 : ℝ) / 2)) ∧
      1 / (2436 * (N : ℝ) ^ ((9 : ℝ) / 8) * Real.sqrt (1 + κ)) ≤ δ N κ ∧
        δ N κ ≤ 1 / (1218 * (N : ℝ) ^ ((9 : ℝ) / 8) * Real.sqrt (1 + κ)))

end NewtonLCP


