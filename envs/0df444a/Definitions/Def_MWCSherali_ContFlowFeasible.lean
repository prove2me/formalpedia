-- Prove2me | Definitions.Def_MWCSherali_ContFlowFeasible
-- name    : MWCSherali_ContFlowFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:07.71423+00:00
-- url     : https://prove2.me/theorems/29148ac6-caa1-4537-a4bc-30bb12bc2270
-- title:
--   Feasible solutions of the continuous Flow LP
-- statement:
--   Let $\Delta_k=\{t\in\mathbb R^k_{\ge0}\mid\sum_it_i=1\}$ and $\Gamma_a=\{t\in\Delta_k\mid t_a=0\}$. A **feasible solution of (Continuous-Flow-LP)** consists of nonnegative Borel measures $F_{a,i}$, $B_i$ on $\Delta_k$ ($a\neq i\in[k]$) and probability measures $\nu_a$ on $\Gamma_a$ with
--
--   1. $0\le F_{a,i}\le B_i$ for $a\neq i$;
--   2. for every $a\in[k]$ and every continuously differentiable $\varphi$ on $\Delta_k$,
--   $$\sum_{i\neq a}\int_{\Delta_k}\nabla\varphi\cdot(e_a-e_i)\,dF_{a,i}=\varphi(e_a)-\int_{\Gamma_a}\varphi\,d\nu_a .$$
--
--   It is the continuum limit of the Flow LP: commodity $a$ starts at $e_a$, the measure $\nu_a$ is where it exits.
--
--   **Formalization Note** Measures live on $\mathbb R^k$ and give the complement of $\Delta_k$ (resp. $\Gamma_a$) measure $0$. The capacities $B_i$ are required to be finite: an infinite capacity has objective $\infty$, so no infimum changes, and every integral is then a genuine one. Test functions are the $C^1$ functions on $\mathbb R^k$: the constraint only involves values on $\Delta_k$ and derivatives in directions tangent to $\Delta_k$, and every function continuously differentiable on $\Delta_k$ agrees there with a global $C^1$ function.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (Continuous-Flow-LP), pp.27–28

import Mathlib

namespace MWCSherali

open MeasureTheory

/-- **Feasible solutions of (Continuous-Flow-LP).** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), §3.3, pp.27–28. With
`Δ_k = {t ∈ ℝ^k_{≥0} | ∑ t_i = 1}` and `Γ_a = {t ∈ Δ_k | t_a = 0}`, the variables are nonnegative
Borel measures `F_{a,i}`, `B_i` on `Δ_k` (`a ≠ i ∈ [k]`) and probability measures `ν_a` on `Γ_a`,
subject to
* `0 ≤ F_{a,i} ≤ B_i` for `a ≠ i`;
* `∑_{i ≠ a} ∫_{Δ_k} ∇φ · (e_a − e_i) dF_{a,i} = φ(e_a) − ∫_{Γ_a} φ dν_a` for every `a ∈ [k]`
  and every `φ ∈ C^{(1)}(Δ_k)`.

**Formalization Note.**
* Measures live on `Fin k → ℝ` (Borel); "a measure on `Δ_k`" is a measure giving the complement
  of `Δ_k = stdSimplex ℝ (Fin k)` measure `0`, and likewise for `ν_a` and `Γ_a`. `F a i ≤ B i`
  is the order on measures; it puts `F a i` on `Δ_k` too. `F a a` is not a variable and appears
  nowhere.
* The capacities `B i` are required to be finite. An infinite capacity has objective `⊤`, so the
  requirement changes no infimum; it makes every integral in the constraint a genuine one (a
  Bochner integral of a non-integrable function would be `0`).
* Test functions are the `C¹` functions on all of `ℝ^k` (`ContDiff ℝ 1 φ`). The constraint only
  involves the values of `φ` on `Δ_k` and its derivatives in the directions `e_a − e_i` tangent
  to `Δ_k`, and every function continuously differentiable on `Δ_k` agrees there with a global
  `C¹` function. `∇φ(t) · (e_a − e_i)` is `fderiv ℝ φ t (e_a − e_i)`.
* Indices are 0-based (`Fin k`); `e_a = Pi.single a 1`. -/
def ContFlowFeasible (k : ℕ) (F : Fin k → Fin k → Measure (Fin k → ℝ))
    (B : Fin k → Measure (Fin k → ℝ)) (ν : Fin k → Measure (Fin k → ℝ)) : Prop :=
  (∀ i, IsFiniteMeasure (B i) ∧ B i (stdSimplex ℝ (Fin k))ᶜ = 0) ∧
  (∀ a i, a ≠ i → F a i ≤ B i) ∧
  (∀ a, IsProbabilityMeasure (ν a) ∧ ν a {t | t ∈ stdSimplex ℝ (Fin k) ∧ t a = 0}ᶜ = 0) ∧
  (∀ (a : Fin k) (φ : (Fin k → ℝ) → ℝ), ContDiff ℝ 1 φ →
    ∑ i ∈ Finset.univ.filter (· ≠ a),
        ∫ t, fderiv ℝ φ t (Pi.single a 1 - Pi.single i 1) ∂(F a i) =
      φ (Pi.single a 1) - ∫ t, φ t ∂(ν a))

end MWCSherali


