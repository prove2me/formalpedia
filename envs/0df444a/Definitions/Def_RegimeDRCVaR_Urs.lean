-- Prove2me | Definitions.Def_RegimeDRCVaR_Urs
-- name    : RegimeDRCVaR_Urs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:19.049209+00:00
-- url     : https://prove2.me/theorems/0c2a5f56-966e-46f9-8e7f-5330a4e63609
-- title:
--   Regime-switching ambiguity set $\mathcal U_{rs}(\boldsymbol\theta)$ (corrected regime budget)
-- statement:
--   There are $K$ regimes. Regime $k$ has $N_k$ return samples $r_{nk}\in\mathbb R^I$ ($n\in[N_k]$), occurs with probability $w_k$, and has radius $\theta_k$. The **regime-switching ambiguity set** $\mathcal U_{rs}(\boldsymbol\theta)$ is the set of probability laws $\mathbb P$ of $(\tilde r,\tilde u,\tilde n,\tilde k)$ such that
--
--   1. $\mathbb P[\tilde k=k,\ \tilde n=n]=w_k/N_k$ for every $k\in[K]$ and $n\in[N_k]$;
--   2. $\mathbb P[\tilde k=k]=w_k$ for every $k$;
--   3. $\rho(\tilde r,r_{\tilde n\tilde k})=\|\tilde r-r_{\tilde n\tilde k}\|_m\le\tilde u_{\tilde k}$ almost surely;
--   4. $\mathbb E^{\mathbb P}[\tilde u_k\,\mathbf 1\{\tilde k=k\}]\le w_k\theta_k$ for every $k$.
--
--   Conditionally on regime $k$ and scenario $n$, the return is moved away from the sample $r_{nk}$ by at most $\tilde u_k$, and the average displacement in regime $k$ is at most $\theta_k$. This is the ambiguity set of problem (11) and of Theorem 1.
--
--   **Formalization Note**
--   1. Condition 4 corrects display (9), which prints $\mathbb E^{\mathbb P}[\tilde u_k]\le\theta_k$. With the printed budget the coordinates $\tilde u_k$, $k\ne\tilde k$, are unconstrained by condition 3 and can be made very negative, and Theorem 1 fails: for $K=2$, $w=(\tfrac12,\tfrac12)$, $N_1=N_2=1$, $I=1$, $r_{11}=r_{12}=0$, $\theta=(1,1)$, put $\tilde r=-M$, $\tilde u=(M,0)$ on $\tilde k=1$ and $\tilde r=0$, $\tilde u=(-M,0)$ on $\tilde k=2$; all printed constraints hold for every $M$ and the worst-case loss is unbounded. Condition 4 is the budget of the first display of the proof of Theorem 1 (p. ec2) and the per-regime $\mathbb E[\tilde u]\le\theta_k$ of (EC.1), weighted by $w_k$.
--   2. Condition 1 is the paper's $\mathbb P[\tilde n=n\mid\tilde k=k]=1/N_k$ combined with $\mathbb P[\tilde k=k]=w_k$; it is well defined when $w_k=0$. Condition 2 is kept as printed.
--   3. The expectation in condition 4 is a lower Lebesgue integral of $\max(\tilde u_k,0)$ over $\{\tilde k=k\}$, faithful because $\tilde u_{\tilde k}\ge 0$ almost surely by condition 3.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, display (9), p.11 (budget as in the proof of Theorem 1, p.ec2, and (EC.1), p.ec1)

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_RegimeDRCVaR_Scenario

open MeasureTheory
open scoped ENNReal

namespace RegimeDRCVaR

/-- **The regime-switching Wasserstein ambiguity set `U_rs(θ)`**
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, display (9), p.11), with the
regime budget as used in the proof of Theorem 1 (p.ec2).

There are `K` regimes; regime `k` has `N_k` return samples `r_{nk} ∈ ℝ^I`, occurs with
probability `w_k`, and has radius `θ_k`. A law `P` of `(r̃, ũ, (k̃, ñ))` belongs to `U_rs(θ)` iff
it is a probability measure and
1. (scenario law) `P[k̃ = k, ñ = n] = w_k / N_k` for every `k` and `n ∈ [N_k]`
   (the paper's `P[ñ = n | k̃ = k] = 1/N_k` together with `P[k̃ = k] = w_k`);
2. (regime law) `P[k̃ = k] = w_k` for every `k`;
3. (support) `ρ(r̃, r_{ñk̃}) = ‖r̃ − r_{ñk̃}‖_m ≤ ũ_{k̃}` `P`-almost surely;
4. (regime budget) `𝔼^P[ũ_k 1{k̃ = k}] ≤ w_k θ_k` for every `k`.

**Formalization Note**
* Correction of display (9): the printed budget is `𝔼^P[ũ_k] ≤ θ_k`, unconditional. Since
  the support constraint only bounds `ũ_{k̃}`, the coordinates `ũ_k` with `k ≠ k̃` are free and
  can be made very negative, which lets the regime-`k̃` coordinate be large; with the printed
  budget, Theorem 1 is false (`K = 2`, `w = (½, ½)`, `N₁ = N₂ = 1`, `I = 1`, `r₁₁ = r₁₂ = 0`,
  `θ = (1, 1)`: on `k̃ = 1` put `r̃ = −M`, `ũ = (M, 0)`; on `k̃ = 2` put `r̃ = 0`, `ũ = (−M, 0)`;
  the printed constraints hold for every `M` and the worst-case loss is unbounded). The
  budget used here, `𝔼^P[ũ_k 1{k̃ = k}] ≤ w_kθ_k`, is the one in the first display of the proof
  of Theorem 1 (p.ec2: `∑_n (w_k/N_k) 𝔼^{P̃_nk}[u_k] ≤ w_kθ_k`) and is the per-regime
  `𝔼[ũ] ≤ θ_k` of (EC.1) (p.ec1) weighted by `w_k`.
* The expectation in the budget is a lower Lebesgue integral of `ofReal ũ_k` over `{k̃ = k}`;
  this is faithful because `ũ_{k̃} ≥ ρ ≥ 0` almost surely by the support constraint.
* Regime `k` of the paper is `k : Fin K` (index `k − 1`), scenario `n ∈ [N_k]` is
  `n : Fin (N k)` (index `n − 1`), and the sample `r_{nk}` is `r k n`.
* The regime law 2 follows from 1 when the `N_k` are positive and the `w_k` sum to one; it
  is kept because the paper lists it. -/
def Urs {I K : ℕ} {N : Fin K → ℕ} (m : ℝ≥0∞) (r : (k : Fin K) → Fin (N k) → Fin I → ℝ)
    (w θ : Fin K → ℝ) : Set (Measure (Scenario I K)) :=
  {P | IsProbabilityMeasure P ∧
    (∀ (k : Fin K) (n : Fin (N k)),
      P {ω | ω.2.2 = (k, (n : ℕ))} = ENNReal.ofReal (w k / (N k : ℝ))) ∧
    (∀ k : Fin K, P {ω | ω.2.2.1 = k} = ENNReal.ofReal (w k)) ∧
    (∀ᵐ ω ∂P, ∀ h : ω.2.2.2 < N ω.2.2.1,
      normM m (ω.1 - r ω.2.2.1 ⟨ω.2.2.2, h⟩) ≤ ω.2.1 ω.2.2.1) ∧
    (∀ k : Fin K,
      ∫⁻ ω in {ω : Scenario I K | ω.2.2.1 = k}, ENNReal.ofReal (ω.2.1 k) ∂P ≤
        ENNReal.ofReal (w k * θ k))}

end RegimeDRCVaR


