-- Prove2me | Definitions.Def_HermiteLaptop_MaxAgree_TruncBounds
-- name    : HermiteLaptop_MaxAgree_TruncBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:17:27.545197+00:00
-- url     : https://prove2.me/theorems/95002089-4122-4887-848c-a8c849139eb5
-- title:
--   Truncated bounds P̲_{k,M}, P̄_{k,M} on the collision probability and their mixtures P̲_M, P̄_M (Proposition 2.4, Corollary 2.5)
-- statement:
--   Given reals $\underline c_{k,m}$ and $\overline c_{k,m}$ for $m=0,\dots,M$ (intended as bounds $\underline c_{k,m}\le c_{k,m}\le\overline c_{k,m}$), define
--   $$\underline P_{k,M}(\rho)=\begin{cases}\sum_{m=0}^M\underline c_{k,m}\rho^m,&\rho\in[0,1],\\ \sum_{m\le M,\ m\text{ even}}\underline c_{k,m}\rho^m+\sum_{m\le M,\ m\text{ odd}}\overline c_{k,m}\rho^m-|\rho|^{M+1}\big(1-\sum_{m=0}^M\underline c_{k,m}\big),&\rho\in[-1,0],\end{cases}$$
--   $$\overline P_{k,M}(\rho)=\begin{cases}\sum_{m=0}^M\overline c_{k,m}\rho^m+\rho^{M+1}\big(1-\sum_{m=0}^M\underline c_{k,m}\big),&\rho\in[0,1],\\ \sum_{m\le M,\ m\text{ even}}\overline c_{k,m}\rho^m+\sum_{m\le M,\ m\text{ odd}}\underline c_{k,m}\rho^m+|\rho|^{M+1}\big(1-\sum_{m=0}^M\underline c_{k,m}\big),&\rho\in[-1,0].\end{cases}$$
--   For a mixture, $\underline P_M=\sum_{k\in\mathcal K}\lambda_k\underline P_{k,M}$ and $\overline P_M=\sum_{k\in\mathcal K}\lambda_k\overline P_{k,M}$.
--
--   **Formalization Note.** `truncLower M cl cu ρ` and `truncUpper M cl cu ρ` take the `[0,1]` branch for `ρ ≥ 0` and the `[−1,0]` branch for `ρ < 0` (the branches agree at `0`). `Mixture.truncLower μ M cl cu ρ = ∑' k, lam k * truncLower M (cl k) (cu k) ρ`, likewise for the upper bound; `cl cu : ℕ → ℕ → ℝ` are indexed by `k` then `m`.
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), pp. 16–18 (PDF 19–21), Proposition 2.4 and Corollary 2.5

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Mixture

/-!
# Truncated bounds `P̲_{k,M}`, `P̄_{k,M}` and their mixtures `P̲_M`, `P̄_M`

García-Soriano, Miyauchi, *Hermite Brings a Laptop*, arXiv:2609.35453 (held version, sha256
97504f90…), Proposition 2.4 pp. 16–17 (PDF 19–20); Corollary 2.5 pp. 17–18 (PDF 20–21).

Given bounds `c̲_{k,m} ≤ c_{k,m} ≤ c̄_{k,m}` (`m = 0, …, M`):
P̲_{k,M}(ρ) = Σ_{m≤M} c̲_{k,m} ρᵐ on [0, 1];
            = Σ_{m≤M, m even} c̲_{k,m} ρᵐ + Σ_{m≤M, m odd} c̄_{k,m} ρᵐ − |ρ|^{M+1}(1 − Σ_{m≤M} c̲_{k,m}) on [−1, 0];
P̄_{k,M}(ρ) = Σ_{m≤M} c̄_{k,m} ρᵐ + ρ^{M+1}(1 − Σ_{m≤M} c̲_{k,m}) on [0, 1];
            = Σ_{m≤M, m even} c̄_{k,m} ρᵐ + Σ_{m≤M, m odd} c̲_{k,m} ρᵐ + |ρ|^{M+1}(1 − Σ_{m≤M} c̲_{k,m}) on [−1, 0].
P̲_M = Σ_{k∈K} λ_k P̲_{k,M}, P̄_M = Σ_{k∈K} λ_k P̄_{k,M}.

Conventions.
* `cl m` is `c̲_{k,m}` and `cu m` is `c̄_{k,m}` (only `m ≤ M` is read). The two printed branches
  agree at `ρ = 0`; the definition uses the `[0, 1]` branch for `ρ ≥ 0` and the `[−1, 0]` branch
  for `ρ < 0`. Values outside `[−1, 1]` are never used.
* For a mixture, the bounds are families `cl cu : ℕ → ℕ → ℝ` indexed by `k` then `m`.
-/

namespace HermiteLaptop.MaxAgree

/-- `P̲_{k,M}(ρ)` of Proposition 2.4, from lower bounds `cl` and upper bounds `cu`. -/
noncomputable def truncLower (M : ℕ) (cl cu : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  if 0 ≤ ρ then ∑ m ∈ Finset.range (M + 1), cl m * ρ ^ m
  else (∑ m ∈ Finset.range (M + 1), (if Even m then cl m else cu m) * ρ ^ m)
    - |ρ| ^ (M + 1) * (1 - ∑ m ∈ Finset.range (M + 1), cl m)

/-- `P̄_{k,M}(ρ)` of Proposition 2.4, from lower bounds `cl` and upper bounds `cu`. -/
noncomputable def truncUpper (M : ℕ) (cl cu : ℕ → ℝ) (ρ : ℝ) : ℝ :=
  if 0 ≤ ρ then (∑ m ∈ Finset.range (M + 1), cu m * ρ ^ m)
    + ρ ^ (M + 1) * (1 - ∑ m ∈ Finset.range (M + 1), cl m)
  else (∑ m ∈ Finset.range (M + 1), (if Even m then cu m else cl m) * ρ ^ m)
    + |ρ| ^ (M + 1) * (1 - ∑ m ∈ Finset.range (M + 1), cl m)

/-- `P̲_M(ρ) = Σ_{k∈K} λ_k P̲_{k,M}(ρ)` (Corollary 2.5). -/
noncomputable def Mixture.truncLower (μ : Mixture) (M : ℕ) (cl cu : ℕ → ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑' k, μ.lam k * HermiteLaptop.MaxAgree.truncLower M (cl k) (cu k) ρ

/-- `P̄_M(ρ) = Σ_{k∈K} λ_k P̄_{k,M}(ρ)` (Corollary 2.5). -/
noncomputable def Mixture.truncUpper (μ : Mixture) (M : ℕ) (cl cu : ℕ → ℕ → ℝ) (ρ : ℝ) : ℝ :=
  ∑' k, μ.lam k * HermiteLaptop.MaxAgree.truncUpper M (cl k) (cu k) ρ

end HermiteLaptop.MaxAgree


