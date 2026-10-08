-- Prove2me | Definitions.Def_SmallGainISS_OmegaPath_IsOmegaPath
-- name    : SmallGainISS_OmegaPath_IsOmegaPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:25.279376+00:00
-- url     : https://prove2.me/theorems/e2c48605-fd37-4fc6-8231-e9b506082c04
-- title:
--   Definition 5.1 — $\Omega$-path with respect to an operator $T$
-- statement:
--   Let $T:\mathbb R^n_+\to\mathbb R^n_+$. A continuous path $\sigma:\mathbb R_+\to\mathbb R^n_+$ all of whose components $\sigma_i$ belong to $\mathcal K_\infty$ is an **$\Omega$-path with respect to $T$** if, writing $\sigma_i^{-1}$ for the inverse of $\sigma_i$ on $\mathbb R_+$,
--
--   1. each $\sigma_i^{-1}$ is locally Lipschitz continuous on $(0,\infty)$;
--   2. for every compact set $K\subset(0,\infty)$ there are constants $0<c<C$ such that for all $i=1,\dots,n$ and all points $r\in K$ at which $\sigma_i^{-1}$ is differentiable,
--   $$0<c\le(\sigma_i^{-1})'(r)\le C;$$
--   3. $\sigma(r)\in\Omega(T)$ for every $r>0$, that is,
--   $$T(\sigma(r))<\sigma(r)\qquad\text{for all } r>0,$$
--   with the strict inequality in every component.
--
--   The constants $c,C$ depend on $K$ only and are uniform in $i$. An $\Omega$-path is the nonlinear substitute for a Perron vector: it is the input of the paper's construction of an ISS Lyapunov function for a network (Theorem 5.3).
--
--   **Formalization Note** The inverses are carried explicitly as functions $\tau_i$ with $\tau_i\circ\sigma_i=\mathrm{id}=\sigma_i\circ\tau_i$; since each $\sigma_i$ is a bijection of $\mathbb R_+$ they are unique. Derivatives are taken of the real function $r\mapsto\tau_i(\max(r,0))$, which agrees with $\tau_i$ near every $r>0$, and only at points where it is differentiable.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 13, Definition 5.1

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator
import Definitions.Def_SmallGainISS_Lyapunov_Gains

open scoped NNReal

namespace SmallGainISS.OmegaPath

/-! Definition 5.1 (Dashkovskiy, Rüffer, Wirth, arXiv:0901.1842v2, p. 13). -/

variable {n : ℕ}

/-- Definition 5.1 (p. 13). A continuous path `σ : ℝ₊ → ℝⁿ₊` with every component `σᵢ ∈ 𝒦∞` is
an Ω-path with respect to `T` if, writing `τᵢ = σᵢ⁻¹` for the inverse of `σᵢ` on `ℝ₊`,
(i) each `τᵢ` is locally Lipschitz continuous on `(0, ∞)`;
(ii) for every compact `K ⊂ (0, ∞)` there are constants `0 < c < C` such that for all `i` and all
`r ∈ K` at which `τᵢ` is differentiable, `c ≤ τᵢ'(r) ≤ C` (5.1);
(iii) `σ(r) ∈ Ω(T)` for all `r > 0`, i.e. `T(σ(r)) < σ(r)` (5.2), strict componentwise.
The inverses are carried explicitly as `τ`; since each `σᵢ` is a bijection of `ℝ₊`, `τ` is unique. -/
def IsOmegaPath (T : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) (σ : ℝ≥0 → Fin n → ℝ≥0) : Prop :=
  Continuous σ ∧ (∀ i, SmallGainISS.Lyapunov.IsKInf (fun r => σ r i)) ∧
  ∃ τ : Fin n → ℝ≥0 → ℝ≥0,
    (∀ i, Function.LeftInverse (τ i) (fun r => σ r i) ∧
      Function.RightInverse (τ i) (fun r => σ r i)) ∧
    (∀ i, LocallyLipschitzOn (Set.Ioi (0 : ℝ≥0)) (τ i)) ∧
    (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
      ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ i, ∀ r ∈ K, DifferentiableAt ℝ (SmallGainISS.Lyapunov.liftR (τ i)) r →
        c ≤ deriv (SmallGainISS.Lyapunov.liftR (τ i)) r ∧ deriv (SmallGainISS.Lyapunov.liftR (τ i)) r ≤ C) ∧
    ∀ r : ℝ≥0, 0 < r → σ r ∈ SmallGainISS.Lyapunov.Omega T

end SmallGainISS.OmegaPath


