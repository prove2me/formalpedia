-- Prove2me | Definitions.Def_MarkdownReadjust_Model
-- name    : MarkdownReadjust_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:11:50.726264+00:00
-- url     : https://prove2.me/theorems/99bce816-c715-4019-b18e-423883d9a783
-- title:
--   Demand model with assumptions A1–A3
-- statement:
--   A seller posts prices for a single product over $[0,T]$. Customers arrive as a Poisson process with rate $\lambda>0$; each has a valuation in $[0,V]$ and buys one unit iff her valuation is at least the posted price, which at price $v$ happens with probability $\bar F(v)=1-F(v)$. Since $\bar F$ is invertible, the purchase rate $\rho=\bar F(v)$ determines the price $\bar F^{-1}(\rho)$, and the revenue rate per customer is
--
--   $$
--   R(\rho)=\rho\,\bar F^{-1}(\rho),\qquad \rho\in[0,1].
--   $$
--
--   A **model** consists of $\lambda,V>0$, the survival function $\bar F$, a point $\rho^*$ and a constant $C>0$ such that
--
--   1. $\bar F$ is continuous and strictly decreasing on $[0,V]$ with $\bar F(0)=1$ and $\bar F(V)=0$ (so A1 holds: $\bar F(\pi)\to0$ and $R(\pi)\to0$ as $\pi\to V$);
--   2. (A2) $R$ is strictly concave on $[0,1]$ and $\rho^*\in(0,1)$ maximizes it; $v^*=\bar F^{-1}(\rho^*)$;
--   3. (A3) $R$ is twice differentiable on $(0,1)$ with $|R'|,|R''|\le C$ there, and $|R|\le C$ on $[0,1]$.
--
--   This is the model of every result of the paper; $\bar F^{-1}$ and $R$ are derived from it.
--
--   **Formalization Note** $\bar F^{-1}(\rho)$ is `Function.invFunOn` of $\bar F$ on $[0,V]$, the unique price in $[0,V]$ with purchase rate $\rho$ when $\rho\in[0,1]$. A3's derivatives are required only on the open interval $(0,1)$ (nothing is asked at the endpoints; they are written `derivWithin` on $[0,1]$, which is the ordinary derivative at interior points); continuity of $R''$ is not assumed. The density $f$ is not part of the structure.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §3, pp.6–7 (model; assumptions A1–A3, p.7)

import Mathlib

namespace MarkdownReadjust

/-- The inverse demand `F̄⁻¹ : [0,1] → [0,V]` of a survival function `F̄` that is a decreasing
bijection `[0,V] → [0,1]` (Chen–Jasin, SSRN 3740871, §3, p.7: "Since F̄(·) is invertible").

**Formalization Note.** `Function.invFunOn F̄ [0,V] ρ` is the price in `[0,V]` at which the
purchase rate is `ρ`; for a model (`Model`) it is the unique such price whenever `ρ ∈ [0,1]`.
Values at `ρ ∉ [0,1]` are junk and never used (purchase rates are projected onto `[0,1]`). -/
noncomputable def invDemand (Fbar : ℝ → ℝ) (V : ℝ) : ℝ → ℝ :=
  Function.invFunOn Fbar (Set.Icc 0 V)

/-- The revenue rate as a function of the purchase rate, `R(ρ) = ρ F̄⁻¹(ρ)` (SSRN 3740871, p.7). -/
noncomputable def revRate (Fbar : ℝ → ℝ) (V : ℝ) (ρ : ℝ) : ℝ :=
  ρ * invDemand Fbar V ρ

/-- The single-product pricing model of Chen–Jasin (SSRN 3740871, §3, pp.6–7) with
assumptions A1–A3 (p.7).

Customers arrive as a Poisson process of rate `lam`; a customer buys one unit at price `v` iff
her valuation is at least `v`, which happens with probability `F̄(v) = 1 − F(v)`; valuations lie
in `[0, V]`. A1: `F̄(π) → 0` and `R(π) → 0` as `π → V`. A2: `R(ρ) = ρ F̄⁻¹(ρ)` is strictly concave
and has a maximizer `ρ* ∈ (0,1)`. A3: there is `C > 0` bounding `R`, `|R′|` and `|R″|`.

**Formalization Note.** The primitive is the survival function `Fbar` on `[0, V]`: continuous
(valuations have a density), strictly decreasing (the paper's "F̄ is invertible"), `F̄(0) = 1`,
`F̄(V) = 0`. So `F̄` is a decreasing bijection `[0,V] → [0,1]`, and A1 follows from continuity at
`V` (`R(π) = πF̄(π) → V·0`). The density `f` and its derivative `f′` are not used by the paper's
results beyond A1–A3, so they are not part of the structure. A2 and A3 are stated on the purchase
rate interval `[0, 1]`: strict concavity on `[0,1]`, a maximizer `rhoStar ∈ (0,1)` (so
`F̄(v*) = ρ*`), and A3 as twice differentiability on the open interval `(0,1)` with
`|R′| ≤ C`, `|R″| ≤ C` there and `|R| ≤ C` on `[0,1]`; nothing is asked of `R′`, `R″` at the
endpoints `0, 1` (A3 does not say one-sided derivatives exist there), and continuity of `R″` is not
assumed. Derivatives are written `derivWithin · [0,1]`, which equals the ordinary derivative at
interior points. Since `R ≥ 0` on `[0,1]`, "`R(ρ)` bounded by `C`" is `|R(ρ)| ≤ C`. -/
structure Model where
  /-- Poisson arrival rate `λ`. -/
  lam : ℝ
  /-- Upper end `V` of the valuation support (the turn-off price). -/
  V : ℝ
  /-- Survival function `F̄ = 1 − F` of the valuations. -/
  Fbar : ℝ → ℝ
  /-- The maximizer `ρ*` of A2. -/
  rhoStar : ℝ
  /-- The constant `C` of A3. -/
  C : ℝ
  lam_pos : 0 < lam
  V_pos : 0 < V
  C_pos : 0 < C
  Fbar_cont : ContinuousOn Fbar (Set.Icc 0 V)
  Fbar_anti : StrictAntiOn Fbar (Set.Icc 0 V)
  Fbar_zero : Fbar 0 = 1
  Fbar_V : Fbar V = 0
  /-- A2: `R` strictly concave on `[0,1]`. -/
  R_strictConcave : StrictConcaveOn ℝ (Set.Icc 0 1) (revRate Fbar V)
  /-- A2: the maximizer lies in `(0,1)`. -/
  rhoStar_mem : rhoStar ∈ Set.Ioo 0 1
  /-- A2: `ρ*` maximizes `R` on `[0,1]`. -/
  rhoStar_max : ∀ ρ ∈ Set.Icc (0 : ℝ) 1, revRate Fbar V ρ ≤ revRate Fbar V rhoStar
  /-- A3: `R` differentiable on `(0,1)`. -/
  R_diff : DifferentiableOn ℝ (revRate Fbar V) (Set.Ioo 0 1)
  /-- A3: `R′` differentiable on `(0,1)`. -/
  R'_diff : DifferentiableOn ℝ (derivWithin (revRate Fbar V) (Set.Icc 0 1)) (Set.Ioo 0 1)
  /-- A3: `|R| ≤ C` on `[0,1]`. -/
  R_bound : ∀ ρ ∈ Set.Icc (0 : ℝ) 1, |revRate Fbar V ρ| ≤ C
  /-- A3: `|R′| ≤ C` on `(0,1)`. -/
  R'_bound : ∀ ρ ∈ Set.Ioo (0 : ℝ) 1, |derivWithin (revRate Fbar V) (Set.Icc 0 1) ρ| ≤ C
  /-- A3: `|R″| ≤ C` on `(0,1)`. -/
  R''_bound : ∀ ρ ∈ Set.Ioo (0 : ℝ) 1,
    |derivWithin (derivWithin (revRate Fbar V) (Set.Icc 0 1)) (Set.Icc 0 1) ρ| ≤ C

/-- The price `F̄⁻¹(ρ)` at purchase rate `ρ` in the model `M`. -/
noncomputable def Model.Finv (M : Model) : ℝ → ℝ := invDemand M.Fbar M.V

/-- The revenue rate `R(ρ) = ρ F̄⁻¹(ρ)` of the model `M`. -/
noncomputable def Model.R (M : Model) : ℝ → ℝ := revRate M.Fbar M.V

end MarkdownReadjust


