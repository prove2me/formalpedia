-- Prove2me | Definitions.Def_RecursiveStopping_Finite_Gam
-- name    : RecursiveStopping_Finite_Gam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:25.120466+00:00
-- url     : https://prove2.me/theorems/24067001-966c-4e9b-a2ed-f2f46be9a5b6
-- title:
--   The finite-horizon operator $\Gamma$
-- statement:
--   For $z=(t,x)\in[0,T]\times\mathbb R^{d-1}$,
--
--   $$
--   (\Gamma f)(z):=\sup_{\tau\in\mathcal T_z}\mathsf E\Big[e^{-r\tau}\max\{\varphi(Z^z_\tau),(\Lambda f)(Z^z_\tau)\}\Big],
--   $$
--
--   where $\mathcal T_z$ is the set of $\mathbb F$-stopping times with $\tau\le T-t$ $\mathsf P$-a.s. and $\Lambda$ is (12). Problem 2' asks for $v=\Gamma v$ on $[0,T]\times\mathbb R^{d-1}$.
--
--   **Formalization Note** The gain is computed in $[0,\infty]$ and the expectation is a `lintegral`; the payoff on the null set $\{\tau=\infty\}$ is $0$.
-- source:
--   Colaneri & De Angelis, A Class of Recursive Optimal Stopping Problems with Applications to Stock Trading, arXiv:1905.02650v4, (15), p.10, with §2.2, p.9

import Mathlib
import Definitions.Def_RecursiveStopping_discPayoff
import Definitions.Def_RecursiveStopping_Finite_Lam

open MeasureTheory
open scoped NNReal ENNReal

namespace RecursiveStopping.Finite

/-- The finite-horizon operator `Γ` of Colaneri & De Angelis, arXiv:1905.02650v4, (15), p.10,
with the finite-horizon conventions of §2.2, p.9: for `z = (t, x)`,
$$(\Gamma f)(z) := \sup_{\tau\in\mathcal T} E_z\Big[e^{-r\tau}\max\{\varphi(X_\tau),(\Lambda f)(X_\tau)\}\Big],$$
where "`τ ∈ 𝒯` if it is a stopping time and `τ ∈ [0, T − t]`, `P_z`-a.s." and `Λ` is (12).
Problem 2' asks for `v` with `v = Γv` on `[0, T] × ℝ^{d−1}`.

**Formalization Note** The gain `max{ϕ, Λf}` is computed in `[0, ∞]` and the expectation is a
`lintegral`; the payoff on the null set `{τ = ∞}` is `0` (`discPayoff`). -/
noncomputable def Gam {m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ≥0 mΩ)
    (Z : ℝ × EuclideanSpace ℝ (Fin m) → ℝ≥0 → Ω → ℝ × EuclideanSpace ℝ (Fin m))
    (μ : Measure ℝ≥0) (T r p : ℝ) (ϕ ψ f : ℝ × EuclideanSpace ℝ (Fin m) → ℝ)
    (z : ℝ × EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ⨆ (τ : Ω → ℝ≥0∞) (_ : IsStoppingTime 𝔽 τ ∧ ∀ᵐ ω ∂P, τ ω ≤ ENNReal.ofReal (T - z.1)),
    ∫⁻ ω, discPayoff r (fun y => max (ENNReal.ofReal (ϕ y)) (Lam P Z μ T r p ψ f y)) Z z τ ω ∂P

end RecursiveStopping.Finite


