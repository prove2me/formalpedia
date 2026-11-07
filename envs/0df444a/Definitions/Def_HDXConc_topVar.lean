-- Prove2me | Definitions.Def_HDXConc_topVar
-- name    : HDXConc_topVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:35.116295+00:00
-- url     : https://prove2.me/theorems/6a844698-294b-4adf-8709-9e693e400744
-- title:
--   Mean and variance under a density on the top level
-- statement:
--   For a density $\rho$ on $X(d)$ and $F:X(d)\to\mathbb R$,
--
--   $$\mathbb E_\rho[F]=\sum_{\sigma\in X(d)}\rho(\sigma)F(\sigma),\qquad \mathrm{Var}_\rho(F)=\sum_{\sigma\in X(d)}\rho(\sigma)\big(F(\sigma)-\mathbb E_\rho[F]\big)^2.$$
--
--   These are finite sums, with no integrability issue.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Proof of Theorem 1.1, p.15

import Mathlib
import Definitions.Def_SteurerHDX_faces

namespace HDXConc

/-!
# Mean and variance under a density on the top level

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), proof of Theorem 1.1, p.15.
-/

variable {V : Type*}

/-- `E_ρ[F] = ∑_{σ ∈ X(d)} ρ(σ) F(σ)`. -/
def topMean (X : Finset (Finset V)) (d : ℕ) (ρ : Finset V → ℝ) (F : Finset V → ℝ) : ℝ :=
  ∑ σ ∈ SteurerHDX.faces X d, ρ σ * F σ

/-- `Var_ρ(F) = ∑_{σ ∈ X(d)} ρ(σ) (F(σ) - E_ρ[F])²`. -/
def topVar (X : Finset (Finset V)) (d : ℕ) (ρ : Finset V → ℝ) (F : Finset V → ℝ) : ℝ :=
  ∑ σ ∈ SteurerHDX.faces X d, ρ σ * (F σ - topMean X d ρ F) ^ 2

end HDXConc


