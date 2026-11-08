-- Prove2me | Definitions.Def_FRouting_margQA
-- name    : FRouting_margQA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:49.474562+00:00
-- url     : https://prove2.me/theorems/9643218b-5666-4e08-862d-dca4777a31ec
-- title:
--   Marginals $\rho_{\bar QA},\rho_{\bar QB},\rho_{\bar Q},\rho_A,\rho_B$
-- statement:
--   For an operator $\rho$ on $\bar Q\otimes A\otimes B$, these are its partial traces: $\rho_{\bar QA}=\operatorname{tr}_B\rho$, $\rho_{\bar QB}=\operatorname{tr}_A\rho$, $\rho_{\bar Q}=\operatorname{tr}_{AB}\rho$, $\rho_A=\operatorname{tr}_{\bar QB}\rho$ and $\rho_B=\operatorname{tr}_{\bar QA}\rho$.
--
--   These are the marginals compared by the fidelity gap.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 4.1, p.17

import Definitions.Def_WildeQIT_partialTrace

set_option autoImplicit false

namespace FRouting

open WildeQIT

variable {r a b : Type} [Fintype a] [Fintype b]

/-- **Marginal `ρ_{Q̄A}`** of an operator on `r × (a × b)`: the partial trace over `b`. Renard,
*Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), §4, p.17. -/
def margQA (ρ : Matrix (r × (a × b)) (r × (a × b)) ℂ) : Matrix (r × a) (r × a) ℂ :=
  Matrix.of fun p p' => ∑ k, ρ (p.1, (p.2, k)) (p'.1, (p'.2, k))

/-- **Marginal `ρ_{Q̄B}`** of an operator on `r × (a × b)`: the partial trace over `a`. -/
def margQB (ρ : Matrix (r × (a × b)) (r × (a × b)) ℂ) : Matrix (r × b) (r × b) ℂ :=
  Matrix.of fun p p' => ∑ k, ρ (p.1, (k, p.2)) (p'.1, (k, p'.2))

/-- **Marginal `ρ_{Q̄}`**: the partial trace over `a` and `b`. -/
def margQ (ρ : Matrix (r × (a × b)) (r × (a × b)) ℂ) : Matrix r r ℂ :=
  partialTraceRight (margQA ρ)

/-- **Marginal `ρ_A`**: the partial trace over the reference and `b`. -/
def margA [Fintype r] (ρ : Matrix (r × (a × b)) (r × (a × b)) ℂ) : Matrix a a ℂ :=
  partialTraceLeft (margQA ρ)

/-- **Marginal `ρ_B`**: the partial trace over the reference and `a`. -/
def margB [Fintype r] (ρ : Matrix (r × (a × b)) (r × (a × b)) ℂ) : Matrix b b ℂ :=
  partialTraceLeft (margQB ρ)

end FRouting


