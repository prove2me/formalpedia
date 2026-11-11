-- Prove2me | Definitions.Def_QDSGibbs_cov
-- name    : QDSGibbs_cov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:11.865465+00:00
-- url     : https://prove2.me/theorems/1066e1d3-92aa-42d4-b1b7-d795a08bf054
-- title:
--   Covariance, full-space marginals and products of marginals, and the boundary constant $A_u$
-- statement:
--   For a state $\rho$ the **covariance** is $\mathrm{Cov}_\rho(A,B)=\mathrm{Tr}(\rho AB)-\mathrm{Tr}(\rho A)\mathrm{Tr}(\rho B)$. The **marginal** on $U$ is $\rho_U=\mathrm{Tr}_{U^c}\rho$, and for disjoint $P,Q$ the product of marginals is $\rho_P\otimes\rho_Q$. For a profile $f$, constants $M,C_{\mathrm{cl}}$ and a local dimension bound $d$, the **boundary constant** is
--
--   $$
--   A_u=8(u+1)+4\sum_{v=0}^\infty\min\{1,\,3M^8C_{\mathrm{cl}}d^{4(u+1)}f(v)\}.
--   $$
--
--   **Formalization Note** Marginals and products are full-space operators: $\rho_U\otimes\mathbb 1/\dim\mathcal H_{U^c}$ and $\rho_P\otimes\rho_Q\otimes\mathbb 1/\dim\mathcal H_{(P\cup Q)^c}$; trace norms are unchanged. $A_u$ takes values in $[0,\infty]$, so a divergent series gives $\infty$, never the junk $0$ of a non-summable real series.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), §5.1, p.39; (5.19), p.45; (5.20), p.46

import Mathlib
import Definitions.Def_QDSGibbs_Op

open scoped Matrix ENNReal

namespace QDSGibbs

/-- The **covariance** `Cov_ρ(A, B) = Tr(ρAB) − Tr(ρA) Tr(ρB)` (arXiv:2610.03578, held file sha256
ede55815…, §5.1, p.39). -/
def cov {n : Type} [Fintype n] (ρ A B : Matrix n n ℂ) : ℂ :=
  (ρ * A * B).trace - (ρ * A).trace * (ρ * B).trace

/-- The **marginal** `ρ_U = Tr_{U^c} ρ` (arXiv:2610.03578, §2.1, p.10), in the full-space form
`ρ_U ⊗ 1_{U^c} / dim H_{U^c} = ptr U^c ρ / dim H_{U^c}`.

**Formalization Note** The trace norm is unchanged by tensoring with the normalized identity, so
trace-norm statements about marginals read the same. -/
noncomputable def marg {N : ℕ} {d : Fin N → ℕ} (U : Finset (Fin N)) (ρ : Op d) : Op d :=
  ((dimOf d Uᶜ : ℂ))⁻¹ • ptr Uᶜ ρ

/-- The product of marginals `ρ_P ⊗ ρ_Q` for disjoint `P, Q` (arXiv:2610.03578, (5.19), p.45), in the
full-space form `ρ_P ⊗ ρ_Q ⊗ 1_R / dim H_R`, `R = (P ∪ Q)^c`.

**Formalization Note** `marg P ρ * marg Q ρ = ρ_P ⊗ ρ_Q ⊗ 1_R / (dim H_{P^c} dim H_{Q^c})`, and
`dim H_{P^c} dim H_{Q^c} = dim H_Λ · dim H_R`, so the factor `dim H_Λ` gives the normalized form. -/
noncomputable def margProd {N : ℕ} {d : Fin N → ℕ} (P Q : Finset (Fin N)) (ρ : Op d) : Op d :=
  ((dimOf d Finset.univ : ℂ)) • (marg P ρ * marg Q ρ)

/-- The **boundary constant** `A_u = 8(u+1) + 4 Σ_{v=0}^∞ min{1, 3 M^8 C_cl d^{4(u+1)} f(v)}`
(arXiv:2610.03578, (5.20), p.46), for a profile `f`, constants `M, C_cl` and local dimension bound `d`.

**Formalization Note** Valued in `ℝ≥0∞`: the series of nonnegative terms may diverge, and then
`A_u = ⊤` (never the junk `0` of a non-summable real `tsum`). For a nonnegative profile
`ENNReal.ofReal` is exact on each term. -/
noncomputable def aU (M Ccl : ℝ) (D : ℕ) (f : ℝ → ℝ) (u : ℕ) : ℝ≥0∞ :=
  8 * ((u : ℝ≥0∞) + 1) +
    4 * ∑' v : ℕ, ENNReal.ofReal (min 1 (3 * M ^ 8 * Ccl * (D : ℝ) ^ (4 * (u + 1)) * f (v : ℝ)))

end QDSGibbs


