-- Prove2me | Definitions.Def_ScalarMultiRisk_normKK
-- name    : ScalarMultiRisk_normKK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:24.490473+00:00
-- url     : https://prove2.me/theorems/f2f6f164-fac8-4924-b8bd-23fcba102427
-- title:
--   The norm $\|e_i\|_{\mathbb K_T,0}$
-- statement:
--   The paper defines $\|X\|_{\mathbb K_t,s}=\operatorname{ess\,inf}\{c\in L^\infty_s(\mathbb R)\mid ce_1\ge_{\mathbb K_t}X\ge_{\mathbb K_t}-ce_1\}$. Only $\|e_i\|_{\mathbb K_T,0}$ is used, which bounds the admissible prices of asset $i$.
--
--   Since $\mathbb K_T=L^\infty_T(K_T)$ and $\mathcal F_0$ is trivial, this is the real number
--
--   $$\|e_i\|_{\mathbb K_T,0}=\inf\{c\in\mathbb R\mid ce_1-e_i\in K_T\text{ a.s.},\ e_i+ce_1\in K_T\text{ a.s.}\}.$$
--
--   **Formalization Note** The real infimum is used. Under the standing assumptions the set is nonempty and contained in $[0,\infty)$.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, (3.3), p.9

import Mathlib
import Definitions.Def_ScalarMultiRisk_Market
import Definitions.Def_QKPSDP_e1

open MeasureTheory

namespace ScalarMultiRisk

/-- **The norm `‖e_i‖_{𝕂_T,0}`.** arXiv:1807.10694v5, (3.3), p.9:
`‖X‖_{𝕂_t,s} := ess inf{c ∈ L∞_s(ℝ) | c e₁ ≥_{𝕂_t} X ≥_{𝕂_t} −c e₁}`, used in (4.3) and in `𝒬_t`
(p.11) only for `X = e_i`, `t = T`, `s = 0`.

**Formalization Note.** `𝕂_T = L∞_T(K_T)` and `F₀` is trivial, so `c` is a real constant and
the essential infimum is the real infimum of those `c` with `c e₁ − e_i ∈ K_T` a.s. and
`e_i + c e₁ ∈ K_T` a.s. Under `StandingAssumptions` this set is nonempty (`e₁ ∈ int K̄`) and
contained in `[0, ∞)` (`−e₁ ∈ K_T` a.s. would contradict the finiteness of `ρ_T` by
`𝕂_T`-compatibility and cash invariance), so the junk values of the real `sInf` do not occur. -/
noncomputable def normKK {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} [NeZero d]
    (A : Market Ω T d) (i : Fin d) : ℝ :=
  sInf {c : ℝ | (∀ᵐ ω ∂A.P, c • QKPSDP.e1 d - Pi.single i 1 ∈ A.K (Fin.last T) ω) ∧
    ∀ᵐ ω ∂A.P, Pi.single i 1 + c • QKPSDP.e1 d ∈ A.K (Fin.last T) ω}

end ScalarMultiRisk


