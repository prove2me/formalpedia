-- Prove2me | Definitions.Def_GrothendieckLB_pmInner
-- name    : GrothendieckLB_pmInner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:36.706911+00:00
-- url     : https://prove2.me/theorems/f0fbfbef-1096-479e-8a6c-ff05d14f7a15
-- title:
--   $\langle P_mF,P_mG\rangle$
-- statement:
--   The inner product of the degree-$m$ Hermite parts of $F,G:\mathbb R^d\to\mathbb R$, where $P_mF$ is the orthogonal projection onto the span of all $\mathrm{He}_\alpha(X)=\prod_i\mathrm{He}_{\alpha_i}(X_i)$ with $|\alpha|=m$:
--   $$
--   \langle P_mF,P_mG\rangle=\sum_{|\alpha|=m}\frac{\mathbb E\big[F(X)\prod_i \mathrm{He}^{\mathrm{monic}}_{\alpha_i}(X_i)\big]\,\mathbb E\big[G(X)\prod_i \mathrm{He}^{\mathrm{monic}}_{\alpha_i}(X_i)\big]}{\prod_i\alpha_i!},\qquad X\sim N(0,I_d).
--   $$
--
--   **Formalization Note** $\mathrm{He}^{\mathrm{monic}}_n$ is Mathlib's probabilists' Hermite polynomial `Polynomial.hermite n`, whose square has Gaussian mean $n!$, so dividing by $\prod_i\alpha_i!$ gives the orthonormal coefficients. The moment sum is the definition; no $L^2$ projection is constructed. For $m=1,3$ it agrees with $\langle P_1F,P_1G\rangle$ and $\langle P_3F,P_3G\rangle$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_gaussExp

namespace GrothendieckLB

/-- `⟨P_mF, P_mG⟩`, the inner product of the degree-`m` Hermite parts of `F` and `G` on `ℝ^d`
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31: `P_mF` is the orthogonal projection onto the span of all
`He_α` with `|α| = m`, `He_α(X) = ∏ᵢ He_{αᵢ}(Xᵢ)`).

**Formalization Note** `Polynomial.hermite n` is the monic probabilists' Hermite polynomial, whose
square has Gaussian mean `n!`; the orthonormal `He_α` of the page is `∏ᵢ hermite αᵢ (Xᵢ) / √(αᵢ!)`.
So `⟨P_mF, P_mG⟩ = ∑_{|α| = m} E[F ∏ᵢ hermite αᵢ(Xᵢ)] E[G ∏ᵢ hermite αᵢ(Xᵢ)] / ∏ᵢ αᵢ!`, the sum
running over `Finset.Nat.antidiagonalTuple d m` (all `α : Fin d → ℕ` with `∑ αᵢ = m`). The moment sum
is the definition; no `L²` projection is constructed. For `m = 1` and `m = 3` it agrees with
`p1Inner` and `p3Inner`. -/
noncomputable def pmInner {d : ℕ} (m : ℕ) (F G : (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple d m,
    (gaussExp fun x => F x * ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) *
    (gaussExp fun x => G x * ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) /
    ∏ i, ((α i).factorial : ℝ)

end GrothendieckLB


