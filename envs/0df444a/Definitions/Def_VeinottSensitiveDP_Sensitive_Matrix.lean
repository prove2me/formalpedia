-- Prove2me | Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
-- name    : VeinottSensitiveDP_Sensitive_Matrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:39.667499+00:00
-- url     : https://prove2.me/theorems/af7e4a79-73d5-439c-bc9c-b56bb69e2f02
-- title:
--   Substochastic matrices, the spectral radius |σ(B)|, the resolvent R_λ(B), σ₀(B)ᶜ and the reduced resolvent H_ρ (§§2–3)
-- statement:
--   Let $B$ be a real $S\times S$ matrix and $P$ an $S\times S$ real matrix.
--
--   1. $P$ is **substochastic** if its entries are nonnegative and every row sum is at most $1$; equivalently $P\ge 0$ and $\|P\|=\max_i\sum_j|p_{ij}|\le 1$.
--   2. The **spectral radius** $|\sigma(B)|$ is the largest modulus of a complex eigenvalue of $B$.
--   3. The **resolvent** of $B$ at a real $\lambda$ is $R_\lambda(B)=[\lambda I-B]^{-1}$.
--   4. For a scalar $\delta$, $\sigma_\delta(B)=\sigma(B)-\{\delta\}$; a real $\rho$ lies in $\sigma_0(B)^c$ when $\rho=0$ or $\rho$ is not an eigenvalue of $B$.
--   5. With $Q=P-I$ and $P^*$ the Cesàro limit of the powers of $P$, the **reduced resolvent** of $Q$ is
--   $$H_\rho=R_\rho(Q)\,(I-P^*)\quad(\rho\neq 0),\qquad H_0=(I-P+P^*)^{-1}-P^*.$$
--
--   These are the matrix tools of Veinott's §3: the resolvent $R_\rho(Q)$ has a pole at $\rho=0$ when $P^*\ne0$, and $H_\rho$ is its regular part, $R_\rho(Q)=\rho^{-1}P^*+H_\rho$.
--
--   **Formalization Note** The spectral radius is Mathlib's `spectralRadius ℂ` of the complexified matrix, an extended nonnegative real. The inverse is Mathlib's total matrix inverse ($0$ for a singular matrix), so $R_\lambda(B)$ is meaningful only for $\lambda\notin\sigma(B)$, and $H_\rho$ only on $\sigma_0(Q)^c$; that $H_\rho$ is there the unique solution of Veinott's (17) is Lemma 5, a theorem. The paper's $H_0=R_0(Q-P^*)(I-P^*)=(I-P+P^*)^{-1}(I-P^*)$ equals $(I-P+P^*)^{-1}-P^*$ because $(I-P+P^*)P^*=P^*$; the latter is the published deviation matrix. $P^*$ is the published `limitMatrix`.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, pp. 1636 (norm, spectral radius), 1640 (resolvent), 1642 (substochastic P, σ_δ), 1642–1643 (reduced resolvent, proof of Lemma 5)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Transient_Similarity
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

variable {St : Type} [Fintype St] [DecidableEq St]

/-- A square real matrix is **substochastic**: its entries are nonnegative and every row sum is at
most one (equivalently, it is nonnegative and `‖P‖ = maxᵢ Σⱼ |pᵢⱼ| ≦ 1`).

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1642, §3
("an S × S substochastic matrix P") and p. 1644, §4 ("‖P(g)‖ ≦ 1 for all g ε F"). -/
def IsSubstochastic (P : Matrix St St ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j ≤ 1

/-- The resolvent `R_λ(B) ≡ [λI − B]⁻¹` of a real square matrix `B` at a real `λ`.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1640, §3.

**Formalization Note.** `⁻¹` is Mathlib's total matrix inverse, which is `0` when `λI − B` is
singular, i.e. when `λ ε σ(B)`; every statement using `R_λ(B)` either assumes or proves
`λ ∉ σ(B)`. The scalar `λ` is real throughout §§3–4 of the paper (complex `ρ` is first permitted
in §5, Lemma 13). -/
noncomputable def resolvent (lam : ℝ) (B : Matrix St St ℝ) : Matrix St St ℝ :=
  (lam • (1 : Matrix St St ℝ) - B)⁻¹

/-- Membership of a real scalar `ρ` in `σ₀(B)ᶜ`, where `σ_δ(B) = σ(B) − {δ}` (p. 1642): `ρ = 0`, or
`ρ` is not an eigenvalue of `B`.

Veinott (1969), DOI 10.1214/aoms/1177697379, p. 1642, §3.

**Formalization Note.** For a real scalar, `ρ ε σ(B)` is `ρ ∈ spectrum ℝ B` (`ρI − B` is not
invertible, i.e. `det(ρI − B) = 0`), which is the same as `ρ` being a complex eigenvalue of `B`. -/
def InSigmaZeroCompl (ρ : ℝ) (B : Matrix St St ℝ) : Prop :=
  ρ = 0 ∨ ρ ∉ spectrum ℝ B

/-- The **reduced resolvent** `H_ρ` of `Q = P − I` for a square matrix `P` with Cesàro limit
`P* = limitMatrix P`:

* `H_ρ ≡ R_ρ(Q)(I − P*)` for `ρ ≠ 0` (meaningful for `ρ ε σ(Q)ᶜ − {0}`),
* `H₀ ≡ (I − P + P*)⁻¹ − P*`, the deviation matrix `deviationMatrix P` (meaningful when
  `I − P + P*` is nonsingular).

Veinott (1969), DOI 10.1214/aoms/1177697379, pp. 1642–1643, §3, proof of Lemma 5.

**Formalization Note.** The paper defines `H₀ ≡ R₀(Q − P*)(I − P*) = (I − P + P*)⁻¹(I − P*)`;
since `(I − P + P*)P* = P*` by (15), this equals `(I − P + P*)⁻¹ − P*`, the published
`deviationMatrix P` (Blackwell's `H`). Outside `σ₀(Q)ᶜ` the paper leaves `H_ρ` undefined and the
value here is meaningless (total inverse). That `H_ρ` is the unique common solution of (17) on
`σ₀(Q)ᶜ` is Lemma 5, a theorem. The closed form `(ρI − Q + P*)⁻¹(I − P*)` is not used, because
it fails at `ρ = −1` when `P* ≠ 0`. -/
noncomputable def reducedResolvent (P : Matrix St St ℝ) (ρ : ℝ) : Matrix St St ℝ :=
  if ρ = 0 then deviationMatrix P
  else resolvent ρ (P - 1) * (1 - limitMatrix P)

end VeinottSensitiveDP.Sensitive


