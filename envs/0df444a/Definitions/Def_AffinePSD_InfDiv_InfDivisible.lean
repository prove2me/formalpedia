-- Prove2me | Definitions.Def_AffinePSD_InfDiv_InfDivisible
-- name    : AffinePSD_InfDiv_InfDivisible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:43.279141+00:00
-- url     : https://prove2.me/theorems/fcba200f-5439-47f2-a55a-4a82018f6ed5
-- title:
--   Infinite divisibility of sub-stochastic marginals (Definition 2.7(ii)) and "affine with vanishing diffusion parameter $\alpha=0$"
-- statement:
--   A sub-probability measure $\mu$ on $S_d^+$ is **infinitely divisible** if for every $k\ge1$ there is a sub-probability measure $\mu_k$ on $S_d^+$ with
--   $$\mu=\underbrace{\mu_k*\dots*\mu_k}_{k},$$
--   the convolution being taken in $M_d$, where $S_d^+$ sits as a convex cone.
--
--   A transition family $p$ has **infinitely divisible marginals** (Definition 2.7(ii)) if $p_t(x,\cdot)$, the one-dimensional marginal $P_x\circ X_t^{-1}$ restricted to $S_d^+$, is infinitely divisible for all $(t,x)\in\mathbb R_+\times S_d^+$.
--
--   The process is **affine with vanishing diffusion parameter** if it is affine (Definition 2.1) with exponents $\varphi,\psi$, and there is an admissible parameter set $(\alpha,b,\beta^{ij},c,\gamma,m,\mu)$ with $\alpha=0$ whose functions $F,R$ of (2.16)–(2.17) drive the Riccati equations (2.14)–(2.15) solved by $\varphi,\psi$. That is the parameter set of Theorem 2.4.
--
--   **Formalization Note** The marginal $P_x\circ X_t^{-1}$ lives on $S_d^+\cup\{\Delta\}$. When $\Delta$ is absorbing for addition, it is infinitely divisible exactly when its restriction to $S_d^+$, the sub-stochastic kernel $p_t(x,\cdot)$, is infinitely divisible as a sub-probability measure. The mass at $\Delta$ is the killing, so roots are not required to be probability measures. $F$ and $R$ determine the parameter set, so the existential refers to *the* parameter set of Theorem 2.4. The diffusion parameter $\alpha$ does not depend on the truncation function $\chi$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §2, Definition 2.7(ii), p. 12; Theorem 2.9(ii)–(iii), p. 12; Theorem 2.4, pp. 9–10

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone
import Definitions.Def_AffinePSD_Necessity_Params
import Definitions.Def_AffinePSD_Necessity_Process

open MeasureTheory ProbabilityTheory

namespace AffinePSD.InfDiv

/-- A sub-probability measure `μ` on `S_d^+` is infinitely divisible if for every `k ≥ 1` there is a
sub-probability measure `μ_k` on `S_d^+` whose `k`-fold convolution is `μ` (the convolution is
taken in `M_d`, where `S_d^+` sits as a convex cone).
Formalization Note: the marginal `P_x ∘ X_t^{−1}` lives on `S_d^+ ∪ {Δ}`; with `Δ` absorbing for
addition, it is infinitely divisible iff its restriction to `S_d^+` (the sub-stochastic kernel
`p_t(x, ·)`) is infinitely divisible in this sense. Mass at `Δ` is the killing. -/
def InfDivSub {d : ℕ} (μ : Measure (AffinePSD.Necessity.Cone d)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ (μk : Measure (AffinePSD.Necessity.Cone d)) (_ : IsFiniteMeasure μk), μk Set.univ ≤ 1 ∧
    (Measure.pi (fun _ : Fin k => μk)).map (fun ys => ∑ i, (ys i).1) = μ.map Subtype.val

/-- Definition 2.7(ii) (p. 12), at the level of the transition family: every one-dimensional
marginal `P_x ∘ X_t^{−1}` (restricted to `S_d^+`, i.e. `p_t(x, ·)`) is infinitely divisible,
for all `(t, x) ∈ ℝ_+ × S_d^+`. -/
def InfDivMarginals {d : ℕ} (p : ℝ → Kernel (AffinePSD.Necessity.Cone d) (AffinePSD.Necessity.Cone d)) : Prop :=
  ∀ t, 0 ≤ t → ∀ x, InfDivSub (p t x)

/-- "`X` is affine with vanishing diffusion parameter `α = 0`" (Theorem 2.9(ii), p. 12): `X` is
affine (Definition 2.1) with exponents `φ, ψ`, and the admissible parameter set
`(α, b, β^{ij}, c, γ, m, μ)` of Theorem 2.4, whose `F, R` drive the Riccati equations
(2.14)–(2.15) solved by `φ, ψ`, has `α = 0`.
Formalization Note: `F` and `R` determine the parameter set, so the existential names *the*
parameter set of Theorem 2.4; `α` does not depend on the truncation function `χ`. -/
def AffineZeroDiff {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (p : ℝ → Kernel (AffinePSD.Necessity.Cone d) (AffinePSD.Necessity.Cone d)) : Prop :=
  ∃ (φ : ℝ → AffinePSD.Necessity.Mat d → ℝ) (ψ : ℝ → AffinePSD.Necessity.Mat d → AffinePSD.Necessity.Mat d), AffinePSD.Necessity.IsAffineWith p φ ψ ∧
    ∃ P : AffinePSD.Necessity.Params d, AffinePSD.Necessity.Admissible χ P ∧ P.α = 0 ∧ AffinePSD.Necessity.SolvesRiccati (AffinePSD.Necessity.Fpar P) (AffinePSD.Necessity.Rpar χ P) φ ψ

end AffinePSD.InfDiv


