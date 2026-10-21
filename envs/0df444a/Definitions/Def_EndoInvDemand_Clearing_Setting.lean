-- Prove2me | Definitions.Def_EndoInvDemand_Clearing_Setting
-- name    : EndoInvDemand_Clearing_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:07.627388+00:00
-- url     : https://prove2.me/theorems/a3d789c5-1448-47b8-90ac-fbd525cb9f95
-- title:
--   §2–§3, pp. 4, 7–8 — domain 𝔻, Assumptions 2.1 and 3.1, the weight exp(−R(·)), H_Z and V(Z) (3.1), dom H_Z, Θ_Z, comonotonicity, conditions (a)–(d)
-- statement:
--   The objects of the clearing-price problem of Bichuch and Feinstein.
--
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space. The **domain** $\mathbb D$ of the market participants' utility functions is either the real line $\mathbb R$ or the open half line $\mathbb R_{++}=(0,\infty)$.
--
--   1. **Assumption 2.1.** The aggregate endowment $\mathcal X$ is essentially bounded ($\mathcal X\in L^\infty$), lies in $\mathbb D$ almost surely, and $\operatorname{ess\,inf}\mathcal X\in\mathbb D$.
--   2. **Assumption 3.1.** The function $R:\mathbb D\to\mathbb R$ (the integral of the absolute risk aversion of the harmonic representative agent) is strictly increasing, differentiable and concave on $\mathbb D$. If $\mathbb D=\mathbb R_{++}$, $R(0)=\lim_{z\searrow0}R(z)$ in the broad sense, possibly $-\infty$.
--   3. **The weight** $y\mapsto\exp(-R(y))\in[0,\infty]$. For $\mathbb D=\mathbb R_{++}$ its value at $y=0$ is $\sup_{z>0}\exp(-R(z))=\lim_{z\searrow0}\exp(-R(z))=\exp(-R(0))$, which is $+\infty$ exactly when $R(0)=-\infty$.
--   4. **The pricing map** of a claim $Z\in L^\infty$, display (3.1):
--   $$H_Z(v)=\frac{\mathbb E\big[Z\exp(-R(\mathcal X+Z-v))\big]}{\mathbb E\big[\exp(-R(\mathcal X+Z-v))\big]}.$$
--   5. **Its domain**: $\operatorname{dom}H_Z=\mathbb R$ if $\mathbb D=\mathbb R$; if $\mathbb D=\mathbb R_{++}$, $\operatorname{dom}H_Z$ is the set of $v\in\mathbb R$ with $\mathbb P(\mathcal X+Z\ge v)=1$ and $\mathbb E[\exp(-R(\mathcal X+Z-v))]<\infty$.
--   6. **The clearing prices** $V(Z)=\{v\in\operatorname{dom}H_Z \mid v=H_Z(v)\}$, display (3.1).
--   7. The auxiliary function $\Theta_Z(v)=\mathbb E\big[(Z-v)\exp(-R(\mathcal X+Z-v))\big]$ from the proof of Theorem 3.3.
--   8. Two random variables $Y,W$ are **comonotonic** if $(Y(\omega)-Y(\bar\omega))(W(\omega)-W(\bar\omega))\ge0$ for $\mathbb P\otimes\mathbb P$-almost every $(\omega,\bar\omega)$.
--   9. **The conditions of Theorem 3.3**: (a) $Z$ and $\mathcal X+Z$ are comonotonic; (b) $R$ is linear (affine) on $\mathbb D$; (c) $z\in\mathbb R_{++}\mapsto z\exp(-R(\mathcal X+z))$ is almost surely non-decreasing; (d) the same map is almost surely concave.
--
--   A clearing price $v\in V(Z)$ is the price at which a claim $Z$ liquidated into a Bühlmann-type equilibrium market clears; the mission's theorems are about existence, uniqueness and location of such prices.
--
--   **Formalization Note** Only the aggregate $\mathcal X=\sum_i X_i$ is modelled: $H_Z$ depends on the endowments only through it, so Assumption 2.1 is stated for $\mathcal X$. $R$ is a function on $\mathbb R$ of which only the restriction to $\mathbb D$ is constrained and read; for $\mathbb D=\mathbb R_{++}$ the broad-sense value $R(0)$ enters only through the weight at $0$, defined as a supremum in $[0,\infty]$ (for $y<0$ the weight takes the same constant; such arguments never occur on $\operatorname{dom}H_Z$). The denominator of $H_Z$ is a lower Lebesgue integral in $[0,\infty]$; the numerator and $\Theta_Z$ are Bochner integrals. The paper's $\operatorname{dom}H_Z$ for $\mathbb D=\mathbb R_{++}$ requires the denominator to be $>0$, which always holds; it is read as finite, since $H_Z$ has no value when the denominator is $+\infty$ (the proof of Corollary 3.5 uses exactly this reading). "Linear" in (b) is affine on $\mathbb D$, as in the paper's case $R(x)=\alpha(x-\operatorname{ess\,inf}\mathcal X)$. Comonotonicity is the $\mathbb P\otimes\mathbb P$-a.e. form, which does not depend on the versions of $Z$ and $\mathcal X$.
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, §2 Assumption 2.1 p. 4; §3 Assumption 3.1 and (3.1) p. 7; dom H_Z p. 8; Theorem 3.3 (a)–(d) pp. 9–10; Θ_Z in the proof of Theorem 3.3 (Online Appendix D.2) p. 32

import Mathlib

namespace EndoInvDemand.Clearing

open MeasureTheory
open scoped ENNReal Topology

/-- §2, p. 4: the common domain `𝔻 = dom uᵢ` of the utility functions, either the whole real
line (`real`, 𝔻 = ℝ) or the open half line (`pos`, 𝔻 = ℝ₊₊ = (0, ∞)). -/
inductive Dom
  | real
  | pos

/-- The set `𝔻 ⊆ ℝ` named by the flag. -/
def Dom.set : Dom → Set ℝ
  | .real => Set.univ
  | .pos => Set.Ioi 0

/-- Assumption 3.1, p. 7: `R : 𝔻 → ℝ` is strictly increasing, differentiable and concave.
`R` is a function on `ℝ`; only its restriction to `𝔻` is constrained (and read). -/
def Assumption31 (D : Dom) (R : ℝ → ℝ) : Prop :=
  StrictMonoOn R D.set ∧ DifferentiableOn ℝ R D.set ∧ ConcaveOn ℝ D.set R

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Assumption 2.1, p. 4, for the aggregate endowment `𝒳 = ∑ᵢ Xᵢ`: `𝒳 ∈ L∞`, `𝒳 ∈ 𝔻` a.s.,
and `ess inf 𝒳 ∈ 𝔻`. -/
def Assumption21 (P : Measure Ω) (D : Dom) (X : Ω → ℝ) : Prop :=
  MemLp X ⊤ P ∧ (∀ᵐ ω ∂P, X ω ∈ D.set) ∧ essInf X P ∈ D.set

/-- The weight `exp(−R(y))`, valued in `[0, ∞]`. For `𝔻 = ℝ₊₊` the value at `y = 0` uses
`R(0) = lim_{z↘0} R(z)` in the broad sense (p. 7): it is `sup_{z > 0} exp(−R(z))`, which equals
`lim_{z↘0} exp(−R(z))` for increasing `R` and is `+∞` exactly when `R(0) = −∞`. For `y < 0` the
value is never read (`dom H_Z` forces `y ≥ 0` a.s.); the same constant is used there. -/
noncomputable def weight (D : Dom) (R : ℝ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  match D with
  | .real => ENNReal.ofReal (Real.exp (-R y))
  | .pos =>
      if 0 < y then ENNReal.ofReal (Real.exp (-R y))
      else ⨆ z ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-R z))

/-- The denominator `𝔼[exp(−R(𝒳 + Z − v))] ∈ [0, ∞]` of `H_Z(v)`. -/
noncomputable def denom (P : Measure Ω) (D : Dom) (R : ℝ → ℝ) (X Z : Ω → ℝ) (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, weight D R (X ω + Z ω - v) ∂P

/-- `dom H_Z`, p. 8: all of `ℝ` if `𝔻 = ℝ`; if `𝔻 = ℝ₊₊`, the prices `v` with
`ℙ(𝒳 + Z ≥ v) = 1` at which the denominator `𝔼[exp(−R(𝒳 + Z − v))]` is finite (the page's
`> 0` always holds; finiteness is what makes the ratio `H_Z(v)` defined). -/
def domH (P : Measure Ω) (D : Dom) (R : ℝ → ℝ) (X Z : Ω → ℝ) : Set ℝ :=
  match D with
  | .real => Set.univ
  | .pos => {v | (∀ᵐ ω ∂P, v ≤ X ω + Z ω) ∧ denom P .pos R X Z v < ⊤}

/-- (3.1), p. 7: `H_Z(v) = 𝔼[Z exp(−R(𝒳 + Z − v))] / 𝔼[exp(−R(𝒳 + Z − v))]`. -/
noncomputable def H (P : Measure Ω) (D : Dom) (R : ℝ → ℝ) (X Z : Ω → ℝ) (v : ℝ) : ℝ :=
  (∫ ω, Z ω * (weight D R (X ω + Z ω - v)).toReal ∂P) / (denom P D R X Z v).toReal

/-- (3.1), p. 7: the set of clearing prices `V(Z) = {v ∈ dom H_Z | v = H_Z(v)}`. -/
def V (P : Measure Ω) (D : Dom) (R : ℝ → ℝ) (X Z : Ω → ℝ) : Set ℝ :=
  {v | v ∈ domH P D R X Z ∧ v = H P D R X Z v}

/-- Proof of Theorem 3.3, p. 32: `Θ_Z(v) = 𝔼[(Z − v) exp(−R(𝒳 + Z − v))]`. -/
noncomputable def Theta (P : Measure Ω) (D : Dom) (R : ℝ → ℝ) (X Z : Ω → ℝ) (v : ℝ) : ℝ :=
  ∫ ω, (Z ω - v) * (weight D R (X ω + Z ω - v)).toReal ∂P

/-- `Y` and `W` are comonotonic: `(Y(ω) − Y(ω̄))(W(ω) − W(ω̄)) ≥ 0` for `ℙ ⊗ ℙ`-a.e. `(ω, ω̄)`. -/
def Comonotone (P : Measure Ω) (Y W : Ω → ℝ) : Prop :=
  ∀ᵐ p ∂(P.prod P), 0 ≤ (Y p.1 - Y p.2) * (W p.1 - W p.2)

/-- Theorem 3.3 (a), p. 9: `Z` and `𝒳 + Z` are comonotonic. -/
def condA (P : Measure Ω) (X Z : Ω → ℝ) : Prop :=
  Comonotone P Z (fun ω => X ω + Z ω)

/-- Theorem 3.3 (b), p. 9: `R` is linear (affine) on `𝔻`. -/
def condB (D : Dom) (R : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ z ∈ D.set, R z = a * z + b

/-- Theorem 3.3 (c), p. 9: `z ∈ ℝ₊₊ ↦ z exp(−R(𝒳 + z))` is almost surely non-decreasing. -/
def condC (P : Measure Ω) (R : ℝ → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, MonotoneOn (fun z => z * Real.exp (-R (X ω + z))) (Set.Ioi 0)

/-- Theorem 3.3 (d), p. 10: `z ∈ ℝ₊₊ ↦ z exp(−R(𝒳 + z))` is almost surely concave. -/
def condD (P : Measure Ω) (R : ℝ → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ConcaveOn ℝ (Set.Ioi 0) (fun z => z * Real.exp (-R (X ω + z)))

/-- Any of the conditions (a)–(d) of Theorem 3.3, pp. 9–10. -/
def Thm33Cond (P : Measure Ω) (D : Dom) (R : ℝ → ℝ) (X Z : Ω → ℝ) : Prop :=
  condA P X Z ∨ condB D R ∨ condC P R X ∨ condD P R X

end EndoInvDemand.Clearing


