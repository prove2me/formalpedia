-- Prove2me | Definitions.Def_ShortWDRODual_Legendre_Setting
-- name    : ShortWDRODual_Legendre_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:49.434122+00:00
-- url     : https://prove2.me/theorems/f3704c52-64a1-42a7-b56c-62b7092c210b
-- title:
--   §1–§2, pp. 1–5 — Γ_ℙ̂, worst-case loss (P) over the Kantorovich ball (1), (P-soft), λc with 0·∞ = ∞, (IP), Legendre transform, 𝒢(λ)
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space, let $f:\mathcal X\to\mathbb R$ be a loss function and let $c:\mathcal X\times\mathcal X\to[0,\infty]$ be a transport cost, whose first argument is the nominal point. Expectations take values in $\bar{\mathbb R}=[-\infty,\infty]$ and are computed as $\mathbb E[\varphi]=\int\varphi^+-\int\varphi^-$. A function is $\widehat{\mathbb P}$-measurable when it is measurable for the completion of $\mathcal F$ under $\widehat{\mathbb P}$.
--
--   1. **Couplings.** $\Gamma(\widehat{\mathbb P},\mathbb P)$ is the set of probability measures on $\mathcal X\times\mathcal X$ with marginals $\widehat{\mathbb P}$ and $\mathbb P$; $\Gamma_{\widehat{\mathbb P}}$ is the set of probability measures on $(\mathcal X\times\mathcal X,\mathcal F\otimes\mathcal F)$ with first marginal $\widehat{\mathbb P}$.
--   2. **Kantorovich transport cost (1).** $\mathcal K_c(\widehat{\mathbb P},\mathbb P)=\inf_{\gamma\in\Gamma(\widehat{\mathbb P},\mathbb P)}\mathbb E_{(\widehat X,X)\sim\gamma}[c(\widehat X,X)]\in[0,\infty]$.
--   3. **Worst-case loss (P).** For $\rho\in\mathbb R$,
--   $$\mathcal L(\rho)=\sup_{\mathbb P\in\mathcal P(\mathcal X)}\big\{\mathbb E_{X\sim\mathbb P}[f(X)]:\mathcal K_c(\widehat{\mathbb P},\mathbb P)\le\rho\big\},$$
--   the supremum of the empty set being $-\infty$; in particular $\mathcal L(\rho)=-\infty$ for $\rho<0$.
--   4. **The product $\lambda c$** with the convention $0\cdot\infty=\infty$: it is $+\infty$ when $c=\infty$ and the ordinary product otherwise. The penalized integrand is $\phi_\lambda(\widehat x,x)=f(x)-\lambda c(\widehat x,x)$.
--   5. **Pointwise supremum** $\Phi(\widehat x)=\sup_{x\in\mathcal X}\phi(\widehat x,x)$ for $\phi:\mathcal X\times\mathcal X\to\bar{\mathbb R}$.
--   6. **Interchangeability principle (IP).** An $(\mathcal F\otimes\mathcal F)$-measurable $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ satisfies (IP) if $\widehat x\mapsto\sup_x\phi(\widehat x,x)$ is $\widehat{\mathbb P}$-measurable and
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\phi(\widehat X,x)\Big]=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[\phi(\widehat X,X)\big].$$
--   7. **Legendre transform.** For $h:\mathbb R\to\bar{\mathbb R}$, $h^*(\lambda)=\sup_{\rho\in\mathbb R}\{\lambda\rho-h(\rho)\}$; if $h$ attains $-\infty$ somewhere, then $h^*\equiv+\infty$.
--   8. **Soft-penalty value (P-soft).** For $\lambda\in\mathbb R$, $\sup_{\mathbb P\in\bar{\mathcal P}}\{\mathbb E_{X\sim\mathbb P}[f(X)]-\lambda\mathcal K_c(\widehat{\mathbb P},\mathbb P)\}$, where $\bar{\mathcal P}$ is the set of probability measures with $\mathcal K_c(\widehat{\mathbb P},\mathbb P)<\infty$.
--   9. **The dual function** $\mathcal G(\lambda)=\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\big[\sup_{x\in\mathcal X}\{f(x)-\lambda c(\widehat X,x)\}\big]$.
--
--   These are the objects of Theorem 1, the paper's strong duality theorem, and of the auxiliary Lemmas 1–3.
--
--   **Formalization Note** The Kantorovich cost (1) is the published `RWPI.SqrtLasso.transportCost` (infimum over probability couplings with both marginals fixed of the lower Lebesgue integral of $c$, in $[0,\infty]$; $+\infty$ when no coupling exists). Expectations use the published `ModelRiskOT.Duality.extIntegral` ($\int\varphi^+-\int\varphi^-$ with lower Lebesgue integrals, in `EReal`). It agrees with the paper whenever one of the two parts is finite and assigns $-\infty$ to the undefined case $\infty-\infty$, so a law or coupling with an undefined expectation never raises a supremum. The constraint $\mathcal K_c\le\rho$ is compared in `EReal`, so $\mathcal L(\rho)=-\infty$ for $\rho<0$. The cost is `ENNReal`-valued and curried, `c x̂ x`. The product $\lambda c$ is a separate function `lamMul`, because Mathlib's `EReal` product has $0\cdot\infty=0$. $\widehat{\mathbb P}$-measurability is `NullMeasurable`. Functions into $\mathbb R\cup\{-\infty\}$ are `EReal`-valued with the side condition "never $+\infty$". $\mathcal G$ is only used for $\lambda\ge0$; the paper's extension $\mathcal G(\lambda)=+\infty$ for $\lambda<0$ is not part of the definition.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, §1 (P), (1), p. 1 (PDF p. 1); §2.1 Notations, (P-soft), (IP), pp. 2–3 (PDF pp. 2–3); Theorem 1 and its proof (φ_λ, 𝒢(λ)), pp. 3–5 (PDF pp. 3–5)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_RWPI_SqrtLasso_transportCost

namespace ShortWDRODual.Legendre

open MeasureTheory ModelRiskOT.Duality RWPI.SqrtLasso

variable {X : Type*} [MeasurableSpace X]

/-- `Γ_ℙ̂` (p. 3): probability measures on `(𝒳 × 𝒳, ℱ ⊗ ℱ)` whose first marginal is `ℙ̂`. -/
def couplingsFst (Phat : Measure X) : Set (Measure (X × X)) :=
  {γ | IsProbabilityMeasure γ ∧ γ.map Prod.fst = Phat}

/-- The worst-case loss (P), p. 1:
`𝓛(ρ) = sup {𝔼_ℙ[f] : ℙ ∈ 𝒫(𝒳), 𝒦_c(ℙ̂, ℙ) ≤ ρ}`, where the Kantorovich transport cost (1),
`𝒦_c(ℙ̂, ℙ) = inf_{γ ∈ Γ(ℙ̂, ℙ)} 𝔼_γ[c(X̂, X)]` with `c : 𝒳 × 𝒳 → [0, ∞]` written curried as `c x̂ x`, is
the published `RWPI.SqrtLasso.transportCost c Phat P`. The constraint is compared in `EReal`, so for
`ρ < 0` no law is feasible and `𝓛(ρ) = −∞` (the empty supremum), as the proof of Theorem 1
(p. 4) says. Expectations are `extIntegral` (`∫ f⁺ − ∫ f⁻`, with `∞ − ∞ = −∞`). -/
noncomputable def robustLoss (c : X → X → ENNReal) (f : X → ℝ) (Phat : Measure X) (ρ : ℝ) :
    EReal :=
  ⨆ (P : Measure X)
    (_ : IsProbabilityMeasure P ∧ ((transportCost c Phat P : ENNReal) : EReal) ≤ (ρ : EReal)),
    extIntegral P (fun x => (f x : EReal))

/-- The product `λ · t` of a real `λ` and a cost `t ∈ [0, ∞]` with the paper's convention
`0 · ∞ = ∞` (p. 2): it is `+∞` whenever `t = ∞`, and the ordinary product otherwise. (Mathlib's
`EReal` product has `0 * ⊤ = 0`, which is why this is a separate function.) -/
noncomputable def lamMul (lam : ℝ) (t : ENNReal) : EReal :=
  if t = ⊤ then ⊤ else (lam : EReal) * (t : EReal)

/-- `φ_λ(x̂, x) = f(x) − λ c(x̂, x)` (Theorem 1, p. 3), with `λc` computed by `lamMul`. -/
noncomputable def phiLam (c : X → X → ENNReal) (f : X → ℝ) (lam : ℝ) : X × X → EReal :=
  fun p => (f p.2 : EReal) - lamMul lam (c p.1 p.2)

/-- `x̂ ↦ sup_{x ∈ 𝒳} φ(x̂, x)`, the pointwise supremum over the second coordinate. -/
noncomputable def supFn (φ : X × X → EReal) : X → EReal :=
  fun xh => ⨆ x, φ (xh, x)

/-- The clause of the interchangeability principle (IP), p. 3: `x̂ ↦ sup_x φ(x̂, x)` is
`ℙ̂`-measurable (measurable for the completion of `ℱ` under `ℙ̂`) and
`𝔼_ℙ̂[sup_x φ(X̂, x)] = sup_{γ ∈ Γ_ℙ̂} 𝔼_γ[φ(X̂, X)]`. -/
def IPEq (Phat : Measure X) (φ : X × X → EReal) : Prop :=
  NullMeasurable (supFn φ) Phat ∧
    extIntegral Phat (supFn φ) = ⨆ γ ∈ couplingsFst Phat, extIntegral γ φ

set_option linter.dupNamespace false in
/-- The interchangeability principle (IP), p. 3, for an `(ℱ ⊗ ℱ)`-measurable function
`φ : 𝒳 × 𝒳 → ℝ ∪ {−∞}` (an `EReal`-valued function that never takes the value `+∞`). -/
def IP (Phat : Measure X) (φ : X × X → EReal) : Prop :=
  Measurable φ ∧ (∀ p, φ p ≠ ⊤) ∧ IPEq Phat φ

/-- The Legendre transform (p. 2): `h*(λ) = sup_{ρ ∈ ℝ} {λρ − h(ρ)}`. With `EReal` subtraction
`a − (−∞) = +∞`, so `h*` is identically `+∞` as soon as `h` takes the value `−∞`. -/
noncomputable def legendre (h : ℝ → EReal) (lam : ℝ) : EReal :=
  ⨆ ρ : ℝ, ((lam * ρ : ℝ) : EReal) - h ρ

/-- The value of the soft-penalty problem (P-soft), p. 2:
`sup_{ℙ ∈ 𝒫̄} {𝔼_ℙ[f] − λ 𝒦_c(ℙ̂, ℙ)}`, where `𝒫̄` is the set of probability measures `ℙ` with
`𝒦_c(ℙ̂, ℙ) < ∞`; on `𝒫̄` the cost is a real number, so `toReal` is exact. -/
noncomputable def softValue (c : X → X → ENNReal) (f : X → ℝ) (Phat : Measure X) (lam : ℝ) :
    EReal :=
  ⨆ (P : Measure X) (_ : IsProbabilityMeasure P ∧ transportCost c Phat P < ⊤),
    extIntegral P (fun x => (f x : EReal)) - ((lam * (transportCost c Phat P).toReal : ℝ) : EReal)

/-- `𝒢(λ) = 𝔼_{X̂ ∼ ℙ̂}[sup_{x ∈ 𝒳} {f(x) − λ c(X̂, x)}]` (proof of Theorem 1, p. 5, and
Lemma 2, p. 13), for `λ ≥ 0`. -/
noncomputable def dualG (c : X → X → ENNReal) (f : X → ℝ) (Phat : Measure X) (lam : ℝ) :
    EReal :=
  extIntegral Phat (supFn (phiLam c f lam))

end ShortWDRODual.Legendre


