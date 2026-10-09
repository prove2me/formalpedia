-- Prove2me | Definitions.Def_ShortWDRODual_MaxCost_Setting
-- name    : ShortWDRODual_MaxCost_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:24.624764+00:00
-- url     : https://prove2.me/theorems/dd93a47f-d6d4-4c1b-9879-197abc071aad
-- title:
--   §2.1, §3, §5.1, pp. 1–3, 6–7, 9 — couplings, (IP), (Proj), (Sel), maximum transport cost 𝒦̄_c, robust loss 𝓛̄, local supremum, ψ_ρ
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space, and let $\mathcal F_{\widehat{\mathbb P}}$ be the completion of $\mathcal F$ under $\widehat{\mathbb P}$; a set or function is called $\widehat{\mathbb P}$-measurable when it is measurable for $\mathcal F_{\widehat{\mathbb P}}$. Expectations take values in $\bar{\mathbb R}=[-\infty,\infty]$ and are computed as $\mathbb E[\varphi]=\int\varphi^+-\int\varphi^-$. Throughout, $c:\mathcal X\times\mathcal X\to[0,\infty)$ is a transport cost, written $c(\widehat x,x)$ with the nominal point first, and $f:\mathcal X\to\mathbb R$ is a loss.
--
--   1. **Couplings.** $\Gamma(\widehat{\mathbb P},\mathbb P)$ is the set of probability measures on $(\mathcal X\times\mathcal X,\mathcal F\otimes\mathcal F)$ with marginals $\widehat{\mathbb P}$ and $\mathbb P$; $\Gamma_{\widehat{\mathbb P}}$ is the set of those whose first marginal is $\widehat{\mathbb P}$ (the second is free).
--   2. **Interchangeability principle (IP).** For $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ put $\Phi(\widehat x)=\sup_{x\in\mathcal X}\phi(\widehat x,x)$. An $(\mathcal F\otimes\mathcal F)$-measurable $\phi$ satisfies (IP) if $\Phi$ is $\widehat{\mathbb P}$-measurable and
--   $$\mathbb E_{\widehat X\sim\widehat{\mathbb P}}\Big[\sup_{x\in\mathcal X}\phi(\widehat X,x)\Big]=\sup_{\gamma\in\Gamma_{\widehat{\mathbb P}}}\mathbb E_{(\widehat X,X)\sim\gamma}\big[\phi(\widehat X,X)\big].$$
--   3. **Legendre transform.** For $h:\mathbb R\to\bar{\mathbb R}$, $h^*(\lambda)=\sup_{\rho\in\mathbb R}\{\lambda\rho-h(\rho)\}$; if $h$ takes the value $-\infty$ somewhere then $h^*\equiv+\infty$.
--   4. **The product $\lambda t$** for $\lambda\in\mathbb R$ and $t\in[0,\infty]$, with the convention $0\cdot\infty=\infty$: $+\infty$ if $t=\infty$, the ordinary product otherwise.
--   5. **Diagonally dominant sets and (Proj).** A set $A\in\mathcal F\otimes\mathcal F$ is diagonally dominant if $(\widehat x,x)\in A$ implies $(x,x)\in A$. (Proj) holds if $\mathrm{Proj}_{\widehat x}(A)=\{\widehat x:(\widehat x,x)\in A\text{ for some }x\}\in\mathcal F_{\widehat{\mathbb P}}$ for every diagonally dominant $A\in\mathcal F\otimes\mathcal F$.
--   6. **(Sel), measurable selection.** For every set-valued $E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$ with measurable graph $\mathrm{Graph}(E)=\{(\widehat x,x):x\in E(\widehat x)\}\in\mathcal F\otimes\mathcal F$ there is an $(\mathcal F_{\widehat{\mathbb P}},\mathcal F)$-measurable $T:\mathcal X\to\mathcal X$ with $T(\widehat x)\in E(\widehat x)$ for all $\widehat x$.
--   7. **Maximum transport cost and its robust loss (§5.1).**
--   $$\overline{\mathcal K}_c(\widehat{\mathbb P},\mathbb P)=\inf_{\gamma\in\Gamma(\widehat{\mathbb P},\mathbb P)}\ \gamma\text{-}\operatorname*{ess\,sup}_{\widehat x,x\in\mathcal X}c(\widehat x,x)\in[0,\infty],\qquad \overline{\mathcal L}(\rho)=\sup_{\mathbb P\in\mathcal P(\mathcal X)}\big\{\mathbb E_{X\sim\mathbb P}[f(X)]:\overline{\mathcal K}_c(\widehat{\mathbb P},\mathbb P)\le\rho\big\}.$$
--   For $\rho<0$ the constraint set is empty and $\overline{\mathcal L}(\rho)=-\infty$.
--   8. **Local supremum.** $\widehat x\mapsto\sup_x\{f(x):c(\widehat x,x)\le\rho\}\in\bar{\mathbb R}$.
--   9. **The barrier integrand** $\psi_\rho(\widehat x,x)=f(x)-\infty\mathbf 1\{c(\widehat x,x)>\rho\}$: equal to $-\infty$ where $c(\widehat x,x)>\rho$ and to $f(x)$ elsewhere.
--
--   These are the objects of Theorem 2, the duality theorem for the maximum transport cost (which for a metric $c=d$ is the $\infty$-Wasserstein distance).
--
--   **Formalization Note** Expectations use the published `ModelRiskOT.Duality.extIntegral` ($\int\varphi^+-\int\varphi^-$ with lower Lebesgue integrals, in `EReal`); it agrees with the paper whenever one part is finite and assigns $-\infty$ to the undefined case $\infty-\infty$. The essential supremum is Mathlib's `essSup` of $\mathrm{ofReal}\circ c$ in $[0,\infty]$. The ball constraint of $\overline{\mathcal L}$ is compared in `EReal`, so that $\overline{\mathcal L}(\rho)=-\infty$ for $\rho<0$. The paper's $\mathcal P(\mathcal X)$ (p. 2) consists of the probability measures with finite Kantorovich cost $\mathcal K_c(\widehat{\mathbb P},\mathbb P)<\infty$; the Lean supremum ranges over all probability measures, which changes nothing because $\overline{\mathcal K}_c(\widehat{\mathbb P},\mathbb P)\le\rho<\infty$ already forces $\mathcal K_c(\widehat{\mathbb P},\mathbb P)\le\rho$. $\widehat{\mathbb P}$-measurability is `NullMeasurable` / `NullMeasurableSet`. In $\psi_\rho$ the term $\infty\mathbf 1\{\cdot\}$ is read with $\infty\cdot0=0$ (otherwise $\psi_\rho\equiv-\infty$); this is the reading the next line of the paper's proof fixes. The product $\lambda t$ is a separate function `lamMul` because Mathlib's `EReal` product has $0\cdot\infty=0$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, §1 (P) p. 1; §2.1 notations, Assumption 1 and (IP), pp. 2–3 (PDF pp. 2–3); §3 Definition 1, (Proj), (Sel), pp. 6–7 (PDF pp. 6–7); §5.1 𝒦̄_c, 𝓛̄, p. 9 (PDF p. 9); proof of Theorem 2, ψ_ρ, p. ec8 (PDF p. 22)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- `Γ(ℙ̂, ℙ)` (p. 1): the probability measures on `(𝒳 × 𝒳, ℱ ⊗ ℱ)` with first marginal `ℙ̂` and
second marginal `ℙ`. -/
def couplings {X : Type*} [MeasurableSpace X] (Phat P : Measure X) :
    Set (Measure (X × X)) :=
  {γ | IsProbabilityMeasure γ ∧ γ.map Prod.fst = Phat ∧ γ.map Prod.snd = P}

/-- (Sel) Measurable Selection (p. 7): for every set-valued `E : 𝒳 → ℱ ∖ {∅}` (measurable,
nonempty values) with an `(ℱ ⊗ ℱ)`-measurable graph there is an `(ℱ_ℙ̂, ℱ)`-measurable map
`T : 𝒳 → 𝒳` (`NullMeasurable T ℙ̂`: measurable from the completion of `ℱ` under `ℙ̂`) with
`T(x̂) ∈ E(x̂)` for every `x̂`. -/
def Sel {X : Type*} [MeasurableSpace X] (Phat : Measure X) : Prop :=
  ∀ E : X → Set X,
    (∀ xh, MeasurableSet (E xh) ∧ (E xh).Nonempty) →
    MeasurableSet (ShortWDRODual.IP.graph E) →
    ∃ T : X → X, NullMeasurable T Phat ∧ ∀ xh, T xh ∈ E xh

/-- The maximum transport cost of §5.1 (p. 9):
`𝒦̄_c(ℙ̂, ℙ) = inf_{γ ∈ Γ(ℙ̂, ℙ)} γ-ess sup_{x̂, x} c(x̂, x)`, in `[0, ∞]`, for a real cost
`c(x̂, x)` (nominal point first). -/
noncomputable def maxCost {X : Type*} [MeasurableSpace X]
    (c : X → X → ℝ) (Phat P : Measure X) : ℝ≥0∞ :=
  ⨅ γ ∈ couplings Phat P,
    essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ

/-- The maximum transport cost robust loss of §5.1 (p. 9):
`𝓛̄(ρ) = sup_{ℙ ∈ 𝒫(𝒳)} {𝔼_ℙ[f(X)] : 𝒦̄_c(ℙ̂, ℙ) ≤ ρ}`. The ball constraint is compared in
`EReal`, so for `ρ < 0` the ball is empty and `𝓛̄(ρ) = −∞`. -/
noncomputable def robustLossMax {X : Type*} [MeasurableSpace X]
    (c : X → X → ℝ) (f : X → ℝ) (Phat : Measure X) (ρ : ℝ) : EReal :=
  ⨆ (P : Measure X)
    (_ : IsProbabilityMeasure P ∧ ((maxCost c Phat P : ℝ≥0∞) : EReal) ≤ (ρ : EReal)),
    extIntegral P (fun x => (f x : EReal))

/-- `x̂ ↦ sup_x {f(x) : c(x̂, x) ≤ ρ}`, the supremum of `f` over the closed `c`-ball around `x̂`,
in `EReal` (`+∞` when `f` is unbounded above on the ball, `−∞` when the ball is empty). -/
noncomputable def localSup {X : Type*} (c : X → X → ℝ)
    (f : X → ℝ) (ρ : ℝ) : X → EReal :=
  fun xh => ⨆ (x : X) (_ : c xh x ≤ ρ), (f x : EReal)

/-- `ψ_ρ(x̂, x) = f(x) − ∞·1{c(x̂, x) > ρ}` (proof of Theorem 2, p. ec8): `−∞` where
`c(x̂, x) > ρ` and `f(x)` elsewhere (here `∞ · 0 = 0`). -/
noncomputable def psi {X : Type*} (c : X → X → ℝ)
    (f : X → ℝ) (ρ : ℝ) : X × X → EReal :=
  fun q => if ρ < c q.1 q.2 then ⊥ else (f q.2 : EReal)

end ShortWDRODual.MaxCost


