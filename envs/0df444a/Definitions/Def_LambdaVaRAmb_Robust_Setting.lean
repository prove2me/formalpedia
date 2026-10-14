-- Prove2me | Definitions.Def_LambdaVaRAmb_Robust_Setting
-- name    : LambdaVaRAmb_Robust_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:57.239075+00:00
-- url     : https://prove2.me/theorems/6a3f176b-395c-4cc3-8027-5dc340a70253
-- title:
--   pp. 6–12 — capacities, ΛVaR and ΛVaR⁺ (1), ℋ_I, envelopes w̄, w̲ (2), φ-divergence ball 𝒫_φ(ℙ,δ), g_{φ,δ}, g⁻¹_{φ,δ} and g_{φ,δ}∘ℙ
-- statement:
--   This file fixes the objects of Liu and Schied's *Lambda Value-at-Risk under ambiguity and risk sharing* that are needed for robust $\Lambda$VaR over a $\phi$-divergence ball.
--
--   Let $(\Omega,\mathcal F)$ be a measurable space.
--
--   1. **Capacities** (p. 6). A set function $w:\mathcal F\to[0,1]$ is a *capacity* if it is increasing ($A\subseteq B$ implies $w(A)\le w(B)$), $w(\emptyset)=0$ and $w(\Omega)=1$. A probability measure $\mathbb P$ is a capacity, $A\mapsto\mathbb P(A)$.
--   2. **Lambda functions** (p. 6). $\mathcal H$ is the set of functions $\Lambda:\mathbb R\to(0,1)$, and $\mathcal H_I$ the (non-strictly) increasing ones.
--   3. **Lambda Value-at-Risk** ((1), p. 6). For a capacity $w$ and a random variable $X$,
--   $$\Lambda\mathrm{VaR}^w(X)=\inf\{x\in\mathbb R: w(X>x)\le\Lambda(x)\},\qquad \Lambda\mathrm{VaR}^{+,w}(X)=\sup\{x\in\mathbb R: w(X>x)\ge\Lambda(x)\},$$
--   with $\inf\emptyset=\infty$ and $\sup\emptyset=-\infty$, so both take values in $[-\infty,\infty]$. For a constant $\Lambda\equiv p$, $\mathrm{VaR}^w_p=\Lambda\mathrm{VaR}^w$ is the Choquet quantile.
--   4. **Envelopes** ((2), p. 8). For a class $W$ of capacities, $\overline w=\sup_{w\in W}w$ and $\underline w=\inf_{w\in W}w$, setwise; for a class $\mathcal P$ of probability measures, $\overline{\mathbb Q}=\sup_{\mathbb Q\in\mathcal P}\mathbb Q$ and $\underline{\mathbb Q}=\inf_{\mathbb Q\in\mathcal P}\mathbb Q$.
--   5. **$\phi$-divergence ball** (p. 11). A function $\phi:[0,\infty)\to\mathbb R\cup\{\infty\}$ is admissible if it is convex, $\phi(1)=0$ and $\phi(0)=\lim_{x\downarrow0}\phi(x)$. For a probability measure $\mathbb Q\ll\mathbb P$, $D_\phi(\mathbb Q\|\mathbb P)=\mathbb E^{\mathbb P}[\phi(\mathrm d\mathbb Q/\mathrm d\mathbb P)]$, and
--   $$\mathcal P_\phi(\mathbb P,\delta)=\{\mathbb Q\ll\mathbb P: D_\phi(\mathbb Q\|\mathbb P)\le\delta\}.$$
--   6. **The distortion** (Proposition 5, p. 11). $g_{\phi,\delta}(0)=0$, $g_{\phi,\delta}(1)=1$ and, for $x\in(0,1)$,
--   $$g_{\phi,\delta}(x)=\sup\{t\in[x,1]: x\phi(t/x)+(1-x)\phi((1-t)/(1-x))\le\delta\}.$$
--   Its inverse $g^{-1}_{\phi,\delta}(t)=\sup\{x\in[0,1]: g_{\phi,\delta}(x)\le t\}$ and the distorted capacity $(g_{\phi,\delta}\circ\mathbb P)(A)=g_{\phi,\delta}(\mathbb P(A))$ appear in Theorem 2 (p. 12).
--
--   These objects are shared by the three missions of the series (robust ΛVaR, inf-convolution, comonotonic risk sharing).
--
--   **Formalization Note** Set functions are `Set Ω → ℝ`; the capacity axioms are imposed on measurable sets only, and only events $\{X>x\}$ with $X$ measurable are ever evaluated. $\Lambda$VaR and $\Lambda$VaR$^+$ are infima and suprema in `EReal`, so $\pm\infty$ are genuine values and never collapse to $0$. The envelopes are real `sSup`/`sInf` of values in $[0,1]$; they are the true supremum and infimum when the class is nonempty, which every statement using them assumes. $\phi$ is a function `ℝ → EReal` whose values at negative arguments are never read; convexity is stated with the `EReal` conventions $0\cdot\infty=0$ and $\theta\cdot\infty=\infty$ for $\theta>0$. $D_\phi$ is the integral of the positive part of $\phi(\mathrm d\mathbb Q/\mathrm d\mathbb P)$ minus that of the negative part; for admissible $\phi$ the negative part is integrable (an affine minorant and $\mathbb E^{\mathbb P}[\mathrm d\mathbb Q/\mathrm d\mathbb P]=1$), so the difference never meets $\infty-\infty$. Members of the ball are required to be probability measures. $g_{\phi,\delta}$ outside $[0,1]$ is a junk value that is never read. Under the hypotheses of Proposition 5's second part, $g_{\phi,\delta}$ is continuous and strictly increasing up to $x_\delta$ and equal to $1$ after it, so for $t\in(0,1)$ the formula for $g^{-1}_{\phi,\delta}(t)$ returns the unique $x\in(0,x_\delta)$ with $g_{\phi,\delta}(x)=t$, which is the paper's inverse; it is only applied to $\Lambda(x)\in(0,1)$ and $\alpha\in(0,1)$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, pp. 6, 8, 11–12: §2 (1), §3 (2) and Corollary 1, §4.1, Proposition 5, Theorem 2

import Mathlib

namespace LambdaVaRAmb.Robust

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- p. 6: a capacity on ℱ, as a set function constrained on measurable sets only. -/
structure IsCapacity (w : Set Ω → ℝ) : Prop where
  nonneg : ∀ A, MeasurableSet A → 0 ≤ w A
  le_one : ∀ A, MeasurableSet A → w A ≤ 1
  mono : ∀ A B, MeasurableSet A → MeasurableSet B → A ⊆ B → w A ≤ w B
  empty : w ∅ = 0
  univ : w Set.univ = 1

/-- A probability measure as a capacity, `A ↦ ℙ(A)`. -/
noncomputable def probCap (P : Measure Ω) : Set Ω → ℝ := fun A => P.real A

/-- p. 6: `ℋ`, the functions `Λ : ℝ → (0, 1)`. -/
def InH (Λ : ℝ → ℝ) : Prop := ∀ x, 0 < Λ x ∧ Λ x < 1

/-- p. 6: `ℋ_I`, the increasing (non-strict) functions in `ℋ`. -/
def InHI (Λ : ℝ → ℝ) : Prop := InH Λ ∧ Monotone Λ

/-- (1), p. 6: `ΛVaR^w(X) = inf {x ∈ ℝ | w(X > x) ≤ Λ(x)}` in `[-∞, ∞]`, with `inf ∅ = ∞`. -/
noncomputable def LVaR (Λ : ℝ → ℝ) (w : Set Ω → ℝ) (X : Ω → ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | w {ω | x < X ω} ≤ Λ x})

/-- (1), p. 6: `ΛVaR^{+,w}(X) = sup {x ∈ ℝ | w(X > x) ≥ Λ(x)}`, with `sup ∅ = -∞`. -/
noncomputable def LVaRPlus (Λ : ℝ → ℝ) (w : Set Ω → ℝ) (X : Ω → ℝ) : EReal :=
  sSup ((fun x : ℝ => (x : EReal)) '' {x : ℝ | Λ x ≤ w {ω | x < X ω}})

/-- p. 6: the Choquet quantile `VaR^w_p = ΛVaR^w` with `Λ ≡ p`. -/
noncomputable def VaRw (p : ℝ) (w : Set Ω → ℝ) (X : Ω → ℝ) : EReal := LVaR (fun _ => p) w X

/-- (2), p. 8: the upper envelope `w̄ = sup_{w ∈ W} w` of a class of capacities.
Real `sSup` of a set of values in `[0, 1]`; the statements that use it assume `W` nonempty. -/
noncomputable def upperCap (W : Set (Set Ω → ℝ)) : Set Ω → ℝ := fun A => sSup ((fun w => w A) '' W)

/-- (2), p. 8: the lower envelope `w̲ = inf_{w ∈ W} w` of a class of capacities.
Real `sInf` of a set of values in `[0, 1]`; the statements that use it assume `W` nonempty. -/
noncomputable def lowerCap (W : Set (Set Ω → ℝ)) : Set Ω → ℝ := fun A => sInf ((fun w => w A) '' W)

/-- Corollary 1, p. 8: `ℚ̄ = sup_{ℚ ∈ 𝒫} ℚ` for a class `𝒫` of probability measures. -/
noncomputable def upperProb (Pcl : Set (Measure Ω)) : Set Ω → ℝ := upperCap (probCap '' Pcl)

/-- Corollary 1, p. 8: `ℚ̲ = inf_{ℚ ∈ 𝒫} ℚ` for a class `𝒫` of probability measures. -/
noncomputable def lowerProb (Pcl : Set (Measure Ω)) : Set Ω → ℝ := lowerCap (probCap '' Pcl)

/-- p. 11: "a convex ϕ : [0, ∞) → ℝ ∪ {∞} satisfying ϕ(1) = 0 and ϕ(0) = lim_{x↓0} ϕ(x)".
`φ : ℝ → EReal`; values at negative arguments are never used. -/
structure IsPhiFunction (φ : ℝ → EReal) : Prop where
  ne_bot : ∀ x, 0 ≤ x → φ x ≠ ⊥
  convex : ∀ s t θ : ℝ, 0 ≤ s → 0 ≤ t → 0 ≤ θ → θ ≤ 1 →
    φ (θ * s + (1 - θ) * t) ≤ (θ : EReal) * φ s + ((1 - θ : ℝ) : EReal) * φ t
  map_one : φ 1 = 0
  map_zero : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0))

/-- p. 11: `D_ϕ(ℚ‖ℙ) = 𝔼^ℙ[ϕ(dℚ/dℙ)]`, as positive part minus negative part in `EReal`. -/
noncomputable def phiDiv (φ : ℝ → EReal) (Q P : Measure Ω) : EReal :=
  ((∫⁻ ω, (φ (Q.rnDeriv P ω).toReal).toENNReal ∂P : ℝ≥0∞) : EReal) -
    ((∫⁻ ω, (-(φ (Q.rnDeriv P ω).toReal)).toENNReal ∂P : ℝ≥0∞) : EReal)

/-- p. 11: `𝒫_ϕ(ℙ, δ) = {ℚ ≪ ℙ : D_ϕ(ℚ‖ℙ) ≤ δ}` (probability measures `ℚ`). -/
def phiBall (φ : ℝ → EReal) (P : Measure Ω) (δ : ℝ) : Set (Measure Ω) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ P ∧ phiDiv φ Q P ≤ (δ : EReal)}

/-- Proposition 5, p. 11: `g_{ϕ,δ}(x) = sup {t ∈ [x, 1] | xϕ(t/x) + (1 − x)ϕ((1 − t)/(1 − x)) ≤ δ}`
for `x ∈ (0, 1)`, `g_{ϕ,δ}(0) = 0`, `g_{ϕ,δ}(1) = 1`. -/
noncomputable def gPhi (φ : ℝ → EReal) (δ : ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else if x = 1 then 1 else
    sSup {t : ℝ | t ∈ Set.Icc x 1 ∧
      (x : EReal) * φ (t / x) + ((1 - x : ℝ) : EReal) * φ ((1 - t) / (1 - x)) ≤ (δ : EReal)}

/-- Theorem 2, p. 12: `g⁻¹_{ϕ,δ}`, the inverse of `g_{ϕ,δ}` on `(0, 1)`, as
`t ↦ sup {x ∈ [0, 1] | g_{ϕ,δ}(x) ≤ t}`. -/
noncomputable def gPhiInv (φ : ℝ → EReal) (δ : ℝ) (t : ℝ) : ℝ :=
  sSup {x : ℝ | x ∈ Set.Icc 0 1 ∧ gPhi φ δ x ≤ t}

/-- Theorem 2, p. 12: the distorted capacity `g_{ϕ,δ} ∘ ℙ`. -/
noncomputable def distortedCap (φ : ℝ → EReal) (δ : ℝ) (P : Measure Ω) : Set Ω → ℝ :=
  fun A => gPhi φ δ (P.real A)

end LambdaVaRAmb.Robust


