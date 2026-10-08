-- Prove2me | Definitions.Def_ZhangBSDE_Scheme_FBSDE
-- name    : ZhangBSDE_Scheme_FBSDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:52.866154+00:00
-- url     : https://prove2.me/theorems/99642deb-10f4-431f-b2cd-6e70ca6fa8d7
-- title:
--   (2.1), p. 461 — solutions of the forward–backward SDE, and "Z is càdlàg" (Theorem 3.1)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying a one-dimensional standard Brownian motion $W$, and let $\mathbb F=\{\mathcal F_t\}$ be the natural filtration of $W$ augmented by the $P$-null sets. Given $x\in\mathbb R^d$, coefficients $b,\sigma,f$ and a functional $\Phi$ as in Assumption 2.3, a triple $(X,Y,Z)$ solves the forward–backward SDE
--   $$X_t = x+\int_0^t b(s,X_s)\,ds+\int_0^t\sigma(s,X_s)\,dW_s,\qquad Y_t=\Phi(X)+\int_t^T f(s,X_s,Y_s,Z_s)\,ds-\int_t^T Z_s\,dW_s,\qquad 0\le t\le T, \tag{2.1}$$
--   when:
--
--   1. $X$ is progressively measurable with values in $\mathbb R^d$, almost every path is continuous on $[0,T]$, $\sup_{0\le t\le T}E|X_t|^2<\infty$, and for every $t\in[0,T]$, almost surely, the forward equation holds with the stochastic integral taken coordinatewise in the $L^2$ Itô sense;
--   2. $Y$ is progressively measurable with $E\sup_{0\le t\le T}|Y_t|^2<\infty$, $Z$ is progressively measurable with $E\int_0^T|Z_t|^2dt<\infty$, and for every $t\in[0,T]$, almost surely, the backward equation holds, $\Phi(X)$ being $\Phi$ applied to the path $s\mapsto X_s(\omega)$.
--
--   Under Assumption 2.3 the solution exists and is unique ($X$ and $Y$ up to modification, $Z$ up to $dt\otimes dP$-null sets), so statements about every solution are statements about the paper's solution.
--
--   "$Z$ is càdlàg" (the hypothesis of Theorem 3.1) means: almost every path of $Z$ is càdlàg on $[0,T]$ and $Z_T=Z_{T-}$.
--
--   **Formalization Note** The Itô integral is `Peng1990.SMP.IsItoIntegral` (an $L^2$ limit of elementary integrals) and the filtration is `ReflectedBSDE.Existence.augmentedFiltration`; both are reused published definitions. Completeness of $(\Omega,\mathcal F,P)$, assumed on p. 461, is not imposed: no statement of the mission uses it. The pin $Z_T=Z_{T-}$ is added because $Z$ is determined only $dt\otimes dP$-almost everywhere while Theorem 3.1 evaluates it at $t_n=T$; it is the value given by the representation of $Z$ in the paper's Lemma 2.5.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, §2, p. 461, (2.1) and the standing setting; Theorem 3.1, p. 465 ("Z is càdlàg")

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_Setting

namespace ZhangBSDE.Scheme

open MeasureTheory Filter Topology Set Peng1990.SMP ReflectedBSDE.Existence
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `X` solves the forward SDE of (2.1),
`X_t = x + ∫₀ᵗ b(s, X_s) ds + ∫₀ᵗ σ(s, X_s) dW_s`, `0 ≤ t ≤ T`, with `X_t ∈ ℝᵈ` and `W` a
one-dimensional Brownian motion: `X` is progressively measurable, almost every path is continuous
on `[0, T]`, `sup_{0≤t≤T} E|X_t|² < ∞`, and there are Itô integrals `J_k = ∫₀^· σ_k(s, X_s) dW_s`
of the coordinates of `σ(·, X)` (in the sense of `Peng1990.SMP.IsItoIntegral`) such that for every
`t ∈ [0, T]`, almost surely, the drift is integrable on `[0, t]` and, coordinatewise,
`X_t = x + ∫₀ᵗ b(s, X_s) ds + J_t`. -/
def IsForwardSolution {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  IsStronglyProgressive 𝓕 X ∧
    (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Iic T)) ∧
    (⨆ t ≤ T, ∫⁻ ω, ‖X t ω‖ₑ ^ 2 ∂P) < ⊤ ∧
    ∃ J : Fin d → ℝ≥0 → Ω → ℝ,
      (∀ k, IsItoIntegral 𝓕 P T W (fun s ω => σ s (X s ω) k) (J k)) ∧
      ∀ t ≤ T, ∀ᵐ ω ∂P,
        IntegrableOn (fun s : ℝ => b s.toNNReal (X s.toNNReal ω)) (Icc 0 (t : ℝ)) ∧
        ∀ k, X t ω k = x k + (∫ s in Icc (0 : ℝ) t, b s.toNNReal (X s.toNNReal ω)) k + J k t ω

/-- `(X, Y, Z)` is a solution of the forward–backward SDE (2.1) (p. 461):
`X` solves the forward equation (`IsForwardSolution`), `Y ∈ 𝒮²` (progressive with
`E sup_{0≤t≤T} |Y_t|² < ∞`), `Z ∈ L²(𝔽)`, and for an Itô integral `J = ∫₀^· Z dW` and every
`t ∈ [0, T]`, almost surely, the driver is integrable on `[t, T]` and
`Y_t = Φ(X) + ∫ₜᵀ f(s, X_s, Y_s, Z_s) ds − ∫ₜᵀ Z_s dW_s`, with `Φ(X)` the functional applied to the
path `s ↦ X_s(ω)`.
Under Assumption 2.3 this solution exists and is unique (`X`, `Y` up to modification, `Z` up to
`dt ⊗ dP`-null sets), so a statement about every such `(X, Y, Z)` is a statement about the paper's
solution. -/
def IsFBSDESolution {d : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ)
    (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ)
    (X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (Y Z : ℝ≥0 → Ω → ℝ) : Prop :=
  IsForwardSolution 𝓕 P T W x b σ X ∧ IsS2 𝓕 P T Y ∧ L2F 𝓕 P T Z ∧
    ∃ J : ℝ≥0 → Ω → ℝ, IsItoIntegral 𝓕 P T W Z J ∧
      ∀ t ≤ T, ∀ᵐ ω ∂P,
        IntegrableOn
          (fun s : ℝ => f s.toNNReal (X s.toNNReal ω) (Y s.toNNReal ω) (Z s.toNNReal ω))
          (Icc (t : ℝ) T) ∧
        Y t ω = Φ (fun s => X s ω)
          + (∫ s in Icc (t : ℝ) T, f s.toNNReal (X s.toNNReal ω) (Y s.toNNReal ω) (Z s.toNNReal ω))
          - (J T ω - J t ω)

/-- "`Z` is càdlàg" (Theorem 3.1): almost every path of `Z` is càdlàg on `[0, T]`, and its value
at `T` is its left limit, `Z_T = Z_{T−}`. -/
def ZCadlag (P : Measure Ω) (T : ℝ≥0) (Z : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, IsCadlagOn T (fun t => Z t ω) ∧ Tendsto (fun t => Z t ω) (𝓝[<] T) (𝓝 (Z T ω))

end ZhangBSDE.Scheme


