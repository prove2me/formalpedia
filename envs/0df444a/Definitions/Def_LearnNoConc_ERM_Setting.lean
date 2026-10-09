-- Prove2me | Definitions.Def_LearnNoConc_ERM_Setting
-- name    : LearnNoConc_ERM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:22.674724+00:00
-- url     : https://prove2.me/theorems/3912a6a6-5268-41db-911f-312994552c83
-- title:
--   §1 p. 2, §2 pp. 9–11, §3 p. 13, §5 p. 20 — ERM, β*_N (Def. 2.1), φ_N and α*_N ((2.2)), Q_H (Assumption 3.1), star-shaped classes and β_N(H, γ) (Defs. 5.1–5.2)
-- statement:
--   This file fixes the objects of Mendelson's *Learning without Concentration* used in the proof of its main result (Theorem 3.1).
--
--   Let $(\Omega,\mu)$ be a probability space and let $X_1,\dots,X_N$ be i.i.d. with law $\mu$. In the learning setting the sample is $z=((X_i,Y_i))_{i=1}^N$, drawn i.i.d. from a joint law $\nu$ on $\Omega\times\mathbb R$ whose first marginal is $\mu$. Let $(\varepsilon_i)_{i=1}^N$ be independent symmetric random signs, independent of the sample. For a class $F$ of real functions on $\Omega$, $f^*\in F$ and $r>0$, write $F\cap rD_{f^*}=\{f\in F:\|f-f^*\|_{L_2(\mu)}\le r\}$.
--
--   1. **Empirical risk minimization** (§1, p. 2). The empirical loss is $P_N\ell_f=\frac1N\sum_{i=1}^N (f(X_i)-Y_i)^2$, and $\hat f$ is an *empirical minimizer* in $F$ if $\hat f\in F$ and $P_N\ell_{\hat f}\le P_N\ell_g$ for all $g\in F$.
--   2. **Localized Rademacher average.** For a class $G$, $\mathbb E\sup_{g\in G}\bigl|\frac1N\sum_{i=1}^N\varepsilon_i g(X_i)\bigr|$.
--   3. **Definition 5.2.** $$\beta_N(H,\gamma)=\inf\Bigl\{r>0:\ \mathbb E\sup_{h\in H\cap rD}\Bigl|\frac1N\sum_{i=1}^N\varepsilon_i h(X_i)\Bigr|\le\gamma r\Bigr\},$$ where $D$ is the unit ball of $L_2(\mu)$ centred at $0$.
--   4. **Definition 2.1.** $$\beta^*_N(\gamma)=\inf\Bigl\{r>0:\ \mathbb E\sup_{f\in F\cap rD_{f^*}}\Bigl|\frac1{\sqrt N}\sum_{i=1}^N\varepsilon_i (f-f^*)(X_i)\Bigr|\le\gamma\sqrt N\,r\Bigr\}.$$
--   5. **Display (2.2) and $\alpha^*_N$.** With the noise $\xi_i=f^*(X_i)-Y_i$, $$\phi_N(s)=\sup_{f\in F\cap sD_{f^*}}\Bigl|\frac1{\sqrt N}\sum_{i=1}^N\varepsilon_i\xi_i(f-f^*)(X_i)\Bigr|,\qquad \alpha^*_N(\gamma,\delta)=\inf\bigl\{s>0:\ \Pr\bigl(\phi_N(s)\le\gamma s^2\sqrt N\bigr)\ge1-\delta\bigr\}.$$
--   6. **Assumption 3.1.** The small-ball function $Q_H(u)=\inf_{h\in H}\Pr\bigl(|h|\ge u\|h\|_{L_2}\bigr)$, and the difference class $F-F=\{f-h:f,h\in F\}$; also $F-f^*=\{f-f^*:f\in F\}$.
--   7. **Definition 5.1.** $H$ is *star-shaped around $0$* if $\lambda h\in H$ for every $h\in H$ and $0<\lambda\le1$.
--   8. **Auxiliary notions.** $F$ is *closed in $L_2(\mu)$* if the set of $L_2(\mu)$-classes of its elements is closed; $F$ is *pointwise separable* if some countable $G_0\subseteq F$ approximates every $f\in F$ both pointwise and in $L_2(\mu)$; and $P_N\xi(f-f^*)-\mathbb E\xi(f-f^*)=\frac1N\sum_i\xi_i(f-f^*)(X_i)-\mathbb E\,\xi(f-f^*)(X)$.
--
--   These parameters measure two regimes: $\beta^*_N$ depends on the class only and controls the "version space", while $\alpha^*_N$ measures how the class correlates with the actual noise.
--
--   **Formalization Note** The expectation over the signs is the average over all $2^N$ sign vectors. All suprema, expectations of suprema, and the infima $\beta_N,\beta^*_N,\alpha^*_N$ take values in $[0,\infty]$: a supremum is never truncated, and an infimum over an empty set is $+\infty$. The inequalities "$\le\gamma r$", "$\le\gamma\sqrt N r$" and "$\le\gamma s^2\sqrt N$" are compared in the extended reals, so a negative right-hand side is never replaced by $0$. "$\Pr(A)\ge1-\delta$" in $\alpha^*_N$ is encoded as "the outer probability of the complement of $A$ is at most $\delta$", which is the same for a measurable event and never easier otherwise. The $L_2$ norm is Mathlib's `eLpNorm f 2 μ`, valued in $[0,\infty]$; $Q_H$ uses its real value. Pointwise separability (van der Vaart–Wellner, §2.3.3) is not in the paper; it is the standard condition that makes suprema over the class measurable, which the paper takes for granted.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, §1 p. 2 (ERM), Definition 2.1 p. 9, (2.2) and α*_N p. 11, Assumption 3.1 p. 13, Definitions 5.1–5.2 p. 20

import Mathlib

namespace LearnNoConc.ERM

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random sign `ε_i ∈ {−1, 1}`, encoded by a sign vector `σ : Fin N → Bool`
(`true ↦ 1`, `false ↦ −1`). Averaging over all `2 ^ N` sign vectors with weight `2⁻ᴺ`
is the expectation over independent symmetric random signs. -/
def sgn {N : ℕ} (σ : Fin N → Bool) (i : Fin N) : ℝ := if σ i then 1 else -1

/-- The empirical squared loss `P_N ℓ_f = (1/N) ∑ (f(X_i) − Y_i)²` of `f` on the sample
`z = ((X_i, Y_i))_{i=1}^N` (§1, p. 2). -/
noncomputable def empLoss {N : ℕ} (z : Fin N → Ω × ℝ) (f : Ω → ℝ) : ℝ :=
  (∑ i, (f (z i).1 - (z i).2) ^ 2) / N

/-- `f` is an empirical minimizer in `F` on the sample `z` (ERM, §1, p. 2). -/
def IsEmpMin {N : ℕ} (F : Set (Ω → ℝ)) (z : Fin N → Ω × ℝ) (f : Ω → ℝ) : Prop :=
  f ∈ F ∧ ∀ g ∈ F, empLoss z f ≤ empLoss z g

/-- `F ∩ r D_{f*}`: the elements of `F` in the closed `L₂(μ)` ball of radius `r` around `f*`. -/
def locBall (μ : Measure Ω) (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (r : ℝ) : Set (Ω → ℝ) :=
  {f ∈ F | eLpNorm (f - fstar) 2 μ ≤ ENNReal.ofReal r}

/-- `E sup_{g ∈ G} |(1/N) ∑ ε_i g(X_i)|`, with `X_1, …, X_N` i.i.d. `μ` and independent random
signs; the supremum and the expectation are taken in `[0, ∞]`. -/
noncomputable def radSup (μ : Measure Ω) (G : Set (Ω → ℝ)) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, (2 ^ N)⁻¹ * ∑ σ : Fin N → Bool,
      ⨆ g ∈ G, ‖(N : ℝ)⁻¹ * ∑ i, sgn σ i * g (x i)‖ₑ ∂(Measure.pi fun _ : Fin N => μ)

/-- Definition 5.2: `β_N(H, γ) = inf { r > 0 : E sup_{h ∈ H ∩ rD} |(1/N) ∑ ε_i h(X_i)| ≤ γ r }`,
`D` the unit ball of `L₂(μ)` centred at `0`. Valued in `[0, ∞]` (empty set ↦ `∞`). -/
noncomputable def betaN (μ : Measure Ω) (H : Set (Ω → ℝ)) (N : ℕ) (γ : ℝ) : ℝ≥0∞ :=
  sInf {R : ℝ≥0∞ | ∃ r : ℝ, 0 < r ∧ R = ENNReal.ofReal r ∧
    ((radSup μ {h ∈ H | eLpNorm h 2 μ ≤ ENNReal.ofReal r} N : ℝ≥0∞) : EReal) ≤ ((γ * r : ℝ) : EReal)}

/-- Definition 2.1: `β*_N(γ) = inf { r > 0 : E sup_{f ∈ F ∩ rD_{f*}} |(1/√N) ∑ ε_i (f − f*)(X_i)| ≤ γ √N r }`.
Valued in `[0, ∞]` (empty set ↦ `∞`). -/
noncomputable def betaStar (μ : Measure Ω) (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (N : ℕ) (γ : ℝ) :
    ℝ≥0∞ :=
  sInf {R : ℝ≥0∞ | ∃ r : ℝ, 0 < r ∧ R = ENNReal.ofReal r ∧
    ((∫⁻ x, (2 ^ N)⁻¹ * ∑ σ : Fin N → Bool,
        ⨆ f ∈ locBall μ F fstar r,
          ‖(Real.sqrt N)⁻¹ * ∑ i, sgn σ i * (f (x i) - fstar (x i))‖ₑ
        ∂(Measure.pi fun _ : Fin N => μ) : ℝ≥0∞) : EReal) ≤ ((γ * Real.sqrt N * r : ℝ) : EReal)}

/-- Display (2.2): the multiplier process
`φ_N(s) = sup_{f ∈ F ∩ sD_{f*}} |(1/√N) ∑ ε_i ξ_i (f − f*)(X_i)|`, `ξ_i = f*(X_i) − Y_i`,
evaluated at the sample `z = ((X_i, Y_i))_i` and the sign vector `σ`; `μ` is the law
`ν.map Prod.fst` of `X`. -/
noncomputable def phiN (ν : Measure (Ω × ℝ)) (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (N : ℕ) (s : ℝ)
    (z : Fin N → Ω × ℝ) (σ : Fin N → Bool) : ℝ≥0∞ :=
  ⨆ f ∈ locBall (ν.map Prod.fst) F fstar s,
    ‖(Real.sqrt N)⁻¹ * ∑ i, sgn σ i * (fstar (z i).1 - (z i).2) * (f (z i).1 - fstar (z i).1)‖ₑ

/-- `α*_N(γ, δ) = inf { s > 0 : Pr(φ_N(s) ≤ γ s² √N) ≥ 1 − δ }` (p. 11), with the probability over
the i.i.d. sample from `ν` and independent random signs. "`Pr(A) ≥ 1 − δ`" is encoded as
"the (outer) probability of the complement of `A` is at most `δ`". Valued in `[0, ∞]`. -/
noncomputable def alphaStar (ν : Measure (Ω × ℝ)) (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) (N : ℕ)
    (γ δ : ℝ) : ℝ≥0∞ :=
  sInf {R : ℝ≥0∞ | ∃ s : ℝ, 0 < s ∧ R = ENNReal.ofReal s ∧
    (2 ^ N)⁻¹ * ∑ σ : Fin N → Bool, (Measure.pi fun _ : Fin N => ν)
      {z | ¬ (((phiN ν F fstar N s z σ : ℝ≥0∞) : EReal) ≤ ((γ * s ^ 2 * Real.sqrt N : ℝ) : EReal))}
      ≤ ENNReal.ofReal δ}

/-- Assumption 3.1: the small-ball function `Q_H(u) = inf_{h ∈ H} Pr(|h| ≥ u ‖h‖_{L₂})`. -/
noncomputable def Q (μ : Measure Ω) (H : Set (Ω → ℝ)) (u : ℝ) : ℝ :=
  ⨅ h : H, μ.real {x | u * (eLpNorm h.1 2 μ).toReal ≤ |h.1 x|}

/-- `F − F = {f − h : f, h ∈ F}`. -/
def diffSet (F : Set (Ω → ℝ)) : Set (Ω → ℝ) := {g | ∃ f ∈ F, ∃ h ∈ F, g = f - h}

/-- `F − f* = {f − f* : f ∈ F}`. -/
def shift (F : Set (Ω → ℝ)) (fstar : Ω → ℝ) : Set (Ω → ℝ) := {g | ∃ f ∈ F, g = f - fstar}

/-- Definition 5.1: `H` is star-shaped around `0` if `λ h ∈ H` for every `h ∈ H` and `0 < λ ≤ 1`. -/
def StarShaped (H : Set (Ω → ℝ)) : Prop :=
  ∀ h ∈ H, ∀ c : ℝ, 0 < c → c ≤ 1 → c • h ∈ H

/-- `F` is closed in `L₂(μ)`: the set of `L₂(μ)` classes of elements of `F` is closed. -/
def IsL2Closed (μ : Measure Ω) (F : Set (Ω → ℝ)) : Prop :=
  IsClosed {g : Lp ℝ 2 μ | ∃ f ∈ F, (g : Ω → ℝ) =ᵐ[μ] f}

/-- Pointwise separability (van der Vaart–Wellner §2.3.3): a countable subclass `G₀ ⊆ G`
such that every `g ∈ G` is a pointwise and `L₂(μ)` limit of a sequence in `G₀`. It makes the
suprema over `G` measurable; the paper takes this measurability for granted. -/
def PointwiseSeparable (μ : Measure Ω) (G : Set (Ω → ℝ)) : Prop :=
  ∃ G₀ ⊆ G, G₀.Countable ∧ ∀ g ∈ G, ∃ u : ℕ → Ω → ℝ, (∀ n, u n ∈ G₀) ∧
    (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) ∧
    Tendsto (fun n => eLpNorm (u n - g) 2 μ) atTop (𝓝 0)

/-- `P_N ξ (f − f*) − E ξ (f − f*)` on the sample `z`, with `ξ = f*(X) − Y`. -/
noncomputable def multDev (ν : Measure (Ω × ℝ)) (fstar : Ω → ℝ) {N : ℕ} (z : Fin N → Ω × ℝ)
    (f : Ω → ℝ) : ℝ :=
  (∑ i, (fstar (z i).1 - (z i).2) * (f (z i).1 - fstar (z i).1)) / N
    - ∫ w, (fstar w.1 - w.2) * (f w.1 - fstar w.1) ∂ν

end LearnNoConc.ERM


