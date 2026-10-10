-- Prove2me | Definitions.Def_MasterVisc_Comparison_Setting
-- name    : MasterVisc_Comparison_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:46.206924+00:00
-- url     : https://prove2.me/theorems/161d322a-c5a6-4515-84d4-241ae0217caa
-- title:
--   §2.2, §2.4, §3, §4.1 — path space, 𝒫₂, the pseudometric 𝒲₂ (2.5), the generator and Assumption 3.1, 𝒫_L(t, μ)
-- statement:
--   This file fixes the setting of Wu–Zhang's parabolic master equations.
--
--   **Canonical space.** Let $T\ge 0$ and let $d$ be the dimension. The canonical space is $\Omega=C([0,T];\mathbb R^d)$ with the uniform norm $\|\omega\|=\sup_{0\le s\le T}|\omega_s|$ and its Borel $\sigma$-algebra. The canonical process is $X_s(\omega)=\omega_{s\wedge T}$, the stopped path is $X_{t\wedge\cdot}$, and $\mathcal F_t=\sigma(X_s: s\le t)$ is the natural filtration. $X_{t,s}:=X_s-X_t$ (2.4).
--
--   **Laws.** $\mathcal P_2$ is the set of probability measures $\mu$ on $\Omega$ with $\mathbb E^\mu[\|X\|^2]<\infty$; $\mu_{[0,t]}:=\mu\circ (X_{t\wedge\cdot})^{-1}$ is the law of the stopped process. $\mathcal W_2$ is the 2-Wasserstein distance on laws of paths (uniform norm), and on $\Theta=[0,T]\times\mathcal P_2$ the pseudometric (2.5) is
--   $$\mathcal W_2\big((t,\mu),(t',\mu')\big)=\Big(|t-t'|+\mathcal W_2^2\big(\mu_{[0,t]},\mu'_{[0,t']}\big)\Big)^{1/2}.$$
--   A function $V:\Theta\to\mathbb R$ is in $C^0(\Theta)$ if it is continuous at every point of $\Theta$ for this pseudometric; it is adapted if $V(t,\mu)=V(t,\mu_{[0,t]})$. The file also records continuity relative to a subset $S\subset\Theta$, joint continuity on $S\times\Omega$ for $\mathcal W_2$ plus the uniform distance on paths, and continuity of a terminal function $g:\mathcal P_2\to\mathbb R$ for $\mathcal W_2$ (the class $C^0(\mathcal P_2)$). For matrices, $|\sigma|^2=\sum_{ij}\sigma_{ij}^2$ (Frobenius) and $A:B=\sum_{ij}A_{ij}B_{ij}$.
--
--   **Semimartingale laws.** A representation of a law $\mathbb P$ on $\Omega$ from time $t$ consists of a filtered probability space $(\tilde\Omega,\tilde{\mathbb F},\tilde{\mathbb P})$, a $d$-dimensional $(\tilde{\mathbb F},\tilde{\mathbb P})$-Brownian motion $\tilde B$ (adapted, with increments after $s$ independent of $\tilde{\mathcal F}_s$), bounded progressively measurable $\tilde b,\tilde\sigma$, and an adapted continuous process $\tilde X$ with $\tilde{\mathbb P}\circ\tilde X^{-1}=\mathbb P$ and, almost surely, $\tilde X_s=\tilde X_t+\int_t^s\tilde b_r\,dr+\int_t^s\tilde\sigma_r\,d\tilde B_r$ for all $s\in[t,T]$. Its characteristics are bounded by $L$ if $|\tilde b|\le L$ and $\tfrac12|\tilde\sigma|^2\le L$. For $(t,\mu)\in\Theta$ and $L>0$,
--   $$\mathcal P_L(t,\mu)=\big\{\mathbb P\in\mathcal P_2:\ \mathbb P_{[0,t]}=\mu_{[0,t]},\ X_{[t,T]}\text{ is a }\mathbb P\text{-semimartingale with characteristics bounded by }L\big\}.$$
--   Nothing is required of $X$ under $\mu$ on $[0,t]$.
--
--   **The generator and Assumption 3.1.** The master equation (3.1) is $\mathbb L V=0$ with $\mathbb LV(t,\mu)=\partial_tV(t,\mu)+G(t,\mu,V(t,\mu),\partial_\mu V(t,\mu,\cdot),\partial_\omega\partial_\mu V(t,\mu,\cdot))$, where $G(t,\mu,y,Z,\Gamma)\in\mathbb R$ and $Z,\Gamma$ are $\mathcal F_t$-measurable continuous random variables. Assumption 3.1 with constant $L_0$:
--
--   1. $G$ is continuous in $(t,\mu)$ and $L_0$-Lipschitz in $y$;
--   2. for any $(t,\mu,y)$ and $\mathcal F_t$-measurable $Z_1,\Gamma_1,Z_2,\Gamma_2$ there are $\mathcal F_t$-measurable $b_t,\sigma_t$ with $|b_t|,\tfrac12|\sigma_t|^2\le L_0$ and
--   $$G(t,\mu,y,Z_1,\Gamma_1)-G(t,\mu,y,Z_2,\Gamma_2)=\mathbb E^\mu\Big[b_t\cdot[Z_1-Z_2]+\tfrac12\sigma_t\sigma_t^\top:[\Gamma_1-\Gamma_2]\Big].\qquad(3.2)$$
--
--   These objects are the common ground of every statement of the mission.
--
--   **Formalization Note.** Time is $\mathbb R_{\ge0}$ and every condition is imposed only at $t\le T$ and $\mu\in\mathcal P_2$. The pseudometric uses the real value of the (extended) Wasserstein distance, which is finite on $\mathcal P_2$. $\mathbb P\in\mathcal P_L(t,\mu)$ is encoded by the existence of a representation as above (the paper's own definition of $\widehat{\mathcal P}_L$ in §2.4, started at $t$); the stochastic integral is the published `HasBrownianItoIntegral`, so $\int_t^s\tilde\sigma\,d\tilde B=J(s)-J(t)$. $\mathcal F_t$-measurability of a matrix is required entrywise. $G$ is a total function. Assumption 3.1(i) is read as: for fixed $y$ and fixed continuous $Z,\Gamma$ of linear growth, $(t,\mu)\mapsto G(t,\mu,y,Z(X_{t\wedge\cdot}),\Gamma(X_{t\wedge\cdot}))$ is continuous on $\Theta$ (the arguments are made $\mathcal F_t$-measurable by stopping, so that the condition lives in the paper's domain); the Lipschitz condition in $y$ and (3.2) are required on the paper's domain ($\mathcal F_t$-measurable, continuous arguments), and (3.2) for arguments whose differences are $\mu$-integrable, where the expectation is defined.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), §2.2 p. 940 ((2.4), (2.5)), §2.4 p. 944 (𝒫̂_L), §3 p. 947 ((3.1), Assumption 3.1, (3.2)), §4.1 p. 958 (𝒫_L(t, μ))

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators Matrix

namespace MasterVisc.Comparison

open EthierKurtz

/-- The canonical space `Ω = C([0,T], ℝ^d)` with the uniform norm (Wu–Zhang §2.2, p. 940). -/
abbrev Path (d : ℕ) (T : ℝ≥0) := C(Set.Icc (0 : ℝ≥0) T, SDEState d)

/-- `Ω` carries its Borel σ-algebra. -/
noncomputable instance instMeasurableSpacePath (d : ℕ) (T : ℝ≥0) : MeasurableSpace (Path d T) :=
  borel _

instance instBorelSpacePath (d : ℕ) (T : ℝ≥0) : BorelSpace (Path d T) := ⟨rfl⟩

variable {d : ℕ} {T : ℝ≥0}

/-- The canonical process: `X_s(ω) = ω(s ∧ T)`. -/
def evalAt (s : ℝ≥0) (ω : Path d T) : SDEState d :=
  ω ⟨min s T, ⟨zero_le, min_le_right _ _⟩⟩

/-- The time change `r ↦ r ∧ t` of `[0,T]`. -/
def stopTime (T t : ℝ≥0) : C(Set.Icc (0 : ℝ≥0) T, Set.Icc (0 : ℝ≥0) T) where
  toFun r := ⟨min r.1 t, ⟨zero_le, le_trans (min_le_left _ _) r.2.2⟩⟩
  continuous_toFun := by fun_prop

/-- The stopped path `ω_{t ∧ ·}`. -/
def stopAt (t : ℝ≥0) (ω : Path d T) : Path d T := ω.comp (stopTime T t)

/-- The natural filtration `F_t = σ(X_s : s ≤ t)` of the canonical process. -/
@[instance_reducible]
def filt (t : ℝ≥0) : MeasurableSpace (Path d T) :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (evalAt s) inferInstance

/-- `𝒫₂`: probability measures on `Ω` with `E^μ[‖X‖²] < ∞`. -/
def IsP2 (μ : Measure (Path d T)) : Prop :=
  IsProbabilityMeasure μ ∧ ∫⁻ ω, ‖ω‖ₑ ^ 2 ∂μ < ⊤

/-- `μ_{[0,t]}`: the law of the stopped process `X_{t∧·}` under `μ`. -/
noncomputable def restr (t : ℝ≥0) (μ : Measure (Path d T)) : Measure (Path d T) :=
  μ.map (stopAt t)

/-- The 2-Wasserstein distance on laws of continuous paths (uniform norm). -/
noncomputable def W2 (μ ν : Measure (Path d T)) : ℝ≥0∞ :=
  WassersteinDRO.Duality.wassersteinDistance 2 μ ν

/-- The 2-Wasserstein pseudometric (2.5) on `Θ = [0,T] × 𝒫₂`. -/
noncomputable def W2Θ (t : ℝ≥0) (μ : Measure (Path d T)) (t' : ℝ≥0)
    (μ' : Measure (Path d T)) : ℝ :=
  Real.sqrt (|(t : ℝ) - (t' : ℝ)| + ((W2 (restr t μ) (restr t' μ')).toReal) ^ 2)

/-- `|σ|²`, the squared Frobenius norm of a `d × d` matrix. -/
def frob2 (σ : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, σ i j ^ 2

/-- The trace product `A : B = ∑ᵢⱼ Aᵢⱼ Bᵢⱼ`. -/
def fdot (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- Continuity of `f` at every point of a subset `S ⊆ Θ`, relative to `S`, for the pseudometric `𝒲₂`. -/
def IsC0On (S : ℝ≥0 → Measure (Path d T) → Prop) (f : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  ∀ t μ, S t μ → ∀ ε > 0, ∃ δ > 0, ∀ t' μ', S t' μ' → W2Θ t μ t' μ' < δ →
    |f t' μ' - f t μ| < ε

/-- Joint continuity of a pair `(Z, Γ)` of functions on `S × Ω`, relative to `S × Ω`,
for `𝒲₂` plus the uniform distance on paths. -/
def IsC0OnΩ (S : ℝ≥0 → Measure (Path d T) → Prop)
    (Z : ℝ≥0 → Measure (Path d T) → Path d T → SDEState d)
    (Γ : ℝ≥0 → Measure (Path d T) → Path d T → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ t μ ω, S t μ → ∀ ε > 0, ∃ δ > 0, ∀ t' μ' ω', S t' μ' →
    W2Θ t μ t' μ' + ‖ω' - ω‖ < δ →
      ‖Z t' μ' ω' - Z t μ ω‖ < ε ∧ Real.sqrt (frob2 (Γ t' μ' ω' - Γ t μ ω)) < ε

/-- `Θ = [0,T] × 𝒫₂` as a predicate. -/
def InΘ (t : ℝ≥0) (μ : Measure (Path d T)) : Prop := t ≤ T ∧ IsP2 μ

/-- `V ∈ C⁰(Θ)`: continuity on `Θ` for the pseudometric `𝒲₂` of (2.5). -/
def IsC0Θ (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop := IsC0On (InΘ (T := T)) V

/-- `V` is `𝔽`-adapted: `V(t, μ) = V(t, μ_{[0,t]})`. -/
def IsAdaptedΘ (V : ℝ≥0 → Measure (Path d T) → ℝ) : Prop :=
  ∀ t μ, t ≤ T → IsP2 μ → V t μ = V t (restr t μ)

/-- `g ∈ C⁰(𝒫₂; ℝ)`: continuity on `𝒫₂` for `𝒲₂`. -/
def IsC0P2 (g : Measure (Path d T) → ℝ) : Prop :=
  ∀ μ, IsP2 μ → ∀ ε > 0, ∃ δ > 0, ∀ μ', IsP2 μ' → W2 μ μ' < ENNReal.ofReal δ →
    |g μ' - g μ| < ε

/-- A representation of a law on `Ω` as the law of an Itô process (§2.4, p. 944): a filtered
probability space, a Brownian motion, drift and diffusion coefficients, and the path-valued process. -/
structure Rep (d : ℕ) (T : ℝ≥0) where
  /-- the underlying sample space `Ω̃` -/
  Ω' : Type
  /-- its σ-algebra -/
  mΩ : MeasurableSpace Ω'
  /-- the probability `ℙ̃` -/
  P' : Measure Ω'
  /-- the filtration `𝔽̃` -/
  F' : Filtration ℝ≥0 mΩ
  /-- the Brownian motion `B̃` -/
  B : ℝ≥0 → Ω' → SDEState d
  /-- the drift `b̃` -/
  b : ℝ≥0 → Ω' → SDEState d
  /-- the diffusion coefficient `σ̃` -/
  σ : ℝ≥0 → Ω' → Matrix (Fin d) (Fin d) ℝ
  /-- the process `X̃`, as a path-valued random variable -/
  Y : Ω' → Path d T

attribute [instance] Rep.mΩ

/-- `R` represents `P` as an Itô process on `[t, T]`: `P = ℙ̃ ∘ X̃⁻¹`, `B̃` is an `𝔽̃`-Brownian motion,
`b̃, σ̃` are `𝔽̃`-progressively measurable and bounded, `X̃` is `𝔽̃`-adapted, and almost surely
`X̃_s = X̃_t + ∫_t^s b̃_r dr + ∫_t^s σ̃_r dB̃_r` for all `s ∈ [t,T]`. Nothing is required of `X̃` on `[0,t]`
beyond adaptedness. -/
def IsRepFrom (t : ℝ≥0) (P : Measure (Path d T)) (R : Rep d T) : Prop :=
  IsProbabilityMeasure R.P' ∧ Measurable R.Y ∧ R.P'.map R.Y = P ∧
  IsStandardBrownian R.P' R.B ∧
  (∀ s, Measurable[R.F' s] (R.B s)) ∧
  (∀ s, Indep (R.F' s)
    (MeasurableSpace.comap (fun ω (r : Set.Ici s) => R.B r.val ω - R.B s ω) inferInstance) R.P') ∧
  IsStronglyProgressive R.F' R.b ∧ IsStronglyProgressive R.F' R.σ ∧
  (∃ C : ℝ, ∀ s ω, ‖R.b s ω‖ ≤ C ∧ frob2 (R.σ s ω) ≤ C) ∧
  (∀ s, Measurable[R.F' s] (fun ω => evalAt s (R.Y ω))) ∧
  ∃ J : ℝ≥0 → R.Ω' → Matrix (Fin d) (Fin d) ℝ,
    (∀ i j, HasBrownianItoIntegral R.P' (fun s => R.F' s) (fun s ω => R.B s ω j)
      (fun s ω => R.σ s ω i j) (fun s ω => J s ω i j)) ∧
    ∀ᵐ ω ∂(R.P'), ∀ s, t ≤ s → s ≤ T → ∀ i,
      evalAt s (R.Y ω) i = evalAt t (R.Y ω) i +
        (∫ r in (t : ℝ)..(s : ℝ), R.b r.toNNReal ω i) + ∑ j, (J s ω i j - J t ω i j)

/-- The characteristics of `R` are bounded by `L`: `|b̃| ≤ L` and `½|σ̃|² ≤ L`. -/
def RepBound (L : ℝ) (R : Rep d T) : Prop :=
  ∀ s ω, ‖R.b s ω‖ ≤ L ∧ frob2 (R.σ s ω) / 2 ≤ L

/-- `ℙ ∈ 𝒫_L(t, μ)` (§4.1, p. 958): `ℙ ∈ 𝒫₂`, `ℙ_{[0,t]} = μ_{[0,t]}`, and `X_{[t,T]}` is a
`ℙ`-semimartingale with drift and diffusion characteristics bounded by `L`. -/
def InPL (L : ℝ) (t : ℝ≥0) (μ P : Measure (Path d T)) : Prop :=
  IsP2 P ∧ restr t P = restr t μ ∧ ∃ R : Rep d T, IsRepFrom t P R ∧ RepBound L R

/-- The type of generators `G(t, μ, y, Z, Γ)` of the master equation (3.1). -/
abbrev Gen (d : ℕ) (T : ℝ≥0) :=
  ℝ≥0 → Measure (Path d T) → ℝ → (Path d T → SDEState d) →
    (Path d T → Matrix (Fin d) (Fin d) ℝ) → ℝ

/-- The domain of `G` at time `t` (p. 947): `Z ∈ C⁰(Ω; ℝ^d)`, `Γ ∈ C⁰(Ω; ℝ^{d×d})`, both
`F_t`-measurable (the matrix entrywise). -/
def IsGenArg (t : ℝ≥0) (Z : Path d T → SDEState d) (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ) :
    Prop :=
  Continuous Z ∧ Continuous Γ ∧ Measurable[filt t] Z ∧
  ∀ i j, Measurable[filt t] (fun ω => Γ ω i j)

/-- Linear growth: `|Z(ω)| + |Γ(ω)| ≤ C[1 + ‖ω‖]` for some `C`. -/
def IsLinGrowth (Z : Path d T → SDEState d) (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ C : ℝ, ∀ ω, ‖Z ω‖ + Real.sqrt (frob2 (Γ ω)) ≤ C * (1 + ‖ω‖)

/-- Assumption 3.1 (p. 947) with Lipschitz constant `L₀`.
(i) For fixed `y` and fixed continuous `Z, Γ` of linear growth, `(t, μ) ↦ G(t, μ, y, Z(X_{t∧·}), Γ(X_{t∧·}))`
is continuous on `Θ`; and `G` is `L₀`-Lipschitz in `y` on its domain.
(ii) For `F_t`-measurable continuous arguments with `μ`-integrable differences there are `F_t`-measurable
`b_t, σ_t` with `|b_t|, ½|σ_t|² ≤ L₀` and (3.2). -/
def Assumption31 (L₀ : ℝ) (G : Gen d T) : Prop :=
  (∀ (y : ℝ) (Z : Path d T → SDEState d) (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ),
    Continuous Z → Continuous Γ → IsLinGrowth Z Γ →
      IsC0Θ (fun t μ => G t μ y (fun ω => Z (stopAt t ω)) (fun ω => Γ (stopAt t ω)))) ∧
  (∀ t μ (y y' : ℝ) (Z : Path d T → SDEState d) (Γ : Path d T → Matrix (Fin d) (Fin d) ℝ),
    t ≤ T → IsP2 μ → IsGenArg t Z Γ → |G t μ y Z Γ - G t μ y' Z Γ| ≤ L₀ * |y - y'|) ∧
  (∀ t μ (y : ℝ) (Z₁ Z₂ : Path d T → SDEState d) (Γ₁ Γ₂ : Path d T → Matrix (Fin d) (Fin d) ℝ),
    t ≤ T → IsP2 μ → IsGenArg t Z₁ Γ₁ → IsGenArg t Z₂ Γ₂ →
    Integrable (fun ω => ‖Z₁ ω - Z₂ ω‖) μ →
    Integrable (fun ω => Real.sqrt (frob2 (Γ₁ ω - Γ₂ ω))) μ →
    ∃ (b : Path d T → SDEState d) (σ : Path d T → Matrix (Fin d) (Fin d) ℝ),
      Measurable[filt t] b ∧ (∀ i j, Measurable[filt t] (fun ω => σ ω i j)) ∧
      (∀ ω, ‖b ω‖ ≤ L₀ ∧ frob2 (σ ω) / 2 ≤ L₀) ∧
      G t μ y Z₁ Γ₁ - G t μ y Z₂ Γ₂ =
        ∫ ω, (inner ℝ (b ω) (Z₁ ω - Z₂ ω) + fdot (σ ω * (σ ω)ᵀ) (Γ₁ ω - Γ₂ ω) / 2) ∂μ)

end MasterVisc.Comparison


