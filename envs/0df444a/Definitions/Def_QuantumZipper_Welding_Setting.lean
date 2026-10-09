-- Prove2me | Definitions.Def_QuantumZipper_Welding_Setting
-- name    : QuantumZipper_Welding_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:38.559833+00:00
-- url     : https://prove2.me/theorems/b68383ee-d8f2-468d-9949-66cde37857b3
-- title:
--   Setting: $\mathbb H$, $G^{\mathbb H_F}$, arc averages, conditionally Gaussian fields, reverse Loewner flows, $\mathfrak h_t$ and $\hat{\mathfrak h}_t$ (4.4)–(4.6)
-- statement:
--   This file fixes the shared objects of the mission, following Sheffield, *Conformal weldings of random surfaces* (§1.2, §1.3, §3, §4.2).
--
--   1. **Half-plane and Green's function.** $\mathbb H=\{z\in\mathbb C:\operatorname{Im}z>0\}$, and the free boundary Green's function is
--   $$G(y,z)=G^{\mathbb H_F}(y,z)=-\log|y-z|-\log|y-\bar z| .$$
--   There is no factor $1/(2\pi)$: the Dirichlet inner product carries $(2\pi)^{-1}$, so that $\operatorname{Cov}((h,\rho_1),(h,\rho_2))=\iint\rho_1G\rho_2$, as in (3.6). Also $Q(\gamma)=2/\gamma+\gamma/2$.
--   2. **Arc averages.** For $z$ with $\operatorname{Im}z\ge0$ and $\varepsilon>0$, $\sigma_{z,\varepsilon}$ is the uniform probability measure on the arc $\partial B_\varepsilon(z)\cap\mathbb H$: a full circle when $\varepsilon<\operatorname{Im}z$, the upper semicircle when $z\in\mathbb R$. The pairing $(h,\sigma_{z,\varepsilon})=h_\varepsilon(z)$ is the circle (or semicircle) average of the paper. $\sigma_{0,1}$ is the upper unit semicircle.
--   3. **Normalization $h_1(0)=0$.** For a field with mean function $m$ and covariance kernel $K$, the pairing with $\mu-\mu(\mathbb C)\sigma_{0,1}$ has mean $\int m\,d\mu-\mu(\mathbb C)\int m\,d\sigma_{0,1}$ and the bilinearly expanded covariance of $\iint K\,d(\mu-\mu(\mathbb C)\sigma_{0,1})\,d(\nu-\nu(\mathbb C)\sigma_{0,1})$. This is how a field defined modulo additive constants becomes a field once $h_1(0)=0$ is fixed.
--   4. **Admissible measures.** Finite measures on $\mathbb C$ with bounded support, no mass outside $\mathbb H$, and finite logarithmic energy $\iint|\log|u-v||\,\mu(du)\mu(dv)<\infty$. Every arc measure is admissible.
--   5. **Conditionally Gaussian field.** A random field $\Psi(\omega,\mu)=(h,\mu)$ is Gaussian on an event $E$ given a $\sigma$-algebra $\mathcal G$, with mean $m$ and covariance $C$, if for all admissible $\mu_1,\dots,\mu_n$, $t\in\mathbb R^n$ and $S\in\mathcal G$ with $S\subseteq E$,
--   $$\mathbb E\Big[\mathbf 1_S\,e^{i\sum_j t_j\Psi(\mu_j)}\Big]=\mathbb E\Big[\mathbf 1_S\,e^{i\sum_jt_jm(\mu_j)-\frac12\sum_{j,k}t_jt_kC(\mu_j,\mu_k)}\Big].$$
--   6. **Reverse Loewner flow (1.7), (4.5).** Given a driving function $W$, $f_t(z)=g_t(z)-W_t$ where $\partial_tg_t(z)=-2/(g_t(z)-W_t)$, $g_0(z)=z$, and $f_t(z)\in\mathbb H$ for $z\in\mathbb H$. At a real point $x$ the same ODE holds until $f_t(x)$ first reaches $0$ (the continuous extension of $f_t$ to $\mathbb R$), and $t\mapsto g_t(x)$ is left-continuous at that time. $f_t'$ is the complex derivative in $z$.
--   7. **Fields of Theorems 1.2 and 4.5.** $\mathfrak h_0(z)=\frac2{\sqrt\kappa}\log|z|$, $\mathfrak h_t(z)=\mathfrak h_0(f_t(z))+Q\log|f_t'(z)|$ with $Q=2/\sqrt\kappa+\sqrt\kappa/2$, and for a signed measure $\rho=\rho_+-\rho_-$,
--   $$\hat{\mathfrak h}_t(z)=\mathfrak h_t(z)+\frac1{2\sqrt\kappa}\int G(f_t(y),f_t(z))\,\rho(dy).\qquad(4.4)$$
--   8. **Driving function of reverse $\mathrm{SLE}_{\kappa,\rho}$ (4.6).** $W_t=\sqrt\kappa B_t+\int_0^t\int\operatorname{Re}\frac{-1}{f_s(y)}\,\rho(dy)\,ds$ for $t<T$.
--   9. **Test functions.** Smooth, compactly supported, mean-zero functions with support in $\mathbb H$; $(F,\rho)=\int F\rho$, and $E^f(\rho)=\iint\rho(y)G(f(y),f(z))\rho(z)\,dy\,dz$.
--
--   These are the shared objects of every statement in the mission.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$, as in Mathlib's Brownian motion. All flows are pathwise (no stochastic integral). The conditionally Gaussian predicate is the characteristic-function form of "the conditional law given $\mathcal G$ is $N(m,C)$". The identity (4.6) is imposed for $t<T$ only, since at the time a real force point reaches $0$ the integral may be improper.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §1.2 (pp. 6–8, (1.1)–(1.3), footnote 1), Theorem 1.2 (p. 13, (1.7)), §3.1–3.3 (pp. 37–42, (3.6)), §4.2 (p. 51, (4.4)–(4.6))

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_FreeBoundaryGFF
import Definitions.Def_QuantumZipper_ReverseCoupling_ReverseLoewnerFlow
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper.Welding

/-! # Shared setting: half-plane, Green's function, arc averages, reverse Loewner flows

Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797v2. Everything here is taken from §1.2 (pp. 6–9), §1.3 (Theorem 1.2, pp. 13–14),
§3.1–3.3 (pp. 37–42) and §4.2 ((4.4)–(4.6), p. 51). -/

/-- The open upper half-plane `ℍ = {z : ℂ | 0 < Im z}` (arXiv:1012.4797v2, §3.1, p. 37). -/
def Hplane : Set ℂ := {z : ℂ | 0 < z.im}

/-- `Q = 2/γ + γ/2` (arXiv:1012.4797v2, p. 7; with `γ = √κ` this is the `Q = 2/√κ + √κ/2` of
Theorem 1.2, p. 13). -/
noncomputable def Qc (γ : ℝ) : ℝ := 2 / γ + γ / 2

/-- The angles `θ ∈ (0, 2π]` for which `z + ε e^{iθ}` lies in `ℍ`. -/
def arcAngles (z : ℂ) (ε : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧ 0 < (z + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im}

/-- The uniform probability measure `σ_{z,ε}` on the arc `∂B_ε(z) ∩ ℍ` (arXiv:1012.4797v2, p. 7:
"`h_ε(z)` is the mean value of `h` on the circle `∂B_ε(z)`"; "When `x ∈ ∂D`, we let `h_ε(x)` be the
mean value of `h` on `D ∩ ∂B_ε(x)`"). For `z ∈ ℍ` and `ε < Im z` it is the uniform measure on the
whole circle; for `z = x ∈ ℝ` it is the uniform measure on the upper semicircle; in general it is
normalized arc length on the part of the circle inside `ℍ`.

**Formalization Note** Built as the normalized push-forward of Lebesgue measure on the angle set
`arcAngles z ε`. For `Im z ≤ −ε` the angle set is empty and the measure is `0` (never used). -/
noncomputable def arcMeasure (z : ℂ) (ε : ℝ) : Measure ℂ :=
  (volume (arcAngles z ε))⁻¹ •
    (volume.restrict (arcAngles z ε)).map
      (fun θ : ℝ => z + (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))

/-- `σ_{0,1}`, the uniform probability measure on the upper unit semicircle `∂B₁(0) ∩ ℍ`, used for
the normalization `h₁(0) = 0` (Figure 1.7, p. 27; (5.9), p. 67). -/
noncomputable def sigma01 : Measure ℂ := arcMeasure 0 1

/-- The energy `∫∫ K(u, v) μ(du) ν(dv)` of two measures against a kernel `K` (the covariance (3.6)
extended to measures, §3.3, p. 41: "the inner products (3.5) and (3.6) still make sense when
`ρ₁(z)dz` and `ρ₂(z)dz` are replaced with more general measures"). -/
noncomputable def kernelEnergy (K : ℂ → ℂ → ℝ) (μ ν : Measure ℂ) : ℝ :=
  ∫ p : ℂ × ℂ, K p.1 p.2 ∂(μ.prod ν)

/-- Mean of the pairing `(h, μ − μ(ℂ)·σ_{0,1})` for a field with mean function `m`: the value of
`∫ m dμ` after fixing the additive constant by `h₁(0) = 0`. -/
noncomputable def normMean (m : ℂ → ℝ) (μ : Measure ℂ) : ℝ :=
  (∫ u, m u ∂μ) - (μ Set.univ).toReal * ∫ u, m u ∂sigma01

/-- Covariance of the pairings `(h, μ − μ(ℂ)σ_{0,1})` and `(h, ν − ν(ℂ)σ_{0,1})` for a field with
covariance kernel `K`, i.e. the bilinear expansion of `∫∫ K d(μ − μ(ℂ)σ_{0,1}) d(ν − ν(ℂ)σ_{0,1})`.
This is how a field defined modulo additive constants becomes a field once `h₁(0) = 0` is fixed
(p. 15, p. 67). -/
noncomputable def normCov (K : ℂ → ℂ → ℝ) (μ ν : Measure ℂ) : ℝ :=
  kernelEnergy K μ ν - (ν Set.univ).toReal * kernelEnergy K μ sigma01
    - (μ Set.univ).toReal * kernelEnergy K sigma01 ν
    + (μ Set.univ).toReal * (ν Set.univ).toReal * kernelEnergy K sigma01 sigma01

/-- **Admissible measures**: the finite measures against which a field is paired. A finite measure
on `ℂ` with bounded support, no mass outside `ℍ`, and finite logarithmic energy
`∫∫ |log |u − v|| μ(du) μ(dv) < ∞` (so that (3.6) is finite, §3.3, p. 41). Every arc measure
`σ_{z,ε}` with `Im z ≥ 0`, `ε > 0` is admissible (the two endpoints of a semicircle are a null set).

**Formalization Note** Bounded support is a well-posedness restriction: it makes `∫ 𝔥_t dμ` finite
for the logarithmically growing mean functions of this paper. -/
structure IsAdmissible (μ : Measure ℂ) : Prop where
  finite : IsFiniteMeasure μ
  bounded : ∃ R : ℝ, μ (Metric.closedBall (0 : ℂ) R)ᶜ = 0
  inH : μ Hplaneᶜ = 0
  logEnergy : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod μ)

/-- **Conditionally Gaussian field.** A random field `Ψ : Ω → Measure ℂ → ℝ` (`Ψ ω μ` is the
pairing `(h, μ)` of the sample `ω`) is, on the event `E` and conditionally on the σ-algebra `𝒢`,
Gaussian with mean `m ω μ` and covariance `C ω μ ν` on the index class `Adm`: for every finite
family `μ₁, …, μₙ` in `Adm`, every `t ∈ ℝⁿ` and every `S ∈ 𝒢` with `S ⊆ E`,
`E[1_S exp(i Σ t_j Ψ(μ_j))] = E[1_S exp(i Σ t_j m(μ_j) − ½ Σ t_j t_k C(μ_j, μ_k))]`.

**Formalization Note** This is the characteristic-function form of "the conditional law of
`(Ψ(μ_j))_j` given `𝒢` is `N((m(μ_j))_j, (C(μ_j, μ_k))_{jk})`" (for `𝒢`-measurable `m`, `C`). It is
how the paper's "given `B`, … is a GFF plus a deterministic function" statements are encoded
(p. 15, p. 65, pp. 66–67), with `h̃ ∘ f` paired with `μ` as `h̃` paired with the push-forward of `μ`
(footnote 1, p. 7, extended to measures, §3.3, p. 41). -/
def IsCondGaussianFieldOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝒢 : MeasurableSpace Ω) (E : Set Ω) (Adm : Measure ℂ → Prop) (Ψ : Ω → Measure ℂ → ℝ)
    (m : Ω → Measure ℂ → ℝ) (C : Ω → Measure ℂ → Measure ℂ → ℝ) : Prop :=
  (∀ μ, Adm μ → Measurable fun ω => Ψ ω μ) ∧
  ∀ (n : ℕ) (μ : Fin n → Measure ℂ), (∀ j, Adm (μ j)) → ∀ (t : Fin n → ℝ) (S : Set Ω),
    MeasurableSet[𝒢] S → S ⊆ E →
      ∫ ω in S, Complex.exp (Complex.I * ((∑ j, t j * Ψ ω (μ j) : ℝ) : ℂ)) ∂P =
        ∫ ω in S, Complex.exp (Complex.I * ((∑ j, t j * m ω (μ j) : ℝ) : ℂ)
          - ((1 / 2 * ∑ j, ∑ k, t j * t k * C ω (μ j) (μ k) : ℝ) : ℂ)) ∂P

/-- The σ-algebra `σ(X_s : s ≤ t)` of a real process up to time `t` (natural filtration). -/
@[instance_reducible] def natSigma {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (X s) inferInstance

/-- The σ-algebra `σ(X_s : s ≥ 0)` generated by a whole real process. -/
@[instance_reducible] def pathSigma {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) : MeasurableSpace Ω :=
  ⨆ s : ℝ≥0, MeasurableSpace.comap (X s) inferInstance

/-! ## Reverse Loewner flow (1.7), (4.5), pathwise -/

/-- The driving function `W_t = √κ B_t(ω)` of reverse `SLE_κ` ((1.7), p. 13). -/
noncomputable def bmDrive {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ :=
  fun t => Real.sqrt κ * B t ω

/-- The pulled-back Green's function `G_t(u, v) = G(f_t(u), f_t(v))` (p. 47), the covariance kernel
of `h̃ ∘ f_t` (footnote 1, p. 7). -/
noncomputable def revCov (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (u v : ℂ) : ℝ :=
  QuantumZipper.ReverseCoupling.greenFree (QuantumZipper.ReverseCoupling.revF W g t u) (QuantumZipper.ReverseCoupling.revF W g t v)

/-- **The flow at a real point `x`**, which is the continuous extension of `f_t` to `ℝ`
(p. 52: "here `f_t` is extended continuously from `ℍ` to `ℍ̄`"). As long as `f_s(x) ≠ 0` for all
`s ≤ t`, the point stays real and solves the same ODE `∂_t g_t(x) = −2/(g_t(x) − W_t)`, `g₀(x) = x`;
and `t ↦ g_t(x)` is left-continuous at the first time `f_t(x)` reaches `0`. Nothing is asserted after
that time (the point has been zipped into the curve).

**Formalization Note** For a real point the reverse flow is the real ODE
`d f_t(x) = −2/f_t(x) dt − dW_t` ((4.8), p. 52, with `ρ₁ = 0`) up to its hitting time of `0`. -/
def IsRealPointFlow (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (x : ℝ) : Prop :=
  g 0 (x : ℂ) = x ∧
  ∀ t : ℝ≥0,
    ((∀ s < t, QuantumZipper.ReverseCoupling.revF W g s x ≠ 0) →
      ContinuousWithinAt (fun s : ℝ => g (Real.toNNReal s) x) (Set.Iic (t : ℝ)) (t : ℝ)) ∧
    ((∀ s ≤ t, QuantumZipper.ReverseCoupling.revF W g s x ≠ 0) →
      (g t x).im = 0 ∧
      HasDerivWithinAt (fun s : ℝ => g (Real.toNNReal s) x) (-2 / QuantumZipper.ReverseCoupling.revF W g t x)
        (Set.Ici 0) (t : ℝ))

/-- `𝔥_t(z) = 𝔥₀(f_t(z)) + Q log |f′_t(z)|` with `𝔥₀(z) = (2/√κ) log |z|` and
`Q = 2/√κ + √κ/2` (arXiv:1012.4797v2, Theorem 1.2, p. 13; fraktur `𝔥` in the PDF). -/
noncomputable def frakH (κ : ℝ) (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  2 / Real.sqrt κ * Real.log ‖QuantumZipper.ReverseCoupling.revF W g t z‖ + Qc (Real.sqrt κ) * Real.log ‖QuantumZipper.ReverseCoupling.revFDeriv W g t z‖

/-- `ĥ_t(z) = 𝔥_t(z) + (1/(2√κ)) ∫ G_t(y, z) ρ(dy)` with `G_t(y, z) = G(f_t(y), f_t(z))`
(arXiv:1012.4797v2, (4.4), p. 51). The signed measure `ρ = ρ₊ − ρ₋` is given by its positive and
negative parts, two finite measures. -/
noncomputable def hatH (κ : ℝ) (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (ρp ρn : Measure ℂ) (t : ℝ≥0)
    (z : ℂ) : ℝ :=
  frakH κ W g t z + 1 / (2 * Real.sqrt κ) *
    ((∫ y, QuantumZipper.ReverseCoupling.greenFree (QuantumZipper.ReverseCoupling.revF W g t y) (QuantumZipper.ReverseCoupling.revF W g t z) ∂ρp) -
      ∫ y, QuantumZipper.ReverseCoupling.greenFree (QuantumZipper.ReverseCoupling.revF W g t y) (QuantumZipper.ReverseCoupling.revF W g t z) ∂ρn)

/-- `ĥ₀(z) = 𝔥₀(z) + (1/(2√κ)) ∫ G(y, z) ρ(dy)` ((4.4) at `t = 0`, where `f₀ = id`). -/
noncomputable def hatH0 (κ : ℝ) (ρp ρn : Measure ℂ) (z : ℂ) : ℝ :=
  QuantumZipper.ReverseCoupling.frakH0 κ z + 1 / (2 * Real.sqrt κ) *
    ((∫ y, QuantumZipper.ReverseCoupling.greenFree y z ∂ρp) - ∫ y, QuantumZipper.ReverseCoupling.greenFree y z ∂ρn)

/-- The drift `∫ Re(−1/f_t(y)) ρ(dy) = (−Re (f_t)⁻¹, ρ)` of (4.6), p. 51. -/
noncomputable def drift (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (ρp ρn : Measure ℂ) (t : ℝ≥0) : ℝ :=
  (∫ y, (-(QuantumZipper.ReverseCoupling.revF W g t y)⁻¹).re ∂ρp) - ∫ y, (-(QuantumZipper.ReverseCoupling.revF W g t y)⁻¹).re ∂ρn

/-- `W` is the driving function of the reverse `SLE_{κ,ρ}` flow (4.5)–(4.6) up to time `T`:
`W_t = √κ B_t + ∫₀ᵗ (∫ Re(−1/f_s(y)) ρ(dy)) ds` for `t < T`, where `f_s = g_s − W_s`
(arXiv:1012.4797v2, (4.6), p. 51, pathwise; a fixed-point condition coupling `W` and `g`).

**Formalization Note** The identity is imposed for `t < T`; `W_T` is then fixed by continuity of `W`.
At `t = T` a real force point may reach `0`, where `∫₀^T` can be improper (for a Bessel process of
dimension `≤ 1`, `∫ ds/X_s` diverges at the hitting time), so a Bochner integral there could be a junk
`0`. -/
def IsSLEκρDriver (κ : ℝ) (b : ℝ≥0 → ℝ) (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (ρp ρn : Measure ℂ)
    (T : ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, t < T →
    W t = Real.sqrt κ * b t + ∫ s in (0 : ℝ)..(t : ℝ), drift W g ρp ρn (Real.toNNReal s)

/-! ## Test functions (for the distributional statements) -/

/-- A smooth, compactly supported, mean-zero test function with support in `ℍ`
(arXiv:1012.4797v2, §3.1.2, p. 37: pairings of a modulo-additive-constant distribution are taken
only against `ρ ∈ H_s(ℍ)` with `∫ ρ = 0`). -/
def IsMeanZeroTest (ρ : ℂ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Hplane ∧ ∫ z, ρ z = 0

/-- The pairing `(F, ρ) = ∫ F(z) ρ(z) dz` (§3.1.1, p. 37). -/
noncomputable def pairing (F : ℂ → ℝ) (ρ : ℂ → ℝ) : ℝ :=
  ∫ z, F z * ρ z

/-- `E^f(ρ) = ∫∫ ρ(y) G(f(y), f(z)) ρ(z) dy dz`, the free boundary energy (3.6) pulled back by `f`
(so `E^{f_t}(ρ) = E_t(ρ)` of p. 47, and `E^{id}(ρ) = E₀(ρ)`). -/
noncomputable def energyUnder (f : ℂ → ℂ) (ρ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, ρ p.1 * QuantumZipper.ReverseCoupling.greenFree (f p.1) (f p.2) * ρ p.2

end QuantumZipper.Welding


