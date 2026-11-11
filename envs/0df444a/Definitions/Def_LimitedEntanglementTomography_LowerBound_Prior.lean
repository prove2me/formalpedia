-- Prove2me | Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior
-- name    : LimitedEntanglementTomography_LowerBound_Prior
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:54.046637+00:00
-- url     : https://prove2.me/theorems/981c7bf3-3cd9-4486-9615-cb7dc7da03f7
-- title:
--   Gaussian measures on $\mathbb R^s$, the truncated Gaussian prior on $\mathrm{Herm}_0(\mathbb C^d)$, entropy and mutual information
-- statement:
--   For $\kappa>0$ and $K\subseteq\mathbb R^s$, the measure
--   $$d\mu_K(x)=\frac1{Z_K}\,e^{-\kappa\|x\|_2^2/2}\,\mathbf 1_K(x)\,dx$$
--   is the centered Gaussian of covariance $\kappa^{-1}I$ conditioned on $K$; with $\kappa=1$ and $K=\mathbb R^s$ it is the standard Gaussian, and a standard Gaussian on $\mathrm{Herm}_0(\mathbb C^d)$ is $Z=\sum_b\theta_bF_b$ with $\theta$ standard Gaussian on $\mathbb R^{d^2-1}$.
--
--   The prior of §6.1: for $C_*\ge2$ and $\varepsilon>0$ put $\tau=C_*\varepsilon$, $\kappa=d^3/(2\tau^2)$ and
--   $$K=\Big\{\Delta\in\mathrm{Herm}_0(\mathbb C^d):\ \|\Delta\|_{\mathrm{op}}\le\frac{C_*\tau}{d}\Big\};$$
--   $\bar\mu$ is the centered Gaussian on $\mathrm{Herm}_0(\mathbb C^d)$ with covariance $\kappa^{-1}I$, and $\mu=\bar\mu(\,\cdot\mid K)$, i.e. $d\mu(\Delta)\propto e^{-\kappa\|\Delta\|_F^2/2}\mathbf 1_K(\Delta)\,d\Delta$.
--
--   For a probability measure $\mu$ and a positive $f$ with $\mathbb E_\mu f=1$, $\mathrm{Ent}_\mu(f)=\mathbb E_\mu[f\log f]\in[0,\infty]$, and $\mathbb E_\mu[\|\nabla f\|_2^2/f]\in[0,\infty]$, with gradients in the coordinates. The mutual information of a joint law is $I(X;Y)=D(P_{XY}\,\|\,P_X\otimes P_Y)\in[0,\infty]$ in nats, with $D=+\infty$ without absolute continuity. Finally, the joint law of $(\Delta,Y)$ when $\Delta\sim\mu$ and $Y$ is the transcript of a protocol on input $\rho_\star+\Delta$ is $\mu\otimes P_{\rho_\star+\Delta}$.
--
--   The prior is the hard instance of the lower bound; entropy, the Fisher functional and mutual information are the quantities linked by the log-Sobolev and Fano arguments.
--
--   **Formalization Note** $\mathrm{Ent}_\mu(f)$ is stored as $\mathbb E_\mu[f\log f-f+1]$, whose integrand is nonnegative and which equals $\mathbb E_\mu[f\log f]$ when $\mathbb E_\mu f=1$, the only case used. Natural logarithms throughout. KL divergence is Mathlib's `klDiv`.
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.4, printed p.16 / PDF p.18 (relative entropy, mutual information, entropy functional); Corollary 4.22, printed p.19 / PDF p.21; §6.1 eqs. (38)–(40), printed p.23 / PDF p.25

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Protocol

open scoped ENNReal ComplexOrder
noncomputable section

/-!
# Gaussian measures, the truncated Gaussian prior, entropy and mutual information

Keskin, Luo, Majid, Radzihovsky, STOC 2027 submission #1625 (October 2026): §4.4 (printed
p.16 / PDF p.18), §4.5 (printed pp.18–19 / PDF pp.20–21), §6.1 (printed p.23 / PDF p.25).

Coordinates: `Herm₀(ℂ^d)` is identified with `ℝ^{d²−1}` (`EuclideanSpace`, Lebesgue measure)
through an orthonormal basis `F` (`herm0Coord`), an isometry for the Frobenius norm. All
logarithms are natural.
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix

/-- Real coordinates `ℝ^s` with the Euclidean inner product and Lebesgue measure. -/
abbrev Coord (s : ℕ) := EuclideanSpace ℝ (Fin s)

/-- The unnormalized measure `e^{−κ‖x‖²/2} 1_K(x) dx` on `ℝ^s`. -/
def gaussWeight (s : ℕ) (κ : ℝ) (K : Set (Coord s)) : Measure (Coord s) :=
  (volume.restrict K).withDensity (fun x => ENNReal.ofReal (Real.exp (-(κ * ‖x‖ ^ 2 / 2))))

/-- Corollary 4.22 / eq. (40): `dμ_K(x) = Z_K⁻¹ e^{−κ‖x‖²/2} 1_K(x) dx`, the centered Gaussian of
covariance `κ⁻¹ I` conditioned on `K` (`K = univ`: the Gaussian itself). -/
def truncGauss (s : ℕ) (κ : ℝ) (K : Set (Coord s)) : Measure (Coord s) :=
  (gaussWeight s κ K Set.univ)⁻¹ • gaussWeight s κ K

/-- The standard Gaussian measure on `ℝ^s` (in coordinates of an orthonormal basis: the standard
Gaussian on the real Hilbert space). -/
def stdGauss (s : ℕ) : Measure (Coord s) := truncGauss s 1 Set.univ

/-- Eq. (38): `κ = d³ / (2τ²)` with `τ = C_* ε`. -/
def priorKappa (d : ℕ) (Cstar ε : ℝ) : ℝ := (d : ℝ) ^ 3 / (2 * (Cstar * ε) ^ 2)

/-- Eq. (39): `K = {Δ ∈ Herm₀(ℂ^d) : ‖Δ‖_op ≤ C_* τ / d}` with `τ = C_* ε`, in coordinates. -/
def priorK {d : ℕ} (F : Fin (d ^ 2 - 1) → Op d) (Cstar ε : ℝ) : Set (Coord (d ^ 2 - 1)) :=
  {θ | opNorm (herm0Coord F θ) ≤ Cstar * (Cstar * ε) / d}

/-- `μ̄`: the centered Gaussian on `Herm₀(ℂ^d)` with covariance `κ⁻¹ I`, in coordinates. -/
def priorBar (d : ℕ) (Cstar ε : ℝ) : Measure (Coord (d ^ 2 - 1)) :=
  truncGauss (d ^ 2 - 1) (priorKappa d Cstar ε) Set.univ

/-- Eq. (40): the prior `μ`, the law `μ̄` conditioned on `K`. -/
def prior {d : ℕ} (F : Fin (d ^ 2 - 1) → Op d) (Cstar ε : ℝ) : Measure (Coord (d ^ 2 - 1)) :=
  truncGauss (d ^ 2 - 1) (priorKappa d Cstar ε) (priorK F Cstar ε)

/-- §4.4: `Ent_μ(f) = E_μ[f log f] − E_μ f log E_μ f` for a positive `f` with `E_μ f = 1`, as an
element of `[0, ∞]`; it is written as `E_μ[f log f − f + 1]`, whose integrand is nonnegative and
which equals `E_μ[f log f]` when `E_μ f = 1`. Every use below assumes `E_μ f = 1`. -/
def entropy {s : ℕ} (μ : Measure (Coord s)) (f : Coord s → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (f x * Real.log (f x) - f x + 1) ∂μ

/-- `E_μ[‖∇f‖₂² / f]`, as an element of `[0, ∞]`. -/
def fisherFunctional {s : ℕ} (μ : Measure (Coord s)) (f : Coord s → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2 / f x) ∂μ

/-- §4.4: the mutual information `I(X; Y) = D(P_{XY} ‖ P_X ⊗ P_Y)` of a joint law, in nats and in
`[0, ∞]` (`+∞` without absolute continuity). -/
def mutualInfo {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (P : Measure (X × Y)) :
    ℝ≥0∞ :=
  InformationTheory.klDiv P (P.fst.prod P.snd)

/-- The input map `θ ↦ ρ_⋆ + ∑_b θ_b F_b`. -/
theorem measurable_translate {d : ℕ} (F : Fin (d ^ 2 - 1) → Op d) (ρstar : Op d) :
    Measurable (fun θ : Coord (d ^ 2 - 1) => ρstar + herm0Coord F θ) := by
  apply Continuous.measurable
  unfold herm0Coord
  fun_prop

/-- §§6–7: the joint law of `(Δ, Y)` when `Δ ∼ μ` and `Y` is the transcript of the protocol on
input `ρ_⋆ + Δ`. -/
def jointLaw {d k : ℕ} (μ : Measure (Coord (d ^ 2 - 1))) (P : Protocol d k)
    (F : Fin (d ^ 2 - 1) → Op d) (ρstar : Op d) : Measure (Coord (d ^ 2 - 1) × P.History) :=
  μ ⊗ₘ (P.law.comap (fun θ => ρstar + herm0Coord F θ) (measurable_translate F ρstar))

end LimitedEntanglementTomography.LowerBound


