-- Prove2me | Definitions.Def_TensorPCAGlauber_OddK_Algorithm1
-- name    : TensorPCAGlauber_OddK_Algorithm1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:54:37.394268+00:00
-- url     : https://prove2.me/theorems/74f70cf2-0605-4aa5-9ba6-9040bb6ac9cd
-- title:
--   Algorithm 1 (annealed Glauber dynamics with ergodic averaging), its sample spaces, and top unit eigenvectors
-- statement:
--   Algorithm 1 takes a Hamiltonian $H$, an initial configuration $\tilde X_0$, inverse temperatures $\beta_0,\beta>0$ and times $T_{av},T>0$. Phase 1 runs continuous-time Glauber dynamics for $H$ at $\beta_0$ from $\tilde X_0$ up to time $T_{av}$ and computes the ergodic average
--   $$\bar X_{T_{av}}=\frac1{T_{av}}\int_0^{T_{av}}\tilde X_t\,dt;$$
--   phase 2 runs Glauber dynamics for $H$ at $\beta$ from $X_0=\mathrm{sgn}(\bar X_{T_{av}})$, and $(X_t)_{t\ge0}$ denotes its trajectory (the output is $X_T$). The algorithm uses only $H$, never $x^\star$. In the tensor PCA experiment the randomness is the Gaussian tensor $G'$, $\tilde X_0\sim\pi$ and the driving noise of the two phases, all independent. A top unit eigenvector of a matrix $M$ is a $v$ with $\|v\|=1$ and $Mv=\mu v$ for an eigenvalue $\mu$ at least every eigenvalue of $M$.
--
--   **Formalization Note.** `alg1Path V β₀ β Tav X̃₀ ω₁ ω₂ t` is the second-phase path; `algMeasure k N` is the product of `disorderMeasure`, `piMeasure`, and two copies of `noiseMeasure` on `AlgSpace k N`. `phase1Measure` (first phase alone) and `disorderNoiseMeasure` (one run in the model) are the analogous products.
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), p. 3 (PDF 6), Algorithm 1; p. 27 (PDF 30), Theorem 5.1; p. 37 (PDF 40), Theorem 6.1

import Mathlib
import Definitions.Def_TensorPCAGlauber_OddK_Hypercube
import Definitions.Def_TensorPCAGlauber_OddK_Model
import Definitions.Def_TensorPCAGlauber_OddK_Glauber

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- The trajectory `(X_t)_{t ≥ 0}` of the second phase of Algorithm 1 (Annealed Glauber Dynamics
with Ergodic Averaging, p. 3). Input: a Hamiltonian `V`, the initial configuration `X̃_0`, the
inverse temperatures `β₀, β` and the averaging time `T_av`. Phase 1 runs Glauber dynamics for `V`
at `β₀` from `X̃_0` with driving noise `ω₁` up to time `T_av`; the ergodic average
`X̄_{T_av} = T_av^{−1} ∫_0^{T_av} X̃_t dt` is rounded to `X_0 = sgn(X̄_{T_av})`; phase 2 runs
Glauber dynamics for `V` at `β` from `X_0` with independent driving noise `ω₂`. The algorithm sees
only `V` (never `x⋆`); the output `X_T` is this path at time `T`. -/
noncomputable def alg1Path {N : ℕ} (V : Cube N → ℝ) (β₀ β Tav : ℝ) (Xt₀ : Cube N)
    (ω₁ ω₂ : Noise N) (t : ℝ) : Cube N :=
  glauberPath V β (sgnCube (ergodicAvg V β₀ Xt₀ Tav ω₁)) ω₂ t

/-- The sample space of the tensor PCA experiment with Algorithm 1: the raw Gaussian tensor `G'`,
the initial configuration `X̃_0`, and the driving noise of the two phases. -/
abbrev AlgSpace (k N : ℕ) := KTensor k N × Cube N × Noise N × Noise N

/-- Its law: `G'` with i.i.d. `N(0,1)` entries, `X̃_0 ∼ π`, and the two driving noises, all
independent. -/
noncomputable def algMeasure (k N : ℕ) : Measure (AlgSpace k N) :=
  (disorderMeasure k N).prod ((piMeasure N).prod ((noiseMeasure N).prod (noiseMeasure N)))

/-- The sample space of one Glauber run in the tensor PCA model: the raw tensor `G'` and the
driving noise. -/
abbrev DisorderNoise (k N : ℕ) := KTensor k N × Noise N

/-- Its law: `G'` with i.i.d. `N(0,1)` entries, independent of the driving noise. -/
noncomputable def disorderNoiseMeasure (k N : ℕ) : Measure (DisorderNoise k N) :=
  (disorderMeasure k N).prod (noiseMeasure N)

/-- The sample space of the first phase alone (Theorem 5.1): `G'`, `X̃_0` and the driving noise. -/
abbrev Phase1Space (k N : ℕ) := KTensor k N × Cube N × Noise N

/-- Its law: `G'` with i.i.d. `N(0,1)` entries, `X̃_0 ∼ π` independent of `G'`, and the driving
noise, all independent. -/
noncomputable def phase1Measure (k N : ℕ) : Measure (Phase1Space k N) :=
  (disorderMeasure k N).prod ((piMeasure N).prod (noiseMeasure N))

/-- A unit vector `v` (`∑ v_i² = 1`) is a top unit eigenvector of the matrix `M`: `M v = μ v` for
an eigenvalue `μ` that is at least every eigenvalue of `M`. -/
def IsTopUnitEigenvector {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) : Prop :=
  ∑ i, v i ^ 2 = 1 ∧ ∃ μ : ℝ, M.mulVec v = μ • v ∧
    ∀ (μ' : ℝ) (w : Fin N → ℝ), w ≠ 0 → M.mulVec w = μ' • w → μ' ≤ μ

end TensorPCAGlauber.OddK


