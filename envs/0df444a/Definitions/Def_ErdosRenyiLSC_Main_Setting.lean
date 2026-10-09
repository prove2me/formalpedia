-- Prove2me | Definitions.Def_ErdosRenyiLSC_Main_Setting
-- name    : ErdosRenyiLSC_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:57.101451+00:00
-- url     : https://prove2.me/theorems/099b838e-4456-4050-bfff-3780d6377a94
-- title:
--   Sparse symmetric ensemble, semicircle transform, and resolvents
-- statement:
--   This module fixes the random-matrix model and spectral notation of Section 2. The centered real symmetric matrix $H_N$ has independent upper-triangular entries, mean zero, variance $1/N$, and the moment bound
--
--   $$\mathbf E|h_{ij}|^p\le \frac{C^p}{Nq_N^{p-2}},\qquad 3\le p\le(\log N)^{A_0\log\log N}.$$
--
--   The parameters obey $1+a_0\le\xi_N\le A_0\log\log N$ and $(\log N)^{3\xi_N}\le q_N\le C\sqrt N$. The deterministic deformation is $A_N=H_N+f_N|e_N\rangle\langle e_N|$, where $e_N=N^{-1/2}(1,\ldots,1)$ and the projection has entries $1/N$. The semicircle density is $\rho_{\mathrm{sc}}(x)=(2\pi)^{-1}\sqrt{[4-x^2]_+}$, and $m_{\mathrm{sc}}(z)$ is its Stieltjes integral. The complex resolvent and its normalized trace use $(M-zI)^{-1}$ and $N^{-1}\operatorname{Tr}(M-zI)^{-1}$.
--
--   These definitions supply the common model for the local laws and their intermediate estimates.
--
--   **Formalization Note** The conditions on $N$ hold eventually, because the displayed lower bound for $\xi_N$ is impossible at small $N$. Integrability accompanies every finite expectation, moment order $p$ is real, and the high-probability predicate uses the measure of arbitrary events so one event may contain an intersection over all spectral parameters.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, pp. 5–8, Definitions 2.1, 2.2, 2.6 and (2.2), (2.10)–(2.14)

import Mathlib

noncomputable section
open ProbabilityTheory

namespace ErdosRenyiLSC.Main

/-- The independent upper-triangular entries of a real symmetric matrix sequence. -/
structure SymmetricIndependentEnsemble {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ) : Prop where
  measurable : ∀ᶠ N in (Filter.atTop : Filter ℕ),
    ∀ (i j : Fin N), Measurable (fun ω => H N ω i j)
  symmetric : ∀ᶠ N in (Filter.atTop : Filter ℕ),
    ∀ ω (i j : Fin N), H N ω i j = H N ω j i
  independent : ∀ᶠ N in (Filter.atTop : Filter ℕ),
    iIndepFun (fun p : {p : Fin N × Fin N // p.1 ≤ p.2} =>
      fun ω => H N ω p.1.1 p.1.2) P

/-- Definition 2.1 and the eventual parameter conditions (2.4), (2.6). -/
structure IsSparseEnsemble {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
    (ξ q : ℕ → ℝ) (a₀ A₀ C : ℝ) : Prop where
  base : SymmetricIndependentEnsemble P H
  xi_bounds : ∀ᶠ N in (Filter.atTop : Filter ℕ),
    1 + a₀ ≤ ξ N ∧ ξ N ≤ A₀ * Real.log (Real.log (N : ℝ))
  q_bounds : ∀ᶠ N in (Filter.atTop : Filter ℕ),
    q N ≥ Real.log (N : ℝ) ^ (3 * ξ N) ∧ q N ≤ C * Real.sqrt (N : ℝ)
  mean_integrable : ∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ (i j : Fin N),
    MeasureTheory.Integrable (fun ω => H N ω i j) P
  mean_zero : ∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ (i j : Fin N),
    ∫ ω, H N ω i j ∂P = (0 : ℝ)
  variance_integrable : ∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ (i j : Fin N),
    MeasureTheory.Integrable (fun ω => (H N ω i j) ^ 2) P
  variance : ∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ (i j : Fin N),
    ∫ ω, (H N ω i j) ^ 2 ∂P = (1 : ℝ) / (N : ℝ)
  moment_integrable : ∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ (i j : Fin N) (p : ℝ),
    3 ≤ p → p ≤ Real.log (N : ℝ) ^ (A₀ * Real.log (Real.log (N : ℝ))) →
    MeasureTheory.Integrable (fun ω => |H N ω i j| ^ p) P
  moments : ∀ᶠ N in (Filter.atTop : Filter ℕ), ∀ (i j : Fin N) (p : ℝ),
    3 ≤ p → p ≤ Real.log (N : ℝ) ^ (A₀ * Real.log (Real.log (N : ℝ))) →
    ∫ ω, |H N ω i j| ^ p ∂P ≤ C ^ p / ((N : ℝ) * q N ^ (p - 2))

/-- The constant unit vector of (2.2), in zero-based coordinates. -/
def eVec (N : ℕ) : Fin N → ℝ := fun _ => 1 / Real.sqrt (N : ℝ)

/-- The rank-one projection `|e⟩⟨e|` of (2.7), with entries `1/N`. -/
def proj (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun _ _ => 1 / (N : ℝ)

/-- The noncentered matrix `A = H + f|e⟩⟨e|`. -/
def deformedMatrix {Ω : Type*}
    (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
    (f : ℕ → ℝ) (N : ℕ) (ω : Ω) : Matrix (Fin N) (Fin N) ℝ :=
  H N ω + f N • proj N

/-- Definition 2.6: high probability, using the measure of an arbitrary event. -/
def HighProb {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ξ : ℕ → ℝ) (ν : ℝ) (E : ℕ → Set Ω) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    P (E N)ᶜ ≤ ENNReal.ofReal (Real.exp (-ν * Real.log (N : ℝ) ^ ξ N))

/-- The spectral domain `D` of (2.10). -/
def domD (Sigma : ℝ) : Set ℂ :=
  {z | |z.re| ≤ Sigma ∧ 0 < z.im ∧ z.im ≤ 3}

/-- The smaller domain `D_L` of (3.1). -/
def domDL (Sigma : ℝ) (L : ℕ → ℝ) (N : ℕ) : Set ℂ :=
  {z | |z.re| ≤ Sigma ∧ Real.log (N : ℝ) ^ L N / (N : ℝ) ≤ z.im ∧ z.im ≤ 3}

/-- The semicircle density (2.11); `Real.sqrt` implements the positive part. -/
def rhoSc (x : ℝ) : ℝ :=
  1 / (2 * Real.pi) * Real.sqrt (4 - x ^ 2)

/-- The Stieltjes transform (2.12), defined by the integral rather than a square-root branch. -/
def msc (z : ℂ) : ℂ :=
  ∫ x : ℝ, (rhoSc x : ℂ) / ((x : ℂ) - z)

/-- Distance from the real part to the nearest spectral edge, (2.14). -/
def kappa (x : ℝ) : ℝ := |(|x| - 2)|

/-- The complex resolvent of a real matrix. -/
def resolvent {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (M.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- The normalized trace of the resolvent. -/
def stieltjes {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ :=
  ((1 : ℂ) / (N : ℂ)) * Matrix.trace (resolvent M z)

end ErdosRenyiLSC.Main


