-- Prove2me | Definitions.Def_GaussMixHH_CenterModel
-- name    : GaussMixHH_CenterModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:54.261378+00:00
-- url     : https://prove2.me/theorems/100572c7-5b4d-4439-b422-74a72c69feef
-- title:
--   Separated center distributions, the mixture $\mathrm{Mix}(D,1)$, the radial law $\rho_z$ and the estimator's inputs
-- statement:
--   A **center distribution** is a probability measure $D$ on $\mathbb R^n$. Its support $\mathrm{Supp}$ is the set of its positive-weight atoms, $D(\mu)=D(\{\mu\})$, and $D$ is **$\Delta$-separated and purely atomic** if
--
--   1. $D(\mathrm{Supp}^{\mathrm c})=0$, and
--   2. $\|\mu-\mu'\|\ge\Delta$ for all distinct $\mu,\mu'\in\mathrm{Supp}$ (the Separation Assumption).
--
--   $\mathrm{Supp}$ may be finite of any size or infinite. The homogeneous mixture $D'=\mathrm{Mix}(D,1)=D*N(0,I_n)$ draws $\mu\sim D$ and outputs $\mu+Z$ with $Z\sim N(0,I_n)$ independent. The **radial law** $\rho_z$ is the law of $\|\mu-z\|$ for $\mu\sim D$.
--
--   A run of the estimator uses the probability space $\Omega_n=\{0,1\}^{\mathbb N}\times(\mathbb R^n)^{\mathbb N}$ with the product of the fair-coin tape and i.i.d. samples from $D'$.
--
--   Inputs: for Theorem 1, pointer $p_0=n$ and memory $(\varepsilon_{wt},\varepsilon_{dist},\Delta_{\min},z_1,\dots,z_n)$ from cell $0$; for Theorem 20, pointer $p_0=n$ and memory $(R,\eta,\zeta,z_1,\dots,z_n)$.
--
--   **Formalization Note** The input layouts are a reading (the paper names none). The mixture is Mathlib's additive convolution with `stdGaussian`.
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), §1, pp.2–4 (PDF pp.4–6): model, Separation Assumption, Mix(D, r), (EP); §2.1, p.9

import Mathlib
import Definitions.Def_GaussMixHH_Machine

open MeasureTheory ProbabilityTheory

namespace GaussMixHH

/-!
# Separated center distributions, the mixture `Mix(D, 1)` and the inputs of the estimator

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), §1, pp.2–4 (PDF pp.4–6): the
model, the Separation Assumption, `D′ = Mix(D, r)` with `r ≡ 1`, and (EP); §2.1, p.9, the radial
distribution `ρ` of `∥μ − z∥`; Theorem 20, p.25, its input.

**Formalization Note.**
* A center distribution is a probability measure `D` on `ℝⁿ`. Its support `Supp D` is the set of
  its positive-weight atoms, and `D(μ)` is `D{μ}`. `IsSeparatedAtomic Δ D` says that `D` is purely
  atomic (`D((Supp D)ᶜ) = 0`) and that distinct atoms are at distance at least `Δ`. `Supp D` may
  be infinite (it is countable).
* `mixture D = D ∗ N(0, I_n)`: draw `μ ∼ D`, output `μ + Z` with `Z ∼ N(0, I_n)` independent;
  this is `Mix(D, 1)`.
* `radialLaw D z` is the law of `∥μ − z∥` for `μ ∼ D`, a probability measure on `ℝ`.
* The randomness of a run is `Ω n = (ℕ → Bool) × (ℕ → ℝⁿ)` with the product of the fair-coin tape
  and i.i.d. samples from the mixture (`sampleSpace D`).
* Input layouts are a reading (the paper names none). Theorem 1: pointer `0` holds `n`; memory
  cells `0, 1, 2` hold `εwt, εdist, ∆min`, cells `3, …, n + 2` hold `z`. Theorem 20: cells `0, 1, 2`
  hold `R, η, ζ`, cells `3, …, n + 2` hold `z`. The output is `r[0]` at `halt`.
-/

/-- The support of a center distribution: its positive-weight atoms. -/
def Supp {n : ℕ} (D : Measure (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {μ | 0 < D {μ}}

/-- `D` is purely atomic and its atoms are pairwise at distance at least `Δ`
(the Separation Assumption, p.2). -/
def IsSeparatedAtomic {n : ℕ} (Δ : ℝ) (D : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  D (Supp D)ᶜ = 0 ∧ ∀ μ ∈ Supp D, ∀ μ' ∈ Supp D, μ ≠ μ' → Δ ≤ dist μ μ'

/-- The homogeneous mixture `Mix(D, 1) = D ∗ N(0, I_n)`. -/
noncomputable def mixture {n : ℕ} (D : Measure (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  D ∗ stdGaussian (EuclideanSpace ℝ (Fin n))

/-- The radial distribution `ρ_z`: the law of `∥μ − z∥` for `μ ∼ D`. -/
noncomputable def radialLaw {n : ℕ} (D : Measure (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : Measure ℝ :=
  D.map (fun μ => dist μ z)

/-- The probability space of a run: fair coins times i.i.d. samples from `Mix(D, 1)`. -/
noncomputable def sampleSpace {n : ℕ} (D : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure D] : Measure ((ℕ → Bool) × (ℕ → EuclideanSpace ℝ (Fin n))) :=
  coinTape.prod (Measure.infinitePi (fun _ : ℕ => mixture D))

/-- The input of Theorem 1: `n` in pointer `0`; `εwt, εdist, ∆min, z₀, …, z_{n−1}` in memory. -/
noncomputable def goalInput (n : ℕ) (εwt εdist Δmin : ℝ) (z : EuclideanSpace ℝ (Fin n)) : State :=
  initState n ([εwt, εdist, Δmin] ++ List.ofFn (fun i : Fin n => z i))

/-- The input of Theorem 20: `n` in pointer `0`; `R, η, ζ, z₀, …, z_{n−1}` in memory. -/
noncomputable def theorem20Input (n : ℕ) (R η ζ : ℝ) (z : EuclideanSpace ℝ (Fin n)) : State :=
  initState n ([R, η, ζ] ++ List.ofFn (fun i : Fin n => z i))

end GaussMixHH


