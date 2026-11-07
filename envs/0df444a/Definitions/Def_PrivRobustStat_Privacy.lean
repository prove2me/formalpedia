-- Prove2me | Definitions.Def_PrivRobustStat_Privacy
-- name    : PrivRobustStat_Privacy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:27.240399+00:00
-- url     : https://prove2.me/theorems/5e3e3515-9836-46f8-a8d3-67adabf8fa63
-- title:
--   $(\varepsilon,\delta)$-DP, Rényi divergence, $(\lambda,\rho)$-RDP, public weight functions, Gaussian noise
-- statement:
--   Datasets have a fixed public size $n$; two datasets are **neighbouring** if they differ in one data point (the published `PrivLearn.Generic.Neighbors`). A mechanism $M$, given by the law $M(D)$ of its output on each dataset $D$, is **$(\varepsilon,\delta)$-differentially private** if for all neighbouring $D,D'$ and measurable events $E$
--
--   $$\Pr[M(D)\in E]\le e^{\varepsilon}\Pr[M(D')\in E]+\delta .$$
--
--   For $\lambda>1$ the **Rényi divergence** (the published `PADMPriv.renyiDiv`) is
--
--   $$D_\lambda(P\|Q)=\frac1{\lambda-1}\log\int\Big(\frac{dP}{dQ}\Big)^{\lambda}dQ\quad(P\ll Q),\qquad D_\lambda(P\|Q)=+\infty\ \text{otherwise},$$
--
--   and $M$ is **$(\lambda,\rho)$-RDP** on a class $S$ of datasets if $D_\lambda(M(D)\|M(D'))\le\lambda\rho$ for all neighbouring $D,D'\in S$ (Definition 3 with footnote 5: the bound is $\lambda\rho$, not $\rho$).
--
--   **Property 1** (sample signature filtering) is encoded by public **weight functions** $f_i:\mathbb R^d\to[0,\tfrac1n]$, fixed before the data: the weights are $w_i=f_i(x_i)$. All Gaussian draws are coordinates of a vector of independent $\mathcal N(0,1)$ variables; the module also defines the inner probability $\sup\{\mu(E): E\subseteq S\text{ measurable}\}$ of a possibly non-measurable event.
--
--   **Formalization Note** Rényi divergence is extended-real valued and computed with reference measure $Q$, which agrees with the paper's density formula for every common reference measure when $\lambda>1$. Every privacy statement of the mission also asserts that the output map is measurable, because the pushforward of a non-measurable map is $0$ in Lean.
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), DP, p.12; Definition 3 and footnote 5, pp.12–13; Property 1, p.13

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PADMPriv_renyiDiv

open MeasureTheory ProbabilityTheory

namespace PrivRobustStat

/-!
# Differential privacy, Rényi divergence, Rényi DP, and the noise measures

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…), §2.2 "Privacy", p.12, Definition 3 and footnote 5, pp.12–13,
Property 1, p.13.

**Formalization Note.**
* A mechanism is given by the law `M D` of its output for each dataset `D : Fin n → X` of the fixed,
  public size `n`. Neighbouring datasets are the published `PrivLearn.Generic.Neighbors` ("differ in
  one data point", p.12).
* The Rényi divergence is the published `PADMPriv.renyiDiv` (e18ca8d8), computed with reference
  measure `Q`: `(λ − 1)⁻¹ · log ∫ (dP/dQ)^λ dQ` if `P ≪ Q`, and `+∞` otherwise; for `λ > 1` this is the
  paper's `D_λ(p‖q)` (Definition 3) for densities with respect to any common reference measure.
* RDP uses the paper's convention `D_λ ≤ λρ` (footnote 5), not Mironov's `D_λ ≤ ρ`.
* `IsRDPOn S` quantifies over neighbouring datasets that both satisfy `S`; this is how the paper's
  input conditions ((9), p.15; `z[n] ⊂ B(q, R₀)`, Algorithm 7) restrict the privacy claims of
  Lemmas 4 and 14 and Proposition 2. `IsApproxDP` is over all pairs of neighbouring datasets.
* A mechanism's law is the pushforward of its noise measure; every privacy statement of the mission
  also asserts that the output map is measurable, because `Measure.map` of a non-measurable map is
  `0`, under which both definitions hold vacuously.
-/

/-- `(ε, δ)`-differential privacy (p.12): for every pair of neighbouring datasets `D, D′` and every
measurable event `E` of the output space, `P[M(D) ∈ E] ≤ e^ε P[M(D′) ∈ E] + δ`. -/
def IsApproxDP {X O : Type*} [MeasurableSpace O] {n : ℕ} (M : (Fin n → X) → Measure O)
    (ε δ : ℝ) : Prop :=
  ∀ D D' : Fin n → X, PrivLearn.Generic.Neighbors D D' → ∀ E : Set O, MeasurableSet E →
    M D E ≤ ENNReal.ofReal (Real.exp ε) * M D' E + ENNReal.ofReal δ

/-- `(λ, ρ)`-Rényi differential privacy (Definition 3, pp.12–13, with footnote 5's convention) over
neighbouring datasets that both satisfy `S`: `D_λ(M(D)‖M(D′)) ≤ λρ`. -/
def IsRDPOn {X O : Type*} [MeasurableSpace O] {n : ℕ} (S : (Fin n → X) → Prop) (lam ρ : ℝ)
    (M : (Fin n → X) → Measure O) : Prop :=
  ∀ D D' : Fin n → X, S D → S D' → PrivLearn.Generic.Neighbors D D' →
    PADMPriv.renyiDiv lam (M D) (M D') ≤ ((lam * ρ : ℝ) : EReal)

/-- Public weight functions as in Property 1 (p.13): `f i : ℝ^d → [0, 1/n]` for each index `i`. A
mechanism "whose input weights satisfy Property 1" runs on `w_i := f i (x_i)`, with `f` fixed before
the dataset. -/
def IsWeightFn {Y : Type*} (n : ℕ) (f : Fin n → Y → ℝ) : Prop :=
  ∀ i y, 0 ≤ f i y ∧ f i y ≤ 1 / (n : ℝ)

/-- Independent standard Gaussians `N(0, 1)` indexed by `ι`. All Gaussian draws of Algorithms 2, 3,
4, 7 and 8 are scaled coordinates of one sample of this measure. -/
noncomputable def stdGauss (ι : Type) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι => gaussianReal 0 1)

/-- `PrivLearn.Generic.laplace s` is σ-finite (a structural fact, used to form finite products). -/
instance laplace_sigmaFinite (s : ℝ) : SigmaFinite (PrivLearn.Generic.laplace s) :=
  SigmaFinite.withDensity_ofReal _

/-- The inner probability of a possibly non-measurable event `S`: the supremum of `μ E` over
measurable `E ⊆ S`. A lower bound on it is a lower bound on the probability of a measurable
sub-event. -/
noncomputable def innerProb {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) :
    ENNReal :=
  ⨆ (E : Set Ω) (_ : MeasurableSet E ∧ E ⊆ S), μ E

end PrivRobustStat


