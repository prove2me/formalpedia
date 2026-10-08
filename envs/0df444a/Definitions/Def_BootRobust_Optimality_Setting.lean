-- Prove2me | Definitions.Def_BootRobust_Optimality_Setting
-- name    : BootRobust_Optimality_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:37.405172+00:00
-- url     : https://prove2.me/theorems/2c53717a-6ebd-459a-a787-f7058142fc73
-- title:
--   pp. 6–16 — support Ωₙ, 𝒟ₙ, bootstrap distance B (27), bootstrap law (14), distance functions (Def. 4), relative topology, disappointment set of (24)
-- statement:
--   This file fixes the objects of Proposition 1 of Bertsimas and Van Parys and of its proof (Appendix B.2).
--
--   **Support and distributions.** The distinct points of the training data form a finite set $\Omega_n$, written $\iota$ below. A distribution on it is a vector $D\in\mathbb R^{\iota}$ with $D_i\ge 0$ and $\sum_i D_i=1$; the set of all of them is the simplex $\mathcal D_n$.
--
--   **Bootstrap distance (27).** For $D,D'\in\mathcal D_n$,
--   $$B(D,D')=\sum_{i\in\iota} D_i\log\frac{D_i}{D'_i},$$
--   with $0\log 0=0$, and $B(D,D')=+\infty$ when some $D_i>0=D'_i$. It takes values in the extended reals.
--
--   **Bootstrap law (14) and empirical distribution.** $D_{\rm tr}^n$ is the law of $n$ independent draws from the training distribution $D_{\rm tr}$, i.e. the product measure on $\iota^n$. For a sample $\omega=(\omega_1,\dots,\omega_n)$ the empirical distribution $D_{{\rm bs}[n]}$ assigns to $i$ the frequency $\#\{m:\omega_m=i\}/n$.
--
--   **Distribution distance functions (Definition 4).** A function $R:\mathcal D_n\times\mathcal D_n\to(-\infty,+\infty]$ is a distribution distance function if
--   1. (discrimination) $R(D,D')\ge 0$ for all $D,D'\in\mathcal D_n$, and $R(D',D)=0$ if and only if $D'=D$;
--   2. (convexity) $D\mapsto R(D,D')$ is convex on $\mathcal D_n$ for every fixed $D'$, with the usual arithmetic of $+\infty$.
--
--   **Relative topology.** A set $\mathcal N\subseteq\mathcal D_n$ is open (in $\mathcal D_n$) if it is the trace on $\mathcal D_n$ of an open subset of $\mathbb R^{\iota}$. The interior ${\rm int}\,\mathcal C$ of a set $\mathcal C$ consists of the points of $\mathcal D_n$ having a neighbourhood whose trace on $\mathcal D_n$ lies in $\mathcal C$.
--
--   **Disappointment set.** For a loss $G:\iota\to\mathbb R$, write $\mathbb E_D[G]=\sum_i D_iG_i$. The disappointment set of the nominal formulation with cost estimator $D\mapsto\mathbb E_D[G]$, robustified as in (24) with the distance $R$ and radius $r$ around $D_{\rm tr}$, is
--   $$\mathcal R=\Big\{D\in\mathcal D_n:\ \mathbb E_D[G]>\sup_{D'\in\mathcal D_n,\ R(D',D_{\rm tr})\le r}\mathbb E_{D'}[G]\Big\}.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Only the support points enter: covariates, responses, neighbourhood weights and the covariate metric are abstracted away, and a loss is a function on support points. $B$ and $R$ are `EReal`-valued; the supremum in $\mathcal R$ is taken in `EReal` (the supremum of the empty set is $-\infty$). Openness and interior are relative to the simplex: an open subset of $\mathbb R^\iota$ cannot lie inside the simplex, so the absolute notions would make the statements vacuous.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, (14) p. 6; Definition 4 pp. 11–12; (24) p. 12; Definition 6, (27) p. 13; (31) and Proposition 1 p. 16; B.2 p. 27

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Optimality

open MeasureTheory

/-! Setting of Bertsimas and Van Parys, *Bootstrap robust prescriptive analytics*, arXiv:1711.09974v2,
for Proposition 1 (p. 16) and its proof (Appendix B.2, p. 27).

The empirical support `Ωₙ` of the training data is a finite type `ι`; a distribution on it is a vector
`D : ι → ℝ` in `stdSimplex ℝ ι` (the set `𝒟ₙ` of the paper). Covariates, responses and distances in the
covariate space never enter: only the support points do. -/

open Classical in

/-- The bootstrap law of a resample of size `n` (Eq. (14), p. 6): `n` independent draws from the
training distribution `Dtr`, i.e. the product measure `Dtrⁿ` on `Fin n → ι`. Only the first `n`
coordinates of the infinite bootstrap process `D^∞_tr` enter the event `D_bs[n] ∈ C`. -/
noncomputable def bootLaw {ι : Type*} [Fintype ι] [MeasurableSpace ι] (Dtr : ι → ℝ) (n : ℕ) :
    Measure (Fin n → ι) :=
  Measure.pi (fun _ : Fin n => ∑ i, ENNReal.ofReal (Dtr i) • Measure.dirac i)

/-- The empirical distribution `D_bs[n]` of a bootstrap sample `ω = (ω₀, …, ω_{n-1})`: the
frequency `#{m : ω m = i} / n` of each support point `i`. -/
noncomputable def empDist {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Fin n → ι) :
    ι → ℝ :=
  fun i => ((Finset.univ.filter fun m => ω m = i).card : ℝ) / n

/-- A distribution distance function (Definition 4, pp. 11–12) on `𝒟ₙ = stdSimplex ℝ ι`, valued in
`EReal` so that `B` (which is `+∞` off absolute continuity) is an instance:
(i) discrimination: `R(D, D') ≥ 0`, and `R(D', D) = 0` iff `D' = D`;
(ii) convexity: `R(·, D')` is convex for every fixed `D'` (written out in `EReal`, where
`0 * ⊤ = 0` and `θ * ⊤ = ⊤` for `θ > 0`). -/
structure IsDistributionDistance {ι : Type*} [Fintype ι] (R : (ι → ℝ) → (ι → ℝ) → EReal) : Prop where
  nonneg : ∀ D ∈ stdSimplex ℝ ι, ∀ D' ∈ stdSimplex ℝ ι, 0 ≤ R D D'
  eq_zero_iff : ∀ D ∈ stdSimplex ℝ ι, ∀ D' ∈ stdSimplex ℝ ι, R D' D = 0 ↔ D' = D
  convex : ∀ D' ∈ stdSimplex ℝ ι, ∀ D₁ ∈ stdSimplex ℝ ι, ∀ D₂ ∈ stdSimplex ℝ ι, ∀ θ : ℝ,
    0 ≤ θ → θ ≤ 1 →
      R (θ • D₁ + (1 - θ) • D₂) D' ≤ (θ : EReal) * R D₁ D' + ((1 - θ : ℝ) : EReal) * R D₂ D'

/-- `N` is open relative to `𝒟ₙ`: it is the trace on the simplex of an open set of `ℝ^ι`. This is
the paper's "open neighborhood `N ⊆ 𝒟ₙ`" (Proposition 1). -/
def relOpen {ι : Type*} [Fintype ι] (N : Set (ι → ℝ)) : Prop :=
  ∃ U : Set (ι → ℝ), IsOpen U ∧ N = U ∩ stdSimplex ℝ ι

/-- The interior of `C` relative to `𝒟ₙ` (the "int 𝒞" of Eq. (31), p. 16): the points `D` of the
simplex having an open neighbourhood `U` whose trace on the simplex lies in `C`. -/
def relInt {ι : Type*} [Fintype ι] (C : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {D | D ∈ stdSimplex ℝ ι ∧ ∃ U : Set (ι → ℝ), IsOpen U ∧ D ∈ U ∧ U ∩ stdSimplex ℝ ι ⊆ C}

/-- The disappointment set `ℛ = {D ∈ 𝒟ₙ : 𝔼_D[G] > sup_{D' ∈ 𝒟ₙ, R(D', D_tr) ≤ r} 𝔼_{D'}[G]}` of
the nominal formulation whose cost estimator is `D ↦ 𝔼_D[G] = ∑ i, D i * G i` (Proposition 1, p. 16,
and B.2, p. 27), robustified by Eq. (24) with the distance `R` and radius `r`. The supremum is taken
in `EReal` (the supremum of the empty set is `⊥ = -∞`). -/
noncomputable def linDisapp {ι : Type*} [Fintype ι] (R : (ι → ℝ) → (ι → ℝ) → EReal)
    (Dtr : ι → ℝ) (r : ℝ) (G : ι → ℝ) : Set (ι → ℝ) :=
  {D | D ∈ stdSimplex ℝ ι ∧
    (⨆ D' ∈ {D' : ι → ℝ | D' ∈ stdSimplex ℝ ι ∧ R D' Dtr ≤ (r : EReal)},
        ((∑ i, D' i * G i : ℝ) : EReal)) < ((∑ i, D i * G i : ℝ) : EReal)}

end BootRobust.Optimality


