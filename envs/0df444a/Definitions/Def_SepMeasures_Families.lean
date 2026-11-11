-- Prove2me | Definitions.Def_SepMeasures_Families
-- name    : SepMeasures_Families
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:26.318211+00:00
-- url     : https://prove2.me/theorems/0a755380-f8b6-46af-932e-ac48ad233efd
-- title:
--   §2.1–2.2, pp.10–12 — atoms, $\mu_{na}$, affine general position, finite first moments and the families $\mathcal P^d_f\supseteq\mathcal P^d\supseteq\mathcal P^d_b\supseteq\mathcal P^d_{bc}$
-- statement:
--   Fix $d\ge1$ and a norm $\|\cdot\|$ on $\mathbb R^d$. For a measure $\mu$ on $\mathbb R^d$, $\mathrm{Atom}(\mu)=\{x:\mu(\{x\})>0\}$ is its set of atoms and
--   $$\mu_{na}=\mu-\sum_{x\in\mathrm{Atom}(\mu)}\mu(\{x\})\,\delta_x$$
--   its non-atomic part. A set $S\subseteq\mathbb R^d$ is in **affine general position** if every subset of at most $d+1$ points of $S$ is affinely independent. A measure has a **finite first moment** if $\int\|x\|\,d\mu(x)<\infty$.
--
--   The families of pairs of measures are:
--   1. $\mathcal P^d_f$: pairs $(\mu,\nu)$ of probability measures with finite first moments;
--   2. $\mathcal P^d\subseteq\mathcal P^d_f$: those pairs with (i) $\mathrm{Atom}(\mu)\cap\mathrm{Atom}(\nu)=\emptyset$ and $\mathrm{Atom}(\mu)\cup\mathrm{Atom}(\nu)$ in affine general position, and (ii) $\mu_{na}(H)=\nu_{na}(H)=0$ for every affine hyperplane $H$;
--   3. $\mathcal P^d_b\subseteq\mathcal P^d$: those pairs in which both measures have bounded support;
--   4. $\mathcal P^d_{bc}\subseteq\mathcal P^d_b$: those pairs in which both measures are absolutely continuous with respect to Lebesgue measure.
--
--   $\mathcal P^d$ is the main family of the paper; the goal theorem is a bound on its cut ratio, and the reduction lemmas pass from $\mathcal P^d$ to $\mathcal P^d_b$ and $\mathcal P^d_{bc}$.
--
--   **Formalization Note** $\mu_{na}$ is the restriction of $\mu$ to the complement of its atom set (equal to the printed formula because the atom set of a finite measure is countable). Affine general position is required of every finite subset of at most $d+1$ points, so it applies to infinite atom sets. First moments are measured with the norm $N$ as lower Lebesgue integrals. Bounded support means both measures vanish outside some closed Euclidean ball around the origin.
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), §2.1, pp.10–11 (Atom(µ), µ_na, 𝒫^d_f, affine general position, 𝒫^d with conditions (i), (ii)); Definition 2.2, p.12 (𝒫^d_b, 𝒫^d_bc); footnote 3, p.5

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- The atom set `Atom(μ) = {x | μ({x}) > 0}` (Correa et al., manuscript sha256 96a86924…fa82f,
§2.1, p.10). -/
def atoms {d : ℕ} (μ : Measure (E d)) : Set (E d) := {x | μ {x} ≠ 0}

/-- The non-atomic part `μ_na := μ − Σ_{x ∈ Atom(μ)} μ({x}) δ_x` (§2.1, p.10).

**Formalization Note.** Encoded as the restriction of `μ` to the complement of its atom set. For
a finite measure the atom set is countable, so the restriction to `Atom(μ)` is
`Σ_{x ∈ Atom(μ)} μ({x}) δ_x` and the two definitions of `μ_na` agree. -/
noncomputable def nonatomic {d : ℕ} (μ : Measure (E d)) : Measure (E d) :=
  μ.restrict (atoms μ)ᶜ

/-- A set of points of `ℝ^d` is in **affine general position** if every subset of at most
`d + 1` points is affinely independent (§2.1, p.11; footnote 3, p.5).

**Formalization Note.** Stated for every finite subset `t ⊆ S` with `|t| ≤ d + 1`, so it also
applies to countably infinite atom sets. -/
def AffGenPos (d : ℕ) (S : Set (E d)) : Prop :=
  ∀ t : Finset (E d), (↑t : Set (E d)) ⊆ S → t.card ≤ d + 1 →
    AffineIndependent ℝ ((↑) : (↑t : Set (E d)) → E d)

/-- Finite first moment `∫ ‖x‖ dμ(x) < ∞`, measured with the norm `N` (§2.1, p.11).

**Formalization Note.** A lower Lebesgue integral in `ℝ≥0∞`, so no integrability side
condition is involved. In finite dimension the condition does not depend on the norm (p.11). -/
def FiniteFirstMoment {d : ℕ} (N : Seminorm ℝ (E d)) (μ : Measure (E d)) : Prop :=
  ∫⁻ x, ENNReal.ofReal (N x) ∂μ < ⊤

/-- `𝒫^d_f`: the pairs `(μ, ν)` of probability measures on `ℝ^d` with finite first moments
(§2.1, p.11). -/
def Pf (d : ℕ) (N : Seminorm ℝ (E d)) : Set (Measure (E d) × Measure (E d)) :=
  {p | IsProbabilityMeasure p.1 ∧ IsProbabilityMeasure p.2 ∧
    FiniteFirstMoment N p.1 ∧ FiniteFirstMoment N p.2}

/-- `𝒫^d ⊆ 𝒫^d_f`: the pairs satisfying (i) the atom sets are disjoint and
`Atom(μ) ∪ Atom(ν)` is in affine general position, and (ii) for every affine hyperplane `H`,
`μ_na(H) = ν_na(H) = 0` (§2.1, p.11). -/
def P (d : ℕ) (N : Seminorm ℝ (E d)) : Set (Measure (E d) × Measure (E d)) :=
  {p | p ∈ Pf d N ∧ Disjoint (atoms p.1) (atoms p.2) ∧ AffGenPos d (atoms p.1 ∪ atoms p.2) ∧
    ∀ H : Hyp d, nonatomic p.1 H.set = 0 ∧ nonatomic p.2 H.set = 0}

/-- `𝒫^d_b`: the pairs in `𝒫^d` for which both measures have bounded support
(Definition 2.2, p.12).

**Formalization Note.** "Bounded support" is: both measures vanish outside some closed
Euclidean ball centred at the origin. -/
def Pb (d : ℕ) (N : Seminorm ℝ (E d)) : Set (Measure (E d) × Measure (E d)) :=
  {p | p ∈ P d N ∧ ∃ R : ℝ, p.1 (Metric.closedBall 0 R)ᶜ = 0 ∧ p.2 (Metric.closedBall 0 R)ᶜ = 0}

/-- `𝒫^d_bc ⊆ 𝒫^d_b`: the pairs for which both measures are absolutely continuous with respect
to Lebesgue measure (Definition 2.2, p.12). -/
def Pbc (d : ℕ) (N : Seminorm ℝ (E d)) : Set (Measure (E d) × Measure (E d)) :=
  {p | p ∈ Pb d N ∧ p.1 ≪ volume ∧ p.2 ≪ volume}

end SepMeasures


