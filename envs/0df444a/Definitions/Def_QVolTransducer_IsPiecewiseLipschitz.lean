-- Prove2me | Definitions.Def_QVolTransducer_IsPiecewiseLipschitz
-- name    : QVolTransducer_IsPiecewiseLipschitz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:11.388452+00:00
-- url     : https://prove2.me/theorems/eed232af-aec3-4ec6-ae44-c9fe47bdf074
-- title:
--   Jordan-measurable sets, $h$-smooth partitions and piecewise $L$-Lipschitz functions
-- statement:
--   A set $\Omega\subseteq\mathbb R^d$ is **Jordan-measurable** if it is bounded and its boundary has Lebesgue measure zero.
--
--   Let $\Omega$ be Jordan-measurable and $\Omega=\Omega_1\sqcup\dots\sqcup\Omega_n$ a finite partition into Jordan-measurable sets. The partition is **$h$-smooth** if $h:\mathbb R_{>0}\to\mathbb R_{>0}$ is continuous with $h(\zeta)\downarrow0$ as $\zeta\downarrow0$ and, for all $\zeta>0$,
--
--   $$
--   \sum_{j=1}^n\mathrm{Vol}\bigl(\{x\in\mathbb R^d:\ \mathrm{dist}(x,\partial\Omega_j)<\zeta\}\bigr)<h(\zeta).
--   $$
--
--   A function $f$ on $\Omega$ is **piecewise $L$-Lipschitz on the $h$-smooth partition** $(\Omega_j)$ if $L>0$ and $|f(x)-f(y)|\le L\|x-y\|$ whenever $x,y$ lie in the same piece $\Omega_j$.
--
--   These conditions make Riemann sums over fine grids converge to integrals (Lemma 7.5), which is how the discretized statements of the paper relate to the continuous distributions.
--
--   **Formalization Note** The set $\{x:\mathrm{dist}(x,\partial\Omega_j)<\zeta\}$ is the $\zeta$-thickening of the boundary, empty for an empty boundary. "$h(\zeta)\downarrow0$" is read as $h(\zeta)\to0$ as $\zeta\to0^+$. Functions are real-valued (the paper allows complex values; the mission applies the notion to real random variables).
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definitions 7.1 and 7.2, p.43 (PDF p.45)

import Mathlib

namespace QVolTransducer

open MeasureTheory Filter Topology

/-- Jordan-measurable sets (Cornelissen, Apers, Gribling, *Improved quantum volume estimation with
transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3, 2026, sha256
40d7b52d…), Definition 7.1, p.43: "A set Ω ⊆ ℝ^d is Jordan-measurable if it is bounded and its
boundary is a measure-zero set"). -/
def IsJordanMeasurable {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Bornology.IsBounded S ∧ volume (frontier S) = 0

/-- An `h`-smooth finite partition `Ω = Ω_1 ⊔ ⋯ ⊔ Ω_n` of a Jordan-measurable set
(arXiv:2609.40217, Definition 7.2, p.43): the pieces are pairwise disjoint, cover `Ω` and are
Jordan-measurable; `h : ℝ_{>0} → ℝ_{>0}` is continuous with `h(ζ) → 0` as `ζ ↓ 0`; and for all
`ζ > 0`, `Σ_j Vol({x ∈ ℝ^d : dist(x, ∂Ω_j) < ζ}) < h(ζ)`.

**Formalization Note** `{x : dist(x, ∂Ω_j) < ζ}` is `Metric.thickening ζ (frontier Ω_j)`, which is
empty when the boundary is empty (distance `+∞` to the empty set), so an empty piece contributes
`0`. `h` is a function on `ℝ`, constrained only on `ζ > 0`; "`h(ζ) ↓ 0` as `ζ ↓ 0`" is read as
`h(ζ) → 0` as `ζ → 0⁺`. The volumes are summed in `ℝ≥0∞`. -/
structure IsSmoothPartition {d n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (parts : Fin n → Set (EuclideanSpace ℝ (Fin d))) (h : ℝ → ℝ) : Prop where
  jordan_whole : IsJordanMeasurable Ω
  jordan : ∀ j, IsJordanMeasurable (parts j)
  disjoint : Pairwise fun i j => Disjoint (parts i) (parts j)
  cover : (⋃ j, parts j) = Ω
  h_cont : ContinuousOn h (Set.Ioi 0)
  h_pos : ∀ ζ : ℝ, 0 < ζ → 0 < h ζ
  h_lim : Tendsto h (𝓝[>] 0) (𝓝 0)
  boundary : ∀ ζ : ℝ, 0 < ζ →
    ∑ j, volume (Metric.thickening ζ (frontier (parts j))) < ENNReal.ofReal (h ζ)

/-- Piecewise `L`-Lipschitz-continuous functions on an `h`-smooth partition (arXiv:2609.40217,
Definition 7.2, p.43): `(Ω_j)_{j=1}^n` is an `h`-smooth partition of the Jordan-measurable set `Ω`,
`L > 0`, and `|f(x) − f(y)| ≤ L ‖x − y‖` for all `x, y` in the same piece `Ω_j`.

**Formalization Note** The paper allows `f : Ω → ℂ`; the statements of this mission apply the notion
to real random variables, so `f` is real-valued here, and it is a function on all of `ℝ^d` of which
only the values on `Ω` matter. -/
def IsPiecewiseLipschitz {d n : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (L : ℝ)
    (parts : Fin n → Set (EuclideanSpace ℝ (Fin d))) (h : ℝ → ℝ) : Prop :=
  IsSmoothPartition Ω parts h ∧ 0 < L ∧
    ∀ j, ∀ x ∈ parts j, ∀ y ∈ parts j, |f x - f y| ≤ L * ‖x - y‖

end QVolTransducer


