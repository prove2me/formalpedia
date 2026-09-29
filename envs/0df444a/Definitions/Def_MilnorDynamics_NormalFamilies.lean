-- Prove2me | Definitions.Def_MilnorDynamics_NormalFamilies
-- name    : MilnorDynamics_NormalFamilies
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T10:38:27.330455+00:00
-- url     : https://prove2.me/theorems/1269e191-44f6-42f6-95cc-a85537c7a0ad
-- title:
--   Riemann sphere, chordal metric, holomorphic maps and normal families (Milnor §3)
-- statement:
--   Basic objects of Milnor's §3 (*Normal Families: Montel's Theorem*), specialised to maps whose source is an open subset $U$ of the complex plane.
--
--   1. **The Riemann sphere** $\hat{\mathbb C}=\mathbb C\cup\{\infty\}$ (the one-point compactification of $\mathbb C$) with its two standard coordinates: $\zeta\mapsto\zeta$ near finite points and $\zeta\mapsto 1/\zeta$ near points other than $0$.
--   2. **The chordal metric** on $\hat{\mathbb C}$:
--   $$
--   \sigma(z,w)=\frac{2|z-w|}{\sqrt{1+|z|^2}\,\sqrt{1+|w|^2}},\qquad \sigma(z,\infty)=\sigma(\infty,z)=\frac{2}{\sqrt{1+|z|^2}},\qquad \sigma(\infty,\infty)=0 .
--   $$
--   3. **Holomorphic maps** $f:U\to\hat{\mathbb C}$: continuous maps that are complex differentiable when read in the two coordinates of the sphere.
--   4. **Locally uniform convergence** (Milnor, Lemma 3.1(a)) of maps $U\to\hat{\mathbb C}$: uniform convergence in the metric $\sigma$ on every compact $K\subseteq U$.
--   5. **Normal families with compact target** (Milnor, p. 33): a family $\mathcal F$ of maps $U\to\hat{\mathbb C}$ is normal if every sequence in $\mathcal F$ has a subsequence converging locally uniformly to some continuous $g:U\to\hat{\mathbb C}$.
--   6. **Locally uniform divergence** from a set $V\subseteq\mathbb C$ (p. 33): $f_n(K)\cap K'=\emptyset$ for all large $n$, for all compact $K\subseteq U$ and $K'\subseteq V$.
--   7. **Normal families with noncompact target** $V\subseteq\mathbb C$ (Definition, p. 33): every sequence has a subsequence that either converges locally uniformly to a continuous $g:U\to V$, or diverges locally uniformly from $V$.
--
--   These are the notions in which the goal (Theorem 3.7) and all milestones of the mission are stated.
--
--   **Formalization Note** The sphere is Mathlib's `OnePoint ℂ`. The chart functions carry junk values ($\infty\mapsto 0$, and $0\mapsto 0$ for the coordinate $1/\zeta$) that are only ever evaluated near points where the corresponding coordinate is genuine. For maps into a subset $V\subseteq\mathbb C$, locally uniform convergence is Mathlib's `TendstoLocallyUniformlyOn` for the Euclidean metric, which is equivalent to Milnor's definition by Lemma 3.1 (the topology does not depend on the choice of metric, and on compacta of $V$ the Euclidean and any compatible metric are uniformly equivalent).
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, pp. 30–33 (Definition of the topology of locally uniform convergence, Lemma 3.1, Definitions of normal families and of locally uniform divergence); Riemann sphere and its charts: §1

import Mathlib

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- Affine coordinate of the Riemann sphere near finite points: `z ↦ z`, with the junk value
`∞ ↦ 0` (only ever used near points where the value is finite). -/
def chartFinite : OnePoint ℂ → ℂ
  | some z => z
  | none => 0

/-- Coordinate of the Riemann sphere near `∞`: `z ↦ z⁻¹`, `∞ ↦ 0` (so `0 ↦ 0` is a junk value;
it is only ever used near points where the value is different from `0`). -/
noncomputable def chartInfinite : OnePoint ℂ → ℂ
  | some z => z⁻¹
  | none => 0

/-- The chordal (spherical) metric on the Riemann sphere `ℂ ∪ {∞}`: the Euclidean distance
between the images on the unit sphere of `ℝ³` under inverse stereographic projection. -/
noncomputable def chordalDist : OnePoint ℂ → OnePoint ℂ → ℝ
  | some z, some w => 2 * ‖z - w‖ / (Real.sqrt (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖w‖ ^ 2))
  | some z, none => 2 / Real.sqrt (1 + ‖z‖ ^ 2)
  | none, some w => 2 / Real.sqrt (1 + ‖w‖ ^ 2)
  | none, none => 0

/-- `f : ℂ → ℂ ∪ {∞}` is a holomorphic map from the open set `U` to the Riemann sphere:
it is continuous on `U`, and in the two standard coordinate charts of the sphere
(`z` near finite values, `1/z` near values different from `0`) it is complex differentiable. -/
def IsHolomorphicOn (U : Set ℂ) (f : ℂ → OnePoint ℂ) : Prop :=
  ContinuousOn f U ∧
  (∀ z ∈ U, f z ≠ ∞ → DifferentiableAt ℂ (fun w => chartFinite (f w)) z) ∧
  (∀ z ∈ U, f z ≠ ((0 : ℂ) : OnePoint ℂ) → DifferentiableAt ℂ (fun w => chartInfinite (f w)) z)

/-- Locally uniform convergence on `U` of maps into the Riemann sphere, with respect to the
chordal metric: uniform convergence on every compact subset of `U`. -/
def TendstoLocallyUniformlyOnSphere (F : ℕ → ℂ → OnePoint ℂ) (g : ℂ → OnePoint ℂ)
    (U : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ K, chordalDist (F n x) (g x) < ε

/-- A family `𝓕` of maps from `U` to the (compact) Riemann sphere is *normal* on `U` if every
sequence in `𝓕` has a subsequence converging locally uniformly on `U` (chordal metric) to some
continuous map `g : U → ℂ ∪ {∞}`. -/
def IsNormalFamily (U : Set ℂ) (𝓕 : Set (ℂ → OnePoint ℂ)) : Prop :=
  ∀ f : ℕ → ℂ → OnePoint ℂ, (∀ n, f n ∈ 𝓕) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → OnePoint ℂ,
      ContinuousOn g U ∧ TendstoLocallyUniformlyOnSphere (fun n => f (φ n)) g U

/-- A sequence of maps `f n : U → V` *diverges locally uniformly from `V`* if for all compact
`K ⊆ U` and `K' ⊆ V` we have `f n (K) ∩ K' = ∅` for all sufficiently large `n`. -/
def DivergesLocallyUniformlyFrom (f : ℕ → ℂ → ℂ) (U V : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∀ K' ⊆ V, IsCompact K' → ∀ᶠ n in atTop, ∀ x ∈ K, f n x ∉ K'

/-- A family `𝓕` of maps from `U` into the (possibly noncompact) set `V ⊆ ℂ` is *normal* if
every sequence in `𝓕` has either a subsequence converging locally uniformly on `U` to a
continuous map `g : U → V`, or a subsequence diverging locally uniformly from `V`. -/
def IsNormalFamilyInto (U V : Set ℂ) (𝓕 : Set (ℂ → ℂ)) : Prop :=
  ∀ f : ℕ → ℂ → ℂ, (∀ n, f n ∈ 𝓕) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ g : ℂ → ℂ, ContinuousOn g U ∧ MapsTo g U V ∧
          TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U) ∨
        DivergesLocallyUniformlyFrom (fun n => f (φ n)) U V)

end MilnorDynamics


