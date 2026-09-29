-- Prove2me | Definitions.Def_FCP_Kakeya
-- name    : FCP_Kakeya
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:04:51.711235+00:00
-- url     : https://prove2.me/theorems/ee5b0537-c94a-4256-8fd6-8e1c791a2f99
-- title:
--   Kakeya sets in $\mathbb{R}^n$ and over finite fields
-- statement:
--   A subset $S \subseteq \mathbb{R}^n$ is a **Kakeya set** if it contains a unit line segment in every direction: for every unit vector $v$ there is a point $a$ with the segment from $a$ to $a + v$ contained in $S$. Following the source, no compactness is imposed.
--
--   $\mathrm{KSC}(n)$ denotes the assertion that every Kakeya set in $\mathbb{R}^n$ has Hausdorff dimension exactly $n$.
--
--   The finite-field analogue: $S \subseteq \mathbb{F}^n$ is a Kakeya set if for every nonzero direction $v$ there is $a$ with the whole line $\{a + tv : t \in \mathbb{F}\}$ inside $S$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Kakeya.lean); https://en.wikipedia.org/wiki/Kakeya_set

import Mathlib

namespace FCP.Kakeya

open MeasureTheory Metric

/-- A set `S ⊆ ℝⁿ` is a Kakeya set if for every unit vector `v` it contains a translate of the
segment from `0` to `v`, i.e. a unit segment in the direction `v`. No compactness is assumed. -/
def IsKakeya {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → ∃ a, affineSegment ℝ a (a + v) ⊆ S

/-- The statement of the Kakeya set conjecture in dimension `n`: every Kakeya set in `ℝⁿ` has
Hausdorff dimension `n`. -/
def KakeyaSetConjectureDim (n : ℕ) : Prop :=
  ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsKakeya S → dimH S = n

/-- A finite-field Kakeya set: a subset of `Fⁿ` containing a full line in every nonzero
direction. -/
def IsKakeyaFinite {F : Type} [Field F] [Fintype F] {n : ℕ} (S : Finset (Fin n → F)) : Prop :=
  ∀ v : Fin n → F, v ≠ 0 → ∃ a : Fin n → F, ∀ t : F, a + t • v ∈ S

end FCP.Kakeya


