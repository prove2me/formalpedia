-- Prove2me | Definitions.Def_LeblSCV_CR_IsSmoothOnSet
-- name    : LeblSCV_CR_IsSmoothOnSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:03:30.504994+00:00
-- url     : https://prove2.me/theorems/10cbbe5b-1645-4a25-853d-adc0f3c39d62
-- title:
--   Definition 3.2.1 — smooth and real-analytic functions on an arbitrary set
-- statement:
--   Let $X \subset \mathbb{C}^n \cong \mathbb{R}^{2n}$ be any set. A function $f : X \to \mathbb{C}$ is **smooth** (respectively **real-analytic**) if for each point $p \in X$ there are an open neighborhood $U$ of $p$ and a smooth (respectively real-analytic, Definition 3.1.1) function $F : U \to \mathbb{C}$ with
--   $$F(q) = f(q) \qquad \text{for all } q \in X \cap U.$$
--   This is how functions on a hypersurface, which is not an open set, are differentiated: through local extensions.
--
--   **Formalization Note.** $f$ is a function on all of $\mathbb{C}^n$ whose values off $X$ are irrelevant. `IsSmoothOnSet X f` is the smooth case (`ContDiffOn ℝ ∞ F U`) and `IsRealAnalyticOnSet X f` the real-analytic case (`IsRealAnalyticOn U F`); both are in this file. The book states the definition for $X \subset \mathbb{R}^n$; only $\mathbb{R}^{2n} \cong \mathbb{C}^n$ is used here. Neighborhoods are taken open.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 110, Definition 3.2.1

import Mathlib
import Definitions.Def_LeblSCV_CR_IsRealAnalyticOn

open scoped ContDiff

namespace LeblSCV.CR

/-- Definition 3.2.1 (Lebl, p. 110), smooth case, for `X ⊂ ℂⁿ ≅ ℝ^{2n}`: `f : X → ℂ` is smooth if
for each `p ∈ X` there is an open neighbourhood `U` of `p` and a smooth `F : U → ℂ` with
`F q = f q` for `q ∈ X ∩ U`. (`f` is an ambient function; only its values on `X` matter.) -/
def IsSmoothOnSet {n : ℕ} (X : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ p ∈ X, ∃ (U : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
    IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ q ∈ X ∩ U, F q = f q

/-- Definition 3.2.1 (Lebl, p. 110), real-analytic case: `f : X → ℂ` is real-analytic if for each
`p ∈ X` there is an open neighbourhood `U` of `p` and a real-analytic `F : U → ℂ` (Definition
3.1.1) with `F q = f q` for `q ∈ X ∩ U`. -/
def IsRealAnalyticOnSet {n : ℕ} (X : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ p ∈ X, ∃ (U : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
    p ∈ U ∧ IsRealAnalyticOn U F ∧ ∀ q ∈ X ∩ U, F q = f q

end LeblSCV.CR


