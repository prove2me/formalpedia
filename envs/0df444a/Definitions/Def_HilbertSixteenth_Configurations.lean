-- Prove2me | Definitions.Def_HilbertSixteenth_Configurations
-- name    : HilbertSixteenth_Configurations
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T20:09:53.737477+00:00
-- url     : https://prove2.me/theorems/b6d8799c-7638-4461-8370-c474ca029895
-- title:
--   Topological configurations of limit cycles
-- statement:
--   1. A **simple closed curve** (Jordan curve) in $\mathbb R^2$ is the image of a continuous injective map from the circle $S^1$.
--   2. A **configuration of limit cycles** is a finite set $\mathcal C=\{C_1,\dots,C_n\}$ of pairwise disjoint simple closed curves.
--   3. The **bounded region limited by $C$** is the set of points not on $C$ whose connected component in $\mathbb R^2\setminus C$ is bounded.
--   4. A curve $C_i\in\mathcal C$ is **primary** if no other curve $C_j\in\mathcal C$ is contained in the bounded region limited by $C_i$.
--   5. Two families of curves $\mathcal C$, $\mathcal C'$ are **(topologically) equivalent** if there is a homeomorphism $h:\mathbb R^2\to\mathbb R^2$ with $h\big(\bigcup_i C_i\big)=\bigcup_j C'_j$.
--   6. A polynomial vector field **realises** $\mathcal C$ if the set of all its limit cycles is equivalent to $\mathcal C$.
--
--   These notions give the precise content of Problem 5 and of Theorem 1.
--
--   **Formalization Note** The circle is Mathlib's unit circle `Circle`. A configuration is a `Finset` of subsets of `ℝ × ℝ`. The equivalence is stated between the family of curves and the family of limit cycles through the unions of their members, exactly as in the source.
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554, §6 (Problem 5): configuration of limit cycles, primary curve, topological equivalence, realisation.

import Definitions.Def_HilbertSixteenth_PolyFields

/-!
# Topological configurations of limit cycles

Source: J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015),
no. 3, 543–554, §6 (Problem 5).
-/

namespace HilbertSixteenth

/-- `C` is a simple closed curve in the plane: the image of a continuous injective map from
the circle. -/
def IsJordanCurve (C : Set (ℝ × ℝ)) : Prop :=
  ∃ φ : Circle → ℝ × ℝ, Continuous φ ∧ Function.Injective φ ∧ Set.range φ = C

/-- A configuration of limit cycles: a finite set of pairwise disjoint simple closed curves. -/
def IsConfiguration (𝒞 : Finset (Set (ℝ × ℝ))) : Prop :=
  (∀ C ∈ 𝒞, IsJordanCurve C) ∧ (𝒞 : Set (Set (ℝ × ℝ))).PairwiseDisjoint id

/-- The bounded region limited by `C`: the points off `C` whose connected component in the
complement of `C` is bounded. -/
def boundedRegion (C : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | p ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ p)}

/-- A curve `C` of the configuration `𝒞` is primary if no other curve of `𝒞` is contained in
the bounded region limited by `C`. -/
def IsPrimary (𝒞 : Finset (Set (ℝ × ℝ))) (C : Set (ℝ × ℝ)) : Prop :=
  C ∈ 𝒞 ∧ ∀ D ∈ 𝒞, D ≠ C → ¬ D ⊆ boundedRegion C

/-- Two families of curves are (topologically) equivalent if a homeomorphism of `ℝ²` maps
the union of the first onto the union of the second. -/
def TopEquivalent (A B : Set (Set (ℝ × ℝ))) : Prop :=
  ∃ h : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), h '' (⋃₀ A) = ⋃₀ B

/-- The polynomial vector field `V` realises the configuration `𝒞`: the set of all limit
cycles of `V` is equivalent to `𝒞`. -/
def Realizes (V : PolyField) (𝒞 : Finset (Set (ℝ × ℝ))) : Prop :=
  TopEquivalent (𝒞 : Set (Set (ℝ × ℝ))) {O | IsLimitCycle V.toField O}

end HilbertSixteenth


