-- Prove2me | Definitions.Def_GradSuffice_Optimizable
-- name    : GradSuffice_Optimizable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:06.187115+00:00
-- url     : https://prove2.me/theorems/11e103b1-4d8b-449d-b8ab-1ea3b26d285b
-- title:
--   Optimizable domain
-- statement:
--   A convex domain $W\subseteq X$ is **optimizable** if for every $\varepsilon>0$ there are a finite number of queries $T\ge1$ and an $\varepsilon$-accurate (possibly randomized) first-order algorithm with $T$ queries on $W$; the bound $T=T(\varepsilon)$ is uniform over all convex 1-Lipschitz objectives and all valid oracles. When $W=B$ the space $X$ is called optimizable. This is item 1 of Theorem 1.
--
--   **Formalization Note** The randomness is any probability space $(\Omega,\mu)$ with $\Omega$ a type in the lowest universe.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.4

import Mathlib
import Definitions.Def_GradSuffice_IsAccurate

namespace GradSuffice

/-- **Optimizable domain.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.4: "We call `W` optimizable if, for every `ε > 0`, there
exists an ε-accurate first-order optimization algorithm with a finite query bound `T(ε)`, uniform
over all convex 1-Lipschitz objectives. When `W = B`, we also say that the underlying normed space
`X` is optimizable."

**Formalization Note.** The algorithm may be randomized: its seed space is any probability space
`(Ω, μ)` with `Ω : Type`. `0 < T` because the output is the last query. -/
def Optimizable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, 0 < T ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω)
    (μ : MeasureTheory.Measure Ω) (_ : MeasureTheory.IsProbabilityMeasure μ)
    (A : Ω → DetAlg X W T), IsAccurate W ε μ A

end GradSuffice


