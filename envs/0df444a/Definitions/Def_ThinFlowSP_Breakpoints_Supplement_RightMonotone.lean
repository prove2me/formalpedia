-- Prove2me | Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone
-- name    : ThinFlowSP_Breakpoints_Supplement_RightMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:41:15.022532+00:00
-- url     : https://prove2.me/theorems/ed3a1af1-4242-44ec-b7d6-902b26d85809
-- title:
--   Definition 20, p. 15 — monotone and right-monotone functions (outside a null set)
-- statement:
--   Definition 20 of Kaiser. A function $g:\mathbb R\to\mathbb R$ is **monotonically non-decreasing** (**non-increasing**) on a set $S$ if there is a Lebesgue null set $N$ such that
--   $$g(\xi)\le g(\hat\xi)\qquad(\text{resp. }g(\xi)\ge g(\hat\xi))\qquad\text{for all }\xi,\hat\xi\in S\setminus N\text{ with }\xi\le\hat\xi .$$
--   It is **monotone** on $S$ if it is non-decreasing or non-increasing on $S$, and **right-monotone** if for every $\xi\in\mathbb R$ there is $\varepsilon>0$ such that $g$ is monotone on $[\xi,\xi+\varepsilon]$.
--
--   Right-monotonicity is the regularity assumed on inflow rates in Theorems 21, 24 and 25, and on arc inflow rates in Theorem 25.
--
--   **Formalization Note** The exceptional null set is kept, so the notion does not depend on the representative of an almost-everywhere class. Local integrability, which the paper builds into the definition, is a separate hypothesis wherever the notion is used.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 15, Definition 20

import Mathlib

open MeasureTheory

namespace ThinFlowSP.Breakpoints.Supplement

/-- Definition 20 (p. 15), non-decreasing on `S`: `g ξ ≤ g ξ̂` for all `ξ ≤ ξ̂` in `S` outside
some null set. -/
def MonoNondecAE (g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ Z : Set ℝ, volume Z = 0 ∧ ∀ x ∈ S \ Z, ∀ y ∈ S \ Z, x ≤ y → g x ≤ g y

/-- Definition 20 (p. 15), non-increasing on `S`: `g ξ ≥ g ξ̂` for all `ξ ≤ ξ̂` in `S` outside
some null set. -/
def MonoNonincAE (g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∃ Z : Set ℝ, volume Z = 0 ∧ ∀ x ∈ S \ Z, ∀ y ∈ S \ Z, x ≤ y → g y ≤ g x

/-- Definition 20 (p. 15): `g` is monotone on `S` if it is non-decreasing or non-increasing
on `S` (outside a null set). -/
def MonotoneAE (g : ℝ → ℝ) (S : Set ℝ) : Prop := MonoNondecAE g S ∨ MonoNonincAE g S

/-- Definition 20 (p. 15): `g` is right-monotone if for every `ξ` there is `ε > 0` such that `g`
is monotone on `[ξ, ξ + ε]`. -/
def RightMonotone (g : ℝ → ℝ) : Prop :=
  ∀ ξ : ℝ, ∃ ε > 0, MonotoneAE g (Set.Icc ξ (ξ + ε))

end ThinFlowSP.Breakpoints.Supplement


