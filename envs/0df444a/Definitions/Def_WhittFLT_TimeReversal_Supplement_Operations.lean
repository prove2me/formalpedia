-- Prove2me | Definitions.Def_WhittFLT_TimeReversal_Supplement_Operations
-- name    : WhittFLT_TimeReversal_Supplement_Operations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:40:30.712787+00:00
-- url     : https://prove2.me/theorems/0a933cd4-1cc3-4d30-9cc8-759b37c8bd71
-- title:
--   Integer-jump paths, nondecreasing time changes, composition and multiplication
-- statement:
--   Let $T_1,T_2,T_3$ be real intervals with $T_2\subseteq T_3$. The class $F(T_3)$ consists of càdlàg paths whose discontinuities occur only at integer times. The class $G(T_1,T_2)$ consists of nondecreasing, integer-valued càdlàg paths taking values in $T_2$. The space $D_0(T_1,T_2)$ has the relative $J_1$ topology. The operations are
--
--   $$(x\circ y)(t)=x(y(t)),\qquad (xv)(t)=x(t)v(t).$$
--
--   For strictly increasing $y$, its inverse is the unique preimage on its image. Composition with this inverse is defined on $y(T_1)$. Finite-dimensional evaluation takes a finite tuple of composed-path values. These constructions express the deterministic and law-level composition theorems and the multiplication theorem.
--
--   **Formalization Note** Intrinsic path operations use the common constructor `packD`; Theorems 3.4 and 4.2 also conclude that their outputs agree with these pointwise formulas, so the fallback branch cannot make their conclusions true. The real-valued inverse is zero off its image; all conclusions use it only on the image. The stochastic inverse chooses a preimage on the image, unique under strict monotonicity. No first-passage inverse is substituted for this ordinary inverse.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, §3, pp. 74, 76–77; §4, p. 79

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_PathSpace

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition
variable {S : Type*} [MetricSpace S]

/-- §3 F: discontinuities only at integer times. -/
def InF (T : Set ℝ) (x : ℝ → S) : Prop :=
  IsCadlagOn T x ∧ ∀ t ∈ disc T x, ∃ k : ℤ, t = (k : ℝ)

/-- §3 G: integer-valued nondecreasing paths with values in U. -/
def InG (T U : Set ℝ) (y : ℝ → ℝ) : Prop :=
  IsCadlagOn T y ∧ MonotoneOn y T ∧ MapsTo y T U ∧
    ∀ t ∈ T, ∃ k : ℤ, y t = (k : ℝ)

/-- Inverse on the image, zero outside the image. Under strict monotonicity
there is exactly one possible preimage, so no choice of inverse is being assumed. -/
noncomputable def inverseOn (T : Set ℝ) (y : ℝ → ℝ) (u : ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ t ∈ T, y t = u then h.choose else 0

/-- D₀(T,U), with the relative topology and Borel sigma field. -/
def D0 (T U : Set ℝ) :=
  {y : DPath T ℝ // Monotone y.1 ∧ ∀ t : T, y.1 t ∈ U}

instance d0Topology (T U : Set ℝ) : TopologicalSpace (D0 T U) :=
  inferInstanceAs (TopologicalSpace {y : DPath T ℝ // Monotone y.1 ∧ ∀ t : T, y.1 t ∈ U})
instance d0Measurable (T U : Set ℝ) : MeasurableSpace (D0 T U) := borel (D0 T U)
instance d0Borel (T U : Set ℝ) : BorelSpace (D0 T U) := ⟨rfl⟩

def timeRange {T U : Set ℝ} (y : D0 T U) : Set ℝ := range y.1.1

/-- The canonical composition function; its exactness as a D-valued map is
part of Theorem 3.4, separately from weak convergence of laws. -/
noncomputable def composeD {T₁ T₂ T₃ : Set ℝ} (h₂₃ : T₂ ⊆ T₃)
    (p : DPath T₃ S × D0 T₁ T₂) : DPath T₁ S :=
  packD (fun t => p.1.1 ⟨p.2.1.1 t, h₂₃ (p.2.2.2 t)⟩)

/-- Restrict an outer path to the deterministic time-change image. -/
def restrictToRange {T₁ T₂ T₃ : Set ℝ} (h₂₃ : T₂ ⊆ T₃) (y : D0 T₁ T₂)
    (x : DPath T₃ S) : DPath (timeRange y) S :=
  restrictD (by rintro u ⟨t, rfl⟩; exact h₂₃ (y.2.2 t)) x

/-- Compose with the inverse of a strictly increasing y on its image. -/
noncomputable def inverseD {T U : Set ℝ} (y : D0 T U) (z : DPath T S) :
    DPath (timeRange y) S :=
  packD (fun u => z.1 (Classical.choose u.2))

/-- Pointwise multiplication, with exactness included in Theorem 4.2. -/
noncomputable def multiplyD {T : Set ℝ} (p : DPath T ℝ × DPath T ℝ) : DPath T ℝ :=
  packD (fun t => p.1.1 t * p.2.1 t)

/-- Finite-dimensional evaluation of a composed path; the points are in T₁. -/
def composeEval {T₁ T₂ T₃ : Set ℝ} (h₂₃ : T₂ ⊆ T₃) {k : ℕ} (ts : Fin k → T₁)
    (p : DPath T₃ S × D0 T₁ T₂) : Fin k → S :=
  fun i => p.1.1 ⟨p.2.1.1 (ts i), h₂₃ (p.2.2.2 (ts i))⟩

end WhittFLT.TimeReversal.Supplement


