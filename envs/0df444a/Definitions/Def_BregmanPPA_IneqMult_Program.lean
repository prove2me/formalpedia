-- Prove2me | Definitions.Def_BregmanPPA_IneqMult_Program
-- name    : BregmanPPA_IneqMult_Program
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:42.173327+00:00
-- url     : https://prove2.me/theorems/7f7d06d0-3f08-4604-83d3-a29e0252143e
-- title:
--   Problem (10) — convex inequality program, dual and monotone conjugate
-- statement:
--   Let $C\subseteq\mathbb R^n$ be closed, nonempty, and convex, and let $f,g_1,\ldots,g_m$ be proper lower semicontinuous convex functions, finite on $C$. Problem (10) minimizes $f(x)$ over $x\in C$ subject to $g_i(x)\le0$. Its **dual functional** is
--
--   $$d(p)=\inf_{x\in C}\{f(x)+\langle p,g(x)\rangle\}\quad(p\ge0),\qquad d(p)=-\infty\quad(p\not\ge0).$$
--
--   An optimal multiplier maximizes $d$, and a primal solution is feasible and minimizes $f$ among feasible points. For a Bregman function $h$, the **monotone conjugate** is
--
--   $$h^{*+}(z)=\sup_{p\ge0}\{\langle p,z\rangle-h(p)\}.$$
--
--   The file also defines the extension of $h$ by $+\infty$, ordinary convex conjugacy, orthant indicators, infimal convolution, and the Appendix's recession and essential strict convexity notions. These objects support Lemmas 2, 3, and A1–A4.
--
--   **Formalization Note** Extended-real infima and suprema preserve infinite values. The real vector $g(x)$ is formed only at $x\in C$, where each constraint function is finite. Essential strict convexity is strict convexity on every convex subset of the subdifferential domain; recession directions use the source's limit inferior condition.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 205, 215–216, 223–224, problem (10), Lemma 2, Appendix, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open Filter Topology InertialFB.IFB

namespace BregmanPPA.IneqMult

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The closed positive orthant of the multiplier space. -/
def nonnegOrthant (m : ℕ) : Set (E m) := {p | ∀ i, 0 ≤ p i}

/-- The strict positive orthant of the multiplier space. -/
def posOrthant (m : ℕ) : Set (E m) := {p | ∀ i, 0 < p i}

/-- The data and standing assumptions of problem (10), p. 215. -/
structure IsConvexProgram {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) : Prop where
  closed : IsClosed C
  nonempty : C.Nonempty
  convex : Convex ℝ C
  f_proper : IsProperFn f
  f_convex : IsConvexFn f
  f_lsc : LowerSemicontinuous f
  g_proper : ∀ i, IsProperFn (g i)
  g_convex : ∀ i, IsConvexFn (g i)
  g_lsc : ∀ i, LowerSemicontinuous (g i)
  f_finite : ∀ x ∈ C, f x ≠ ⊤
  g_finite : ∀ i, ∀ x ∈ C, g i x ≠ ⊤

/-- The real vector of constraint values, used only for `x ∈ C`. -/
noncomputable def gvec {n m : ℕ} (g : Fin m → E n → EReal) (x : E n) : E m :=
  (WithLp.equiv 2 _).symm (fun i => (g i x).toReal)

/-- The dual functional of (10), p. 215; it is `-∞` off the closed positive orthant. -/
noncomputable def dualFn {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (p : E m) : EReal := by
  classical
  exact
  if p ∈ nonnegOrthant m then
    ⨅ x ∈ C, f x + ((inner ℝ p (gvec g x) : ℝ) : EReal)
  else ⊥

/-- A maximizer of the dual functional. -/
def IsOptimalMultiplier {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (p : E m) : Prop :=
  p ∈ nonnegOrthant m ∧ ∀ q, dualFn C f g q ≤ dualFn C f g p

/-- A feasible global minimizer of (10). -/
def IsSolution {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (x : E n) : Prop :=
  x ∈ C ∧ (∀ i, g i x ≤ 0) ∧ ∀ y ∈ C, (∀ i, g i y ≤ 0) → f x ≤ f y

/-- The extension of `h` by `+∞` outside the closure of its zone. -/
noncomputable def extendedH {m : ℕ} (S : Set (E m)) (h : E m → ℝ) (p : E m) : EReal := by
  classical
  exact if p ∈ closure S then (h p : EReal) else ⊤

/-- The extended-real convex conjugate. -/
noncomputable def conjE {m : ℕ} (F : E m → EReal) (z : E m) : EReal :=
  ⨆ p, ((inner ℝ p z : ℝ) : EReal) - F p

/-- The indicator of the closed positive orthant. -/
noncomputable def indicatorPos (m : ℕ) (p : E m) : EReal := by
  classical
  exact if p ∈ nonnegOrthant m then 0 else ⊤

/-- The indicator of the closed negative orthant. -/
noncomputable def indicatorNeg (m : ℕ) (p : E m) : EReal := by
  classical
  exact if (∀ i, p i ≤ 0) then 0 else ⊤

/-- The Fenchel–Rockafellar infimal convolution. -/
noncomputable def infConv {m : ℕ} (F G : E m → EReal) (z : E m) : EReal :=
  ⨅ y, F (z - y) + G y

/-- The monotone conjugate `h*⁺` of §4.2. -/
noncomputable def monoConj {m : ℕ} (h : E m → ℝ) (z : E m) : EReal :=
  ⨆ p ∈ nonnegOrthant m, ((inner ℝ p z - h p : ℝ) : EReal)

/-- The monotone conjugate for a general extended-valued convex function, as in the Appendix. -/
noncomputable def monoConjE {m : ℕ} (F : E m → EReal) (z : E m) : EReal :=
  ⨆ p ∈ nonnegOrthant m, ((inner ℝ p z : ℝ) : EReal) - F p

/-- A recession direction in the sense stated at the opening of the Appendix, p. 223. -/
def IsRecessionDirection {m : ℕ} (F : E m → EReal) (y : E m) : Prop :=
  ∀ x : E m, F x ≠ ⊤ →
    Filter.liminf (fun α : ℝ => F (x + α • y)) Filter.atTop < ⊤

/-- Rockafellar's essential strict convexity: strict convexity on every convex
subset of the subdifferential domain. Only finite values are read on these subsets. -/
def EssentiallyStrictlyConvex {m : ℕ} (F : E m → EReal) : Prop :=
  ∀ s : Set (E m), Convex ℝ s → s ⊆ ThreeOpSplitting.Convergence.dom (BregmanPPA.Convergence.subdiffOp F) →
    StrictConvexOn ℝ s (fun p => (F p).toReal)

/-- The extended-valued composition appearing in Lemma A4. -/
noncomputable def compositeFn {n m : ℕ} (F : Fin m → E n → EReal)
    (F₀ : E m → EReal) (x : E n) : EReal := by
  classical
  exact if ∀ i, F i x ≠ ⊤ then F₀ (gvec F x) else ⊤

/-- The ordinary convex normal cone, empty outside the set. -/
def normalCone {n : ℕ} (C : Set (E n)) (x : E n) : Set (E n) :=
  {v | x ∈ C ∧ ∀ y ∈ C, inner ℝ v (y - x) ≤ 0}

end BregmanPPA.IneqMult


