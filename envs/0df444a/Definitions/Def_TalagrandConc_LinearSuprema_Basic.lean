-- Prove2me | Definitions.Def_TalagrandConc_LinearSuprema_Basic
-- name    : TalagrandConc_LinearSuprema_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:56.699955+00:00
-- url     : https://prove2.me/theorems/ab237e08-462a-4911-b5c2-9dee82d0dbfb
-- title:
--   Coefficient norm, linear supremum, median, and convex hull distance
-- statement:
--   Let $\mathcal F$ be a family of coefficient vectors $\alpha=(\alpha_i)_{i=1}^N$. Define
--   $\|\alpha\|_2=(\sum_i\alpha_i^2)^{1/2}$, $\sigma=\sup_{\alpha\in\mathcal F}\|\alpha\|_2$, and
--   $$Z(x)=\sup_{\alpha\in\mathcal F}\sum_{i=1}^N\alpha_i x_i.$$
--
--   A median $M$ of a real random variable $Z$ satisfies both $P(Z\le M)\ge 1/2$ and $P(Z\ge M)\ge 1/2$.
--   For $A\subseteq\Omega^N$, the mismatch vectors $U_A(x)$ have coordinates in $\{0,1\}$ and admit a
--   witness $y\in A$ such that $s_i=0$ implies $x_i=y_i$. Their convex hull is $V_A(x)$, and $f_c(A,x)$
--   is the Euclidean distance from zero to $V_A(x)$, with value $+\infty$ when $A$ is empty.
--
--   These definitions give the common notation for the linear-supremum concentration result and its
--   convex-hull observation.
--
--   **Formalization Note** Coordinates use `Fin N`; $f_c$ has extended nonnegative values, while
--   $Z$ and $\sigma$ are real suprema used under nonemptiness and boundedness assumptions.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 123, Section 4.1; p. 156, Eq. (8.2) and Section 8.1

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.LinearSuprema

noncomputable def coeffNorm {N : ℕ} (α : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ i, α i ^ 2)

noncomputable def sigma {N : ℕ} (F : Set (Fin N → ℝ)) : ℝ :=
  sSup (coeffNorm '' F)

noncomputable def linearSupremum {N : ℕ} (F : Set (Fin N → ℝ)) (x : Fin N → ℝ) : ℝ :=
  sSup ((fun α : Fin N → ℝ => ∑ i, α i * x i) '' F)

def mismatchVectors {N : ℕ} {Ω : Type*} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  {s | (∀ i, s i = 0 ∨ s i = 1) ∧
    ∃ y ∈ A, ∀ i, s i = 0 → x i = y i}

def mismatchHull {N : ℕ} {Ω : Type*} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : Set (Fin N → ℝ) :=
  convexHull ℝ (mismatchVectors A x)

noncomputable def convexDistance {N : ℕ} {Ω : Type*} (A : Set (Fin N → Ω))
    (x : Fin N → Ω) : ENNReal :=
  ⨅ s ∈ mismatchHull A x,
    ENNReal.ofReal (Real.sqrt (∑ i, s i ^ 2))

def linearSublevel {N : ℕ} (F : Set (Fin N → ℝ))
    (r : Fin N → ℝ) (a : ℝ) : Set (Fin N → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    linearSupremum F (fun i => r i + x i) ≤ a}

end TalagrandConc.LinearSuprema


