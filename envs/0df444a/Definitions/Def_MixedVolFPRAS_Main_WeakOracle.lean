-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_WeakOracle
-- name    : MixedVolFPRAS_Main_WeakOracle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:29:37.592285+00:00
-- url     : https://prove2.me/theorems/3a9e3861-7954-4be9-a29f-91eb4b603485
-- title:
--   Weak membership oracles and well-presented convex bodies (Definition 1.1)
-- statement:
--   Let $K\subseteq\mathbb{R}^n$ be a convex body. A **weak membership oracle** for $K$ is a black box that, given a rational point $x\in\mathbb{Q}^n$ and a rational $\varepsilon>0$, answers YES, certifying $x\in K(\varepsilon)=K+\varepsilon B_2^n$, or NO, certifying $x\notin K(-\varepsilon)=\mathbb{R}^n\setminus((\mathbb{R}^n\setminus K)+\varepsilon B_2^n)$; either answer is allowed when both assertions hold. So a **valid** oracle is any function $O:\mathbb{Q}^n\times\mathbb{Q}\to\{\mathrm{YES},\mathrm{NO}\}$ with
--
--   $$\forall x\in\mathbb{Q}^n,\ \forall\varepsilon\in\mathbb{Q}_{>0}:\quad O(x,\varepsilon)=\mathrm{YES}\Rightarrow x\in K(\varepsilon),\qquad O(x,\varepsilon)=\mathrm{NO}\Rightarrow x\notin K(-\varepsilon).$$
--
--   **Initial data** for $K$ are a point $x^{\mathrm{init}}\in K\cap\mathbb{Q}^n$ and rationals $0<r\le R$ with $x^{\mathrm{init}}+rB_2^n\subseteq K\subseteq x^{\mathrm{init}}+RB_2^n$. A **well-presented** convex body is a convex body supplied with a valid weak membership oracle and initial data (Definition 1.1). An algorithm for $n$ bodies gets $n$ such oracles; a query names the body.
--
--   **Formalization Note.** A rational point is `Fin n → ℚ` and `toE x` is the same point of `E n`. `MemOracle n = Fin n → (Fin n → ℚ) → ℚ → Bool` holds the $n$ oracles (`true` = YES). `IsWeakMembershipOracle K O` constrains `O x ε` only for rational `ε > 0`, exactly as Definition 1.1. `IsInitialData` writes $x^{\mathrm{init}}+rB_2^n$ as the closed ball of radius $r$ about $x^{\mathrm{init}}$ (the same set). `IsWellPresented K O xinit r R` is the conjunction of convex body, valid oracle and initial data.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), pp. 2–3, Definition 1.1

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# Weak membership oracles and well-presented convex bodies (Definition 1.1)

Chen, Liu, *An FPRAS for Mixed Volumes*, pp. 2–3, Definition 1.1.

* A rational point `x ∈ ℚⁿ` is `Fin n → ℚ`; `toE x` is the same point of `ℝⁿ`.
* A weak membership oracle for one body is a function `(x, ε) ↦ YES/NO` (`true`/`false`) on
  `ℚⁿ × ℚ`. It is **valid** for the convex body `K` when, for every `x ∈ ℚⁿ` and every rational
  `ε > 0`, the answer YES implies `x ∈ K(ε)` and the answer NO implies `x ∉ K(−ε)`. Any function
  with this property is allowed (either answer when both hold); its values at `ε ≤ 0` are
  unconstrained.
* `MemOracle n` bundles the oracles of `n` bodies: `O i x ε` is the answer of the `i`-th body's
  oracle.
* Initial data `(x_init, r, R)`: a rational point `x_init ∈ K` and rationals `0 < r ≤ R` with
  `x_init + r B₂ⁿ ⊆ K ⊆ x_init + R B₂ⁿ` (closed balls of radii `r`, `R` about `x_init`).
-/

/-- The point of `ℝⁿ` with the given rational coordinates. -/
def toE {n : ℕ} (x : Fin n → ℚ) : E n := WithLp.toLp 2 (fun j => (x j : ℝ))

/-- The weak membership oracles of `n` bodies: `O i x ε` answers the query `(x, ε)` about body
`i` (`true` = YES, `false` = NO). -/
abbrev MemOracle (n : ℕ) : Type := Fin n → (Fin n → ℚ) → ℚ → Bool

/-- Validity of a weak membership oracle for `K` (Definition 1.1). -/
def IsWeakMembershipOracle {n : ℕ} (K : Set (E n)) (O : (Fin n → ℚ) → ℚ → Bool) : Prop :=
  ∀ (x : Fin n → ℚ) (ε : ℚ), 0 < ε →
    (O x ε = true → toE x ∈ epsNbhd K (ε : ℝ)) ∧
    (O x ε = false → toE x ∉ epsInterior K (ε : ℝ))

/-- The initial data of Definition 1.1: `x_init ∈ K ∩ ℚⁿ`, `0 < r ≤ R`,
`x_init + r B₂ⁿ ⊆ K ⊆ x_init + R B₂ⁿ`. -/
def IsInitialData {n : ℕ} (K : Set (E n)) (xinit : Fin n → ℚ) (r R : ℚ) : Prop :=
  toE xinit ∈ K ∧ 0 < r ∧ r ≤ R ∧
    Metric.closedBall (toE xinit) (r : ℝ) ⊆ K ∧ K ⊆ Metric.closedBall (toE xinit) (R : ℝ)

/-- A well-presented convex body (Definition 1.1): a convex body `K`, a valid weak membership
oracle `O` for it, and initial data `(x_init, r, R)`. -/
def IsWellPresented {n : ℕ} (K : Set (E n)) (O : (Fin n → ℚ) → ℚ → Bool)
    (xinit : Fin n → ℚ) (r R : ℚ) : Prop :=
  IsConvexBody K ∧ IsWeakMembershipOracle K O ∧ IsInitialData K xinit r R

end MixedVolFPRAS.Main


