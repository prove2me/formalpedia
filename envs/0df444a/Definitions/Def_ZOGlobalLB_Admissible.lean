-- Prove2me | Definitions.Def_ZOGlobalLB_Admissible
-- name    : ZOGlobalLB_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:46:01.138724+00:00
-- url     : https://prove2.me/theorems/43a3e29b-2e86-4c71-8d0a-9952a488436b
-- title:
--   The admissible class (2) of finite-sum objectives
-- statement:
--   Let $\Xi=\{1,\dots,n\}$ be a nonempty finite label set and $f_\xi:\mathbb R^d\to\mathbb R$ sample functions, with population mean $f=|\Xi|^{-1}\sum_{\xi}f_\xi$ on $\mathbb R^d$ (Euclidean norm). With initial point $0$, the family is **admissible** for $(\Delta,H,L_0)$ if
--   $$\inf f>-\infty,\qquad f(0)-\inf f\le\Delta,\qquad \mathrm{Lip}(\nabla f)\le H,\qquad \frac1{|\Xi|}\sum_{\xi\in\Xi}\mathrm{Lip}(f_\xi)^2\le L_0^2 .$$
--
--   This is the class of instances over which the lower bound of Theorem 2.1 is proved: a smooth population objective with bounded initial gap, and sample functions with a bounded second moment of their global Lipschitz constants.
--
--   **Formalization Note.** $f$ is required to be differentiable, so that Mathlib's `gradient` is the gradient; $\inf f>-\infty$ is boundedness below; Lipschitz constants are in $[0,\infty]$. The sample functions need not be differentiable or measurable.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Section 2, p.4, display (2)

import Mathlib
import Definitions.Def_ZOGlobalLB_lipConst

open scoped ENNReal

namespace ZOGlobalLB

/-- The Euclidean space `ℝᵈ` with its Euclidean norm (Section 2, p.4: "Norms are Euclidean"). -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- **Population mean** `f = |Ξ|⁻¹ Σ_{ξ ∈ Ξ} f_ξ` of a finite family of sample functions.
arXiv:2610.19652, Section 2, p.4.

**Formalization Note.** The finite label set `Ξ` is `Fin n`; the sample functions are
`F : Fin n → ℝᵈ → ℝ`. -/
noncomputable def popMean {d n : ℕ} (F : Fin n → E d → ℝ) (x : E d) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, F i x

/-- **The admissible class (2).** Xia, Yuan, arXiv:2610.19652, Section 2, p.4, display (2):
`Ξ` finite, `f = |Ξ|⁻¹ Σ_ξ f_ξ` on `ℝᵈ`, initial point `0`, and
`inf f > -∞`, `f(0) - inf f ≤ Δ`, `Lip(∇f) ≤ H`, `|Ξ|⁻¹ Σ_ξ Lip(f_ξ)² ≤ L₀²`.

**Formalization Note.**
* `Ξ = Fin n` with `0 < n` (a finite family is nonempty, since `|Ξ|⁻¹` appears).
* `Lip(∇f) ≤ H` is written as differentiability of `f` plus `lipConst (gradient f) ≤ H`:
  Mathlib's `gradient` is `0` where `f` is not differentiable, so differentiability must be
  stated for `∇f` to be the gradient.
* `inf f > -∞` is `BddBelow (range f)`, which makes the real infimum `⨅ x, f x` the true one.
* Lipschitz constants are `lipConst`, valued in `ℝ≥0∞`, so a non-Lipschitz `f_ξ` makes the
  moment `⊤` and the family inadmissible. The sample functions need not be differentiable or
  measurable; nothing beyond (2) is required. -/
def Admissible {d n : ℕ} (Δ H L₀ : ℝ) (F : Fin n → E d → ℝ) : Prop :=
  0 < n ∧
  Differentiable ℝ (popMean F) ∧
  BddBelow (Set.range (popMean F)) ∧
  popMean F 0 - ⨅ x, popMean F x ≤ Δ ∧
  lipConst (gradient (popMean F)) ≤ ENNReal.ofReal H ∧
  (n : ℝ≥0∞)⁻¹ * ∑ i, lipConst (F i) ^ 2 ≤ ENNReal.ofReal (L₀ ^ 2)

end ZOGlobalLB


