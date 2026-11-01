-- Prove2me | Definitions.Def_DRBatchBandit_Covering
-- name    : DRBatchBandit_Covering
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:01.493997+00:00
-- url     : https://prove2.me/theorems/a54b4895-c0d8-4d9d-8d2e-77b9012e9f81
-- title:
--   Empirical distance $\|f-g\|_{\mathbf P_n}$ and $L^2(\mathbf P)$ distance $\|f-g\|_{\mathbf P}$
-- statement:
--   For points $z_1,\dots,z_n$ the **empirical distance** of two functions is (p.42)
--   $$\|f-g\|_{\mathbf P_n}=\sqrt{\frac1n\sum_{i=1}^n(f(z_i)-g(z_i))^2},$$
--   and for a probability measure $\mathbf P$ on $\mathbb R$ the **$L^2(\mathbf P)$ distance** is $\|f-g\|_{\mathbf P}=\sqrt{\int(f-g)^2\,d\mathbf P}$ (p.54). The $t$-covering numbers $N(t,\mathcal F,\|\cdot\|_{\mathbf P_n})$ and $N(t,\mathcal F,\|\cdot\|_{\mathbf P})$ of the proof of Theorem 2 (pp.54–56) are the smallest number of members of $\mathcal F$ such that every $f\in\mathcal F$ is within distance $t$ of one of them.
--
--   **Formalization Note** The covering numbers are the published `PlugInRisk.coveringNumber` (internal, i.e. proper, covers; valued in $\mathbb N\cup\{\infty\}$, $\infty$ when no finite cover exists) applied to these distances, mapped to $[0,\infty]$, at scale $t$.
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Theorem A8 p.42 (‖·‖_{P_n}); proof of Theorem 2 p.54 (‖·‖_P). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib

open MeasureTheory

namespace DRBatchBandit

/-- The empirical `L²` distance `‖f − g‖_{P_n} = √((1/n) ∑ᵢ (f(zᵢ) − g(zᵢ))²)` on the points
`z₁, …, z_n` (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, Theorem A8, p.42).

**Formalization Note.** Covering numbers `N(t, ℱ, ‖·‖_{P_n})` are the published
`PlugInRisk.coveringNumber` (proper cover, `ℕ∞`-valued) applied to
`fun f g => ENNReal.ofReal (empDist z f g)` at scale `ENNReal.ofReal t`. -/
noncomputable def empDist {Z : Type*} {n : ℕ} (z : Fin n → Z) (f g : Z → ℝ) : ℝ :=
  Real.sqrt ((1 / n : ℝ) * ∑ i, (f (z i) - g (z i)) ^ 2)

/-- The `L²(P)` distance `‖f − g‖_P = √(∫ (f − g)² dP)` for a measure `P` on `ℝ`
(arXiv:2006.05630v7, proof of Theorem 2, p.54).

**Formalization Note.** Covering numbers `N(t, ℱ, ‖·‖_P)` are `PlugInRisk.coveringNumber`
applied to `fun f g => ENNReal.ofReal (L2Dist P f g)`. -/
noncomputable def L2Dist (P : Measure ℝ) (f g : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ y, (f y - g y) ^ 2 ∂P)

end DRBatchBandit


