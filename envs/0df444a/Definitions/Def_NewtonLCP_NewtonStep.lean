-- Prove2me | Definitions.Def_NewtonLCP_NewtonStep
-- name    : NewtonLCP_NewtonStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:28.804047+00:00
-- url     : https://prove2.me/theorems/e02aced2-cc76-4b2e-8cd9-c92f5573cbcd
-- title:
--   The Newton matrix $H_{x,\mu}$ and the Newton step $(\Delta x,\Delta s)$
-- statement:
--   Let $(x,s)\in\mathcal F_{>0}(M,q)$, $\mu>0$ and $X=\mathrm{diag}(x)$. The **Newton matrix** is
--
--   $$H_{x,\mu}=\Big(I_n+\frac1\mu XMX\Big)^{-1},$$
--
--   and the **Newton step** from $(x,s,\mu)$ is $(\Delta x,\Delta s)\in\mathbb R^{2n}$ given by
--
--   $$\frac{\Delta x}{x}=H_{x,\mu}\,\mathrm{err}(x,s,\mu),\qquad \Delta s=M\Delta x .\qquad(10)$$
--
--   This is the standard Newton step toward the central-path equation $xs=\mu 1_n$; it keeps $s-Mx$ fixed.
--
--   **Formalization Note** Lean's matrix inverse returns $0$ for a singular matrix. For $M\in\mathcal P_\star$, $x>0$, $\mu>0$ the matrix is nonsingular (Corollary 2.5), and every theorem using the step assumes $M\in\mathcal P_\star$; Algorithm 3 tests $\det=0$ before taking a step.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Definition 4.1 and display (10), p.13

import Mathlib
import Definitions.Def_NewtonLCP_Centrality

open Matrix

namespace NewtonLCP

/-!
# The Newton matrix and the Newton step

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab…40f8), Definition 4.1 and display (10), p.13.

`H_{x,µ} = (Iₙ + (1/µ) X M X)⁻¹` with `X = diag(x)`; the Newton step `(∆x, ∆s)` from `(x, s, µ)`
is `∆x/x = H_{x,µ} err(x, s, µ)`, `∆s = M∆x`.

**Formalization Note.** The inverse is Mathlib's `Matrix.inv`, which returns `0` for a singular
matrix. For `M ∈ P⋆`, `x > 0` and `µ > 0` the matrix is nonsingular (Corollary 2.5); every
milestone using the step assumes `M ∈ P⋆`, and Algorithm 3 tests `det = 0` before taking a step.
`∆x = x · (H_{x,µ} err(x, s, µ))` entrywise.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Newton matrix `H_{x,µ} = (Iₙ + µ⁻¹ X M X)⁻¹`, `X = diag(x)` (Definition 4.1). -/
noncomputable def newtonMatrix (M : Matrix ι ι ℝ) (x : ι → ℝ) (mu : ℝ) : Matrix ι ι ℝ :=
  (1 + mu⁻¹ • (diagonal x * M * diagonal x))⁻¹

/-- The `x`-part of the Newton step: `∆x = x ∘ (H_{x,µ} err(x, s, µ))` ((10)). -/
noncomputable def newtonDx (M : Matrix ι ι ℝ) (x s : ι → ℝ) (mu : ℝ) : ι → ℝ :=
  fun i => x i * (newtonMatrix M x mu *ᵥ err x s mu) i

/-- The `s`-part of the Newton step: `∆s = M ∆x` ((10)). -/
noncomputable def newtonDs (M : Matrix ι ι ℝ) (x s : ι → ℝ) (mu : ℝ) : ι → ℝ :=
  M *ᵥ newtonDx M x s mu

end NewtonLCP


