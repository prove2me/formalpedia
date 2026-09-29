-- Prove2me | Definitions.Def_DualSSD_Duality_conj
-- name    : DualSSD_Duality_conj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:35:01.562237+00:00
-- url     : https://prove2.me/theorems/f1bccc3d-3bc3-4e55-8c76-0a4e816ec44f
-- title:
--   Convex conjugate $F^*(p)=\sup_\xi\{p\xi-F(\xi)\}$ on $\overline{\mathbb R}$ and the subdifferential
-- statement:
--   For a function $F:\mathbb R\to\overline{\mathbb R}$ its **convex conjugate** is
--   $$F^*(p)=\sup_{\xi\in\mathbb R}\{p\xi-F(\xi)\},\qquad p\in\mathbb R,$$
--   a function $\mathbb R\to\overline{\mathbb R}$; points where $F(\xi)=+\infty$ contribute $-\infty$ to the supremum.
--
--   For a real function $f:\mathbb R\to\mathbb R$ and $\eta\in\mathbb R$, the **subdifferential** of $f$ at $\eta$ is the set of slopes of supporting lines,
--   $$\partial f(\eta)=\{g\in\mathbb R:\ f(\eta)+g(\xi-\eta)\le f(\xi)\ \text{for all }\xi\in\mathbb R\}.$$
--
--   These are the convex-analysis tools through which the paper relates the second performance function and the second quantile function.
--
--   **Formalization Note** The conjugate is computed in `EReal` with `⨆`, so the supremum is always genuine; the paper applies it to convex functions only, and the definition is stated for every function.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 61 (conjugate, §1 last paragraph) and p. 65, eq. (3.3) (subdifferential notation)

import Mathlib

namespace DualSSD.Duality

/-- The convex conjugate `F*(p) = sup_ξ {pξ − F(ξ)}` of a function `F : ℝ → ℝ̄`
(Ogryczak–Ruszczyński 2002, §1, p. 61), computed in the complete lattice `EReal`, so the
supremum is always genuine. A term with `F ξ = +∞` contributes `(pξ) − ⊤ = ⊥` and drops out of
the supremum. The paper applies it only to convex `F`; the definition is stated for every `F`. -/
noncomputable def conj (F : ℝ → EReal) (p : ℝ) : EReal :=
  ⨆ ξ : ℝ, ((p * ξ : ℝ) : EReal) - F ξ

/-- The subdifferential of a real function `f : ℝ → ℝ` at `η`: the set of slopes `g` with
`f η + g (ξ − η) ≤ f ξ` for all `ξ` (the notation `∂F_X^(2)(η)` of (3.3),
Ogryczak–Ruszczyński 2002, §3, p. 65). -/
def subdiff (f : ℝ → ℝ) (η : ℝ) : Set ℝ :=
  {g : ℝ | ∀ ξ : ℝ, f η + g * (ξ - η) ≤ f ξ}

end DualSSD.Duality


