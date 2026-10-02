-- Prove2me | Definitions.Def_HunterPDE_Shared_HolderSeminorm
-- name    : HunterPDE_Shared_HolderSeminorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:11:34.618739+00:00
-- url     : https://prove2.me/theorems/cf09c84e-6848-42e1-bef3-be85504331df
-- title:
--   Definition 1.1 — the Hölder seminorm [u]_{α,Ω}
-- statement:
--   Let $\Omega \subset \mathbb{R}^n$ and $0 < \alpha \le 1$. The **Hölder seminorm** of $u : \Omega \to \mathbb{R}$ with exponent $\alpha$ is
--   $$[u]_{\alpha,\Omega} = \sup_{\substack{x, y \in \Omega \\ x \ne y}} \frac{|u(x) - u(y)|}{|x - y|^{\alpha}}. \qquad (1.1)$$
--   The function $u$ is uniformly Hölder continuous with exponent $\alpha$ in $\Omega$ when this quantity is finite. When $\Omega = \mathbb{R}^n$ the book writes $[u]_{0,\alpha}$.
--
--   It serves two missions of the series: the Hölder estimate for the Newtonian potential (mission II, Theorem 2.28, p. 40) and Morrey's inequality (mission III, Theorem 3.36, p. 68).
--
--   **Formalization Note.** The supremum is taken in the extended nonnegative reals $[0, \infty]$, so $[u]_{\alpha,\Omega} = \infty$ exactly when $u$ is not uniformly Hölder continuous, and $[u]_{\alpha,\Omega} = 0$ when $\Omega$ has fewer than two points. This names the seminorm itself, unlike Mathlib's `HolderWith`, which fixes a constant. $|x - y|$ is the Euclidean norm.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 2, Definition 1.1, Eq. (1.1)

import Mathlib

namespace HunterPDE.Shared

open scoped ENNReal

/-- The Hölder seminorm (1.1) of Hunter, *Notes on PDEs*, Definition 1.1 (p. 2):
`[u]_{α,Ω} = sup_{x, y ∈ Ω, x ≠ y} |u(x) − u(y)| / |x − y|^α`, taken in `ℝ≥0∞`, so that it is
`∞` exactly when the supremum is unbounded (then `u` is not uniformly Hölder continuous with
exponent `α` on `Ω`), and `0` when `Ω` has fewer than two points. `|x − y|` is the Euclidean
norm of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def holderSeminorm {n : ℕ} (α : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (|u x - u y| / ‖x - y‖ ^ α)

end HunterPDE.Shared


