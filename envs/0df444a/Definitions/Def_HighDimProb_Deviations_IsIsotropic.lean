-- Prove2me | Definitions.Def_HighDimProb_Deviations_IsIsotropic
-- name    : HighDimProb_Deviations_IsIsotropic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:07.83914+00:00
-- url     : https://prove2.me/theorems/fd832e8e-8caf-4114-8938-263abe336485
-- title:
--   An isotropic random vector
-- statement:
--   A random vector $X$ in $\mathbb R^n$ is **isotropic** if its covariance matrix is the
--   identity: $\Sigma(X) = \mathbb E[XX^\top] = I_n$. Isotropy is the hypothesis Theorem 9.1.1
--   places on the rows of the random matrix $A$.
--
--   **Formalization Note** Formalized via the book's own basis-free equivalent (Lemma 3.2.3):
--   $X$ is isotropic iff $\mathbb E\langle X,x\rangle^2 = \|x\|_2^2$ for every $x\in\mathbb R^n$,
--   together with an explicit integrability conjunct for each one-dimensional marginal
--   $\langle X,x\rangle$ (the same convention as `subgaussianNorm`, avoiding the junk value $0$ a
--   non-integrable Bochner integral would otherwise silently return).
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 47, Definition 3.2.1, via Lemma 3.2.3 (p. 47-48)

import Mathlib

open MeasureTheory

namespace HighDimProb.Deviations

/-- **`IsIsotropic P X`**: the random vector `X : Ω → EuclideanSpace ℝ (Fin n)` is isotropic on
the probability space `(Ω, P)`. Vershynin, *High-Dimensional Probability* (2018), Definition
3.2.1, p. 47 (PDF p. 55): "A random vector `X` in `ℝⁿ` is called isotropic if `Σ(X) = E[XXᵀ] =
Iₙ`." Formalized via the book's own basis-free equivalent, Lemma 3.2.3, p. 47/48 (PDF p. 55/56):
"`X` is isotropic if and only if `E⟨X,x⟩² = ‖x‖₂²` for all `x ∈ ℝⁿ`" — equal by the standard fact
that two symmetric matrices `A, B` agree iff `xᵀAx = xᵀBx` for every `x`, applied to `A = Σ(X)`,
`B = Iₙ`. The `Integrable` conjunct is essential for the same reason as in `subgaussianNorm`:
Mathlib's Bochner integral of a non-integrable function is `0` by convention, so without it a
non-integrable `⟨X,x⟩²` would vacuously satisfy the equation whenever `‖x‖² = 0`, i.e. at `x = 0`
only — harmless there, but the conjunct is kept uniformly for every `x` to make integrability of
every one-dimensional marginal `⟨X,x⟩` an explicit, checkable part of isotropy rather than a
silent side hypothesis needed later. -/
def IsIsotropic {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    Integrable (fun ω => (inner (𝕜 := ℝ) (X ω) x) ^ 2) P ∧
    ∫ ω, (inner (𝕜 := ℝ) (X ω) x) ^ 2 ∂P = ‖x‖ ^ 2

end HighDimProb.Deviations


