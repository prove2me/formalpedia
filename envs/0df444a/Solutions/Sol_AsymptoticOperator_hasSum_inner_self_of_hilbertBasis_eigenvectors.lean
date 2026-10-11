-- Prove2me | solution 1 for AsymptoticOperator.hasSum_inner_self_of_hilbertBasis_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:03:59.709205+00:00
-- url     : https://prove2.me/submissions/335b0396-5524-404a-a925-fb2ea370555e

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-- Let `A` be a symmetric partially defined operator on a real inner product space, and let `b`
be a Hilbert basis of eigenvectors of `A` lying in its domain, `A bᵢ = evᵢ bᵢ`. Then for every
`x` in the domain the quadratic form of `A` is `⟨A x, x⟩ = ∑ᵢ evᵢ ⟨x, bᵢ⟩²`. -/
theorem solution {E ι : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →ₗ.[ℝ] E) (hA : A.IsFormalAdjoint A)
    (b : HilbertBasis ι ℝ E) (ev : ι → ℝ)
    (hb : ∀ i, ∃ h : b i ∈ A.domain, A ⟨b i, h⟩ = ev i • b i) (x : A.domain) :
    HasSum (fun i => ev i * inner ℝ (x : E) (b i) ^ 2) (inner ℝ (A x) (x : E)) := by
  have hfun : (fun i => inner ℝ (A x) (b i) * inner ℝ (b i) (x : E)) =
      fun i => ev i * inner ℝ (x : E) (b i) ^ 2 := by
    funext i
    obtain ⟨h, hi⟩ := hb i
    have h1 : inner ℝ (A x) (b i) = ev i * inner ℝ (x : E) (b i) := by
      have := hA x ⟨b i, h⟩
      rw [this, hi, real_inner_smul_right]
    rw [h1, real_inner_comm (x : E) (b i)]
    ring
  rw [← hfun]
  exact b.hasSum_inner_mul_inner (A x) (x : E)
