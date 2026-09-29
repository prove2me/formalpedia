-- Prove2me | Definitions.Def_ChapterH5
-- name    : ChapterH5
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T22:43:39.809732+00:00
-- url     : https://prove2.me/theorems/f712c3db-5e9b-4acf-8ecb-5d5e8d113cbc
-- title:
--   `QFM.tex` §9.1 describes the dimensional reduction used by the Krylov–Hashimoto generator. The standard polynomial Krylo ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.H5`, source chapter `BookProof/ChapterH5.lean`).
--
--   `QFM.tex` §9.1 describes the dimensional reduction used by the Krylov–Hashimoto generator. The standard polynomial Krylov subspace is
--
--   `Kry m(H̄, v₀) = span{v₀, H̄v₀, …, H̄^{m−1}v₀}`,
--
--   while the *rational* construction would need to solve `(γI − H̄)y = v` at every step. The observation of §9.1 is that pre-conditioning the seed removes the inversion entirely: applying the resolvent to `v = (γI − H̄)^{m} v₀` merely *lowers the polynomial degree*, and the shifted sequence `wₖ = (H̄ − γI)wₖ₋₁`, `w₀ = v₀`, spans exactly the standard Krylov subspace.
--
--   * `krylovSpan` and `krylov_subspace_span` — `Kry m(H̄, v₀)` is exactly the span of `{H̄^i v₀ | i < m}`, together with the basic monotonicity (`krylovSpan_mono`) and the invariance-step `krylovSpan_map_le`; * `shift_pow_sub_pow_mem` — the degree-lowering core: `(H̄ − γI)^m v₀` differs from `H̄^m v₀` by an element of `Kry m(H̄, v₀)` (the shift only adds lower-order terms); * `krylovSpan_shift_eq` — hence the shifted and unshifted Krylov subspaces coincide: `Kry m(H̄ − γI, v₀) = Kry m(H̄, v₀)`; * `inversion_free_seed` — for the pre-conditioned seed `v = (γI − H̄)^{m+1} v₀` the resolvent image is `(γI − H̄)^{m} v₀`: applying `(γI − H̄)⁻¹` drops the polynomial degree by one, so no linear system is ever solved; * `generator_bounded_of_rankOneProjector` — `H̄` is bounded: a rank-one projector contributes operator norm `≤ 1` and the diagonal part its own norm; * `krylov_no_inversion_eq_standard` — **headline**: the inversion-free sequence `wₖ = (H̄ − γI)wₖ₋₁`, `w₀ = v₀` spans the full Krylov subspace `Kry m(H̄, v₀)`.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH5.lean

import Definitions.Def_ChapterH4
import Mathlib

import Mathlib

/-!
# Chapter H5 — the inversion-free Krylov shortcut (plan Part F.1, roadmap §9.1)

`QFM.tex` §9.1 describes the dimensional reduction used by the Krylov–Hashimoto
generator.  The standard polynomial Krylov subspace is

  `Kry m(H̄, v₀) = span{v₀, H̄v₀, …, H̄^{m−1}v₀}`,

while the *rational* construction would need to solve `(γI − H̄)y = v` at every
step.  The observation of §9.1 is that pre-conditioning the seed removes the
inversion entirely: applying the resolvent to `v = (γI − H̄)^{m} v₀` merely
*lowers the polynomial degree*, and the shifted sequence
`wₖ = (H̄ − γI)wₖ₋₁`, `w₀ = v₀`, spans exactly the standard Krylov subspace.

## Deliverables

* `krylovSpan` and `krylov_subspace_span` — `Kry m(H̄, v₀)` is exactly the span of
  `{H̄^i v₀ | i < m}`, together with the basic monotonicity
  (`krylovSpan_mono`) and the invariance-step `krylovSpan_map_le`;
* `shift_pow_sub_pow_mem` — the degree-lowering core: `(H̄ − γI)^m v₀` differs
  from `H̄^m v₀` by an element of `Kry m(H̄, v₀)` (the shift only adds lower-order
  terms);
* `krylovSpan_shift_eq` — hence the shifted and unshifted Krylov subspaces
  coincide: `Kry m(H̄ − γI, v₀) = Kry m(H̄, v₀)`;
* `inversion_free_seed` — for the pre-conditioned seed `v = (γI − H̄)^{m+1} v₀`
  the resolvent image is `(γI − H̄)^{m} v₀`: applying `(γI − H̄)⁻¹` drops the
  polynomial degree by one, so no linear system is ever solved;
* `generator_bounded_of_rankOneProjector` — `H̄` is bounded: a rank-one projector
  contributes operator norm `≤ 1` and the diagonal part its own norm;
* `krylov_no_inversion_eq_standard` — **headline**: the inversion-free sequence
  `wₖ = (H̄ − γI)wₖ₋₁`, `w₀ = v₀` spans the full Krylov subspace
  `Kry m(H̄, v₀)`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterH5

section Krylov

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The **Krylov subspace** `Kry m(H, v) = span{v, Hv, …, H^{m−1}v}`. -/
def krylovSpan (H : E →ₗ[K] E) (v : E) (m : ℕ) : Submodule K E :=
  Submodule.span K {x | ∃ i < m, x = (H ^ i) v}

variable {H : E →ₗ[K] E} {v : E}

















/-! ## The inversion-free seed -/



/-! ## The inversion-free sequence -/

/-- The **inversion-free Krylov sequence** `w₀ = v₀`, `wₖ₊₁ = (H − γI)wₖ`: it uses
only applications of the generator, never a solve. -/
def noInversionSeq (H : E →ₗ[K] E) (γ : K) (v : E) : ℕ → E
  | 0 => v
  | (k + 1) => (H - γ • 1) (noInversionSeq H γ v k)





end Krylov

/-! ## Boundedness of the generator -/

section Bounded

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The rank-one operator `x ↦ ⟪u, x⟫ u`. -/
def rankOneProj (u : E) : E →L[ℂ] E := (innerSL ℂ u).smulRight u





end Bounded

end BookProof.ChapterH5

end


