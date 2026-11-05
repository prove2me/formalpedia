-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_IsLocalSemigroupGenerator
-- name    : JRCurvedQFT_Symmetries_IsLocalSemigroupGenerator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:13.708116+00:00
-- url     : https://prove2.me/theorems/6a89fdda-ba53-465e-96d5-126641cf3f17
-- title:
--   Self-adjoint generator of a symmetric local semigroup
-- statement:
--   A densely defined self-adjoint operator $A$ is a **generator** of $(S_\alpha,\mathscr D_\alpha,T)$ if $\mathscr D_\alpha\subset D(e^{-\alpha A})$ and $S_\alpha=e^{-\alpha A}|_{\mathscr D_\alpha}$ for all $\alpha\in[0,T]$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Theorem 6.2, p. 11

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Spectral_spectralIntegral
import Definitions.Def_JRCurvedQFT_Symmetries_IsSpectralGenerator
import Definitions.Def_JRCurvedQFT_Symmetries_spectralExpNeg
import Definitions.Def_JRCurvedQFT_Symmetries_pmapApply

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open TeschlQM.Shared TeschlQM.Spectral

namespace JRCurvedQFT.Symmetries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `A` is a **self-adjoint generator** of `(S_α, 𝒟_α, T)`: `A` is densely defined and self-adjoint,
and with `P` its projection-valued measure, `𝒟_α ⊂ D(e^{−αA})` and `S_α = e^{−αA}|_{𝒟_α}` for all
`α ∈ [0, T]`. Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Theorem 6.2, p. 11. -/
def IsLocalSemigroupGenerator (T : ℝ) (D : ℝ → Submodule ℂ H) (S : ℝ → (H →ₗ.[ℂ] H))
    (A : H →ₗ.[ℂ] H) : Prop :=
  Dense (A.domain : Set H) ∧ IsSelfAdjoint A ∧ ∃ P : Set ℝ → (H →L[ℂ] H),
    IsSpectralGenerator P A ∧ ∀ α ∈ Set.Icc 0 T, ∀ f ∈ D α,
      ∃ h : f ∈ (spectralExpNeg P α).domain, spectralExpNeg P α ⟨f, h⟩ = pmapApply (S α) f

end JRCurvedQFT.Symmetries


