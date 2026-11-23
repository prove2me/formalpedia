-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:16.364237+00:00
-- url     : https://prove2.me/theorems/91798a16-e41e-4c97-84e0-b792c58514eb
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
def PartB : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    (∀ w, DualInAt A h A.L w) → ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) ≤
        ∑ᶠ w, lw K w * (γ w : ℝ)
end PI.DvRows


