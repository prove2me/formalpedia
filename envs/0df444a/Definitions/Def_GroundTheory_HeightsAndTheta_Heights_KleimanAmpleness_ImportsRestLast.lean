-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestLast
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestLast
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:29.754803+00:00
-- url     : https://prove2.me/theorems/7f5c6247-8ad9-4e5e-8c11-f7a4a3f10342
-- title:
--   Imports Rest Last
-- statement:
--   Definitions and structural lemmas for Imports Rest Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ImportsRestLast.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
def RestrictGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (N : ℕ) (Ω : Type) [Field Ω] [Algebra F Ω] (x : Fin (N + 1) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (x' : Fin (N + 1) → K') (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0)
    (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
    (∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      ∃ h : aeval x f / aeval x g ∈ R, σ ⟨_, h⟩ = aeval x' f / aeval x' g) →
    ∀ (Q : Kleiman.LineBundle F x) (Q' : Kleiman.LineBundle F x') (c : ℤ) (H : Set Ω) (ρ : Ω → K') (w : Ω)
      (w' : K'), w' ≠ 0 →
      (∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I = Submodule.span (Kleiman.chartRing F x I) H) →
      (∀ I, (Q'.toSubSystem.twist (Kleiman.twistSys F x' c)).sub I =
        Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)) →
      (∀ h ∈ H, ∃ hh : h * w ∈ R, σ ⟨_, hh⟩ = ρ h * w') →
      ∃ r : Ω → K', Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


