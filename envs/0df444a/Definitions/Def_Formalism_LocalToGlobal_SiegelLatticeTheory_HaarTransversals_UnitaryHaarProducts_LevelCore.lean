-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LevelCore
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:39.29653+00:00
-- url     : https://prove2.me/theorems/59de5479-c6b8-4884-a9d7-76e408439e8a
-- title:
--   Level Core
-- statement:
--   Definitions and structural lemmas for Level Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LevelCore.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
namespace Formalism.L2.SG.Pf
def PsiTrCore : Prop :=
  ∀ (I : AutInst) (ψ : I.E ⊗[I.F] Af I.F → ℂ), (∀ x y, ψ (x + y) = ψ x * ψ y) →
    (∀ x ∈ IntAf I.F I.E, ψ x = 1) →
    (∀ x : I.E, ψ (Formalism.UG.inclE (F := I.F) (Af I.F) x) *
      ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x))) = 1) →
    ∀ y : I.E, (∀ o : 𝓞 I.E, ∃ m : ℤ, Algebra.trace ℚ I.E ((o : I.E) * y) = m) →
      ∀ t ∈ IntAf I.F I.E, ψ (t * Formalism.UG.inclE (F := I.F) (Af I.F) y) = 1
def DdTraceCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∀ y ∈ ((((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      ∀ o : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E ((o : E) * y) = m
end Formalism.L2.SG.Pf


