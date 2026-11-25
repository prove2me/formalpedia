-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianSymplecticBasisLocalExtension
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianSymplecticBasisLocalExtension
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:51.304928+00:00
-- url     : https://prove2.me/theorems/fc8b4fd0-8ff9-5f33-95b2-2fb10d8a17fd
-- title:
--   Hermitian Symplectic Basis Local Extension
-- statement:
--   Definitions and structural lemmas for Hermitian Symplectic Basis Local Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianSymplecticBasisLocalExtension.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN
noncomputable section
namespace GlobalTheory.HL.EichlerParams
section Local
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]
def Sm (L : LocE K R) (γ : K) (x : R) : Prop := ∃ o ∈ L.O, x = algebraMap K R γ * o
variable (L : LocE K R)
def piL {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (X Y : Fin r → Fin N → R) (T : Finset (Fin r))
    (v : Fin N → R) : Fin N → R :=
  fun j => v j - ∑ a ∈ T, (hf L Hm v (Y a) * X a j + hf L Hm v (X a) * Y a j)
end Local
section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
def piQ (sig : E →ₐ[F] E) {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E)
    (T : Finset (Fin r)) (w : Fin N → E) : Fin N → E :=
  fun j => w j - ∑ a ∈ T, (hq sig Hm w (Y a) * X a j + hq sig Hm w (X a) * Y a j)
end Global
end GlobalTheory.HL.EichlerParams


