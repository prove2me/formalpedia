-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
-- name    : Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:22.70583+00:00
-- url     : https://prove2.me/theorems/4d567742-8f0b-4070-b0d6-fac0b6f62b88
-- title:
--   Three Forms
-- statement:
--   Definitions and structural lemmas for Three Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/ThreeForms.lean

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace ThreeFormsAlt
section Len
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
def qlen (X Y : Submodule R W) : ℕ∞ := Module.length R (↥X ⧸ Y.comap X.subtype)
end Len
section Sc
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
def scE (a : K) (ha : a ≠ 0) : Z ≃ₗ[𝓞 K] Z :=
  (LinearEquiv.smulOfNeZero K Z a ha).restrictScalars (𝓞 K)
end Sc
section Core
variable {O K Z : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [ValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup Z] [Module K Z] [Module O Z]
  [IsScalarTower O K Z]
end Core
section Split
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
abbrev OO (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors
end Split
section Ram
open IsLocalRing
end Ram
end ThreeFormsAlt
end Formalism.EigenvalueLevelCeiling


