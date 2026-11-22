-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
-- name    : Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:50.21584+00:00
-- url     : https://prove2.me/theorems/1b3273cf-84aa-4bc4-9d61-34f0d2f9d463
-- title:
--   Lemma GG
-- statement:
--   Definitions and structural lemmas for Lemma GG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LemmaGG.lean

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
section Abstract
variable {R : Type*} [CommRing R] {Y Q : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup Q]
  [Module R Q]
end Abstract
section Concrete
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
noncomputable def ggE {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) : Z →ₗ[K] Z :=
  ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P)
end Concrete
end Formalism.EigenvalueLevelCeiling


