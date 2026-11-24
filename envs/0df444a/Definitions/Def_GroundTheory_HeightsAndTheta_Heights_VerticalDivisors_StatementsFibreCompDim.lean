-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:23.130639+00:00
-- url     : https://prove2.me/theorems/e73705a2-44a4-4540-ad5a-cf820cccb3d0
-- title:
--   Statements Fibre Comp Dim
-- statement:
--   Definitions and structural lemmas for Statements Fibre Comp Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsFibreCompDim.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial IsDedekindDomain
def FibreCompDim.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (n : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)) (v : HeightOneSpectrum O),
    P.IsPrime → P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
        ringKrullDim (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸
            W.map (MvPolynomial.map (algebraMap O v.asIdeal.ResidueField))) =
          ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F)))
end GroundTheory.Heights₂.Heights.Vertical


