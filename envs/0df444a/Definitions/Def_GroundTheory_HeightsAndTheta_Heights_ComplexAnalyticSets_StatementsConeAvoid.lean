-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsConeAvoid
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsConeAvoid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:47.324496+00:00
-- url     : https://prove2.me/theorems/4c9d8999-1b98-4d9b-9018-707a2dc110af
-- title:
--   Statements Cone Avoid
-- statement:
--   Definitions and structural lemmas for Statements Cone Avoid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsConeAvoid.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
def leadForm (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent f.totalDegree f
def leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)))
def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range X)
def linIdeal (A : Matrix (Fin d) (Fin n) ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range (linPoly A))
def ConeAvoids (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ) : Prop :=
  originIdeal n ^ N ≤ leadIdeal J ⊔ linIdeal A
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.ComplexSets


