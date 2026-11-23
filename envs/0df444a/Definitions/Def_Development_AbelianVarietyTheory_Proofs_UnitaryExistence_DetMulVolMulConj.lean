-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:39.746544+00:00
-- url     : https://prove2.me/theorems/b842e528-5f61-45b7-a05f-70428d008cf5
-- title:
--   Det Mul Vol Mul Conj
-- statement:
--   Definitions and structural lemmas for Det Mul Vol Mul Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetMulVolMulConj.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.DetIdeal
section General
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
def vol {R : Type} [CommRing R] {r : ℕ} (L : Set (Fin r → R)) : Ideal R :=
  Ideal.span {d | ∃ Y : Matrix (Fin r) (Fin r) R, (∀ i, Y i ∈ L) ∧ Y.det = d}
end General
section Denominators
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
end Denominators
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end GlobalTheory.DetIdeal


