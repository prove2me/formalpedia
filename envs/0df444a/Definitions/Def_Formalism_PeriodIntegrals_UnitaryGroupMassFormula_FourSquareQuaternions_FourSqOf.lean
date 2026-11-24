-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:59.195801+00:00
-- url     : https://prove2.me/theorems/bd58838a-46c8-4a09-a25e-b4b53268d081
-- title:
--   Four Sq Of
-- statement:
--   Definitions and structural lemmas for Four Sq Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/FourSqOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace PI.KerIso.FourSqW
def DiagId {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E → E) {n : Type} [Fintype n]
    (b : Module.Basis n K E) (q : n → ℚ) : Prop :=
  ∀ x y, algebraMap K E (Algebra.trace K E (x * cj y)) =
    ∑ i, (q i : E) * (algebraMap K E (b.repr x i) * cj (algebraMap K E (b.repr y i)))
def OrthDiag : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (n : Type) [Fintype n],
    Module.finrank ℚ K = 2 → Fintype.card n = Module.finrank K E → IsConj K cj →
    (∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) →
      ∃ (b : Module.Basis n K E) (q : n → ℚ), (∀ i, 0 < q i) ∧ DiagId (K := K) cj b q
def FromDiag : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (n : Type) [Fintype n] (b : Module.Basis n K E) (q : n → ℚ),
    (∀ i, 0 < q i) → DiagId (K := K) cj b q →
      ∃ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g
end PI.KerIso.FourSqW


