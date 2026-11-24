-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:29.791131+00:00
-- url     : https://prove2.me/theorems/d3593b59-0ca9-4116-9b0a-7ae4b953934f
-- title:
--   KCountable
-- statement:
--   Definitions and structural lemmas for KCountable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/KCountable.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdUnimod
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WAU
open Formalism.MainNotions.S MeasureTheory
def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype
def KgSubgroup : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ H : Subgroup I.Gf, (H : Set I.Gf) = I.Kg g
def KCompact : Prop := ∀ I : AutInst, IsCompact I.Kset
def KCountable : Prop :=
  ∀ I : AutInst, ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset
def IndexEq : Prop :=
  ∀ (I : AutInst) (x : I.Gf),
    ((Ksub I).map (MulAut.conj x).toMonoidHom).relIndex (Ksub I) =
      ((Ksub I).map (MulAut.conj x⁻¹).toMonoidHom).relIndex (Ksub I)
end PI.WAU


