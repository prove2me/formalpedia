-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DiffGenLoc
-- name    : Formalism_PeriodIntegrals_DiffGenLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:24.653357+00:00
-- url     : https://prove2.me/theorems/ea8fb823-0087-4057-bcb2-cc0278efac6e
-- title:
--   Diff Gen Loc
-- statement:
--   Definitions and structural lemmas for Diff Gen Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DiffGenLoc.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DiffGenLoc
open NumberField IsDedekindDomain
abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d
def DiffExists : Prop := ∃ d, IsDiffVal v d
end PI.DiffGenLoc


