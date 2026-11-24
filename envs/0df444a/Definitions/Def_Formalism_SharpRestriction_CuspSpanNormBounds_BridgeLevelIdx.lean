-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:23:24.343671+00:00
-- url     : https://prove2.me/theorems/a656971c-9378-414f-94b7-fce0a823f9ef
-- title:
--   Bridge Level Idx
-- statement:
--   Definitions and structural lemmas for Bridge Level Idx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean

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
namespace Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
def LevelGen (g : ℕ) : Prop :=
  ∃ (m : ℕ) (l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)) (S : Finset (Fin I.n → I.E ⊗[I.F] Af I.F)),
    m ≤ I.n ∧ S.card ≤ g ^ (2 * I.f * I.n) ∧ (∀ j, l j ∈ I.Lf) ∧
    (∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z) ∧
    ∀ y ∈ I.Lf, ∃ s ∈ S, ∃ z ∈ I.Lf, y = s + (g : I.E ⊗[I.F] Af I.F) • z
variable {I}
end Formalism.MainNotions.BridgeLevelIdx
end


