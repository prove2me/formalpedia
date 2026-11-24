-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:48.863273+00:00
-- url     : https://prove2.me/theorems/9a20596d-25e6-478c-bcbc-b5af2c12add1
-- title:
--   WBasis
-- statement:
--   Definitions and structural lemmas for WBasis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/WBasis.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
namespace PI.ScRefExists.Sk
def WBasis : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p r k : ℕ) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → IsPrincipalIdealRing (Ap I p) → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M p → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ w : Fin (k + 1) → Fin I.n → I.E,
      (∀ i, w i ∈ LA I p ∧ ∀ a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0) ∧
      LinearIndependent I.E w ∧
      ∀ x ∈ LA I p, (∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0) →
        x ∈ Submodule.span (Ap I p) (Set.range w)
end PI.ScRefExists.Sk


