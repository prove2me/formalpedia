-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:31.946666+00:00
-- url     : https://prove2.me/theorems/f490f8f2-7a14-4f89-b6c0-0a51be41bec6
-- title:
--   Row Tie PHa Defs
-- statement:
--   Definitions and structural lemmas for Row Tie PHa Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaDefs.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
def SatRetrSt : Prop :=
  ∀ (ι : Type) [Fintype ι] (W : Submodule ℤ (ι → ℤ)), (∀ (z : ℤ) (x : ι → ℤ), z ≠ 0 → z • x ∈ W → x ∈ W) →
    ∃ ρ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ), (∀ x, ρ x ∈ W) ∧ ∀ x ∈ W, ρ x = x
def RowInvUpSt : Prop :=
  ∀ (Ty : Type) (r : Ty → ℕ) (n : ℕ) (K : Type) [Field K] [CharZero K] (P : MvPolynomial (Letter Ty r n) K),
    (∀ (σ : Ty) (i i' : Fin (r σ)), i' < i → ∀ q : ℚ, rowShift r n K σ i i' (q : K) P = P) → RowInv r n K P
end Formalism.L2.FormalSeriesBounds.HaP


