-- Prove2me | Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
-- name    : Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:43.092679+00:00
-- url     : https://prove2.me/theorems/5996f3cb-5b59-470f-811b-a1c0218eb04a
-- title:
--   Ubint Constant Coeff Eq Zero
-- statement:
--   Definitions and structural lemmas for Ubint Constant Coeff Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DropLevelBounds/ConstantCoeffVanishing/UbintConstantCoeffEqZero.lean

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
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
open MvPowerSeries Finset
namespace Formalism.UnitaryBoundIntegral
open Formalism.IncomingBounds
section UBIntLemmas
variable {C : Type} [Field C] {σ : Type}
end UBIntLemmas
section UBIntRows
variable {C : Type} [Field C] {n0 : ℕ}
open Classical in

def ubint_rowPart (h : MvPowerSeries (PVar n0) C) (b : Fin n0) : MvPowerSeries (PVar n0) C :=
  fun m => if ∀ x ∈ m.support, rowOf x = b then coeff m h else 0
end UBIntRows
section UBIntMain
variable {C : Type} [Field C] {n0 : ℕ}
def ubint_box (n0 L y : ℕ) : Set (PVar n0 →₀ ℕ) :=
  {m | (∀ b, rowDegZ m b ≤ L * y) ∧ ∀ b, rowDegZ' m b ≤ y}
end UBIntMain
end Formalism.UnitaryBoundIntegral


