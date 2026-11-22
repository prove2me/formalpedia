-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:45.975451+00:00
-- url     : https://prove2.me/theorems/5fdaa706-297c-4ed3-b0ff-dbaf7b01a85d
-- title:
--   Sym Strip
-- statement:
--   Definitions and structural lemmas for Sym Strip, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
open Classical in

def qs_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × SymIdx n b) (TIdx nu) ℤ := fun y K =>
  ∑ m : ↥(qs_D mu nu) → Fin n,
    if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
      (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
        ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0)
    else 0
open Classical in

def qs_mid (b : ℕ) (mu nu : Fin n → ℤ) (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) : GLCoord ℤ n :=
  ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
    ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      (if ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1 then
        (∏ c : ↥(qs_D mu nu), ((qs_sg (qs_ext mu J c.1) (a c) : ℤ) : GLCoord ℤ n)) *
          ∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0),
            qs_mn (qs_gC n) (qs_add (qs_D mu nu) (qs_ext mu J) a c) (qs_ext nu K c) else 0)
  else 0
end Formalism.InvariantFactorPaths.ColumnFamilies


