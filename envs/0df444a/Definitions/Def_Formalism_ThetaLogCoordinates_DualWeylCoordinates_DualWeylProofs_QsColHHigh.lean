-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:14.368081+00:00
-- url     : https://prove2.me/theorems/e34f46fb-2d83-4be5-a94e-c59e44862d4d
-- title:
--   Qs Col HHigh
-- statement:
--   Definitions and structural lemmas for Qs Col HHigh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHHigh.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
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
def qs_ext (mu : Fin n → ℤ) (I : TIdx mu) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ TCols mu then (I ⟨c, h⟩).1 else if c ≤ mu (lastIdx n) then univ else ∅
def qs_res (mu : Fin n → ℤ) (F : ℤ → Finset (Fin n)) (hF : ∀ c, (F c).card = colH mu c) : TIdx mu :=
  fun c => ⟨F c.1, hF c.1⟩
def qs_ini (h : ℕ) : Finset (Fin n) := univ.filter fun x => x.1 < h
def qs_TM (lo : ℤ) (S : Finset ℤ) (J I : ℤ → Finset (Fin n)) : GLCoord ℤ n :=
  ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * ∏ c ∈ S, qs_mn (qs_gC n) (J c) (I c)
end Formalism.InvariantFactorPaths.ColumnFamilies


