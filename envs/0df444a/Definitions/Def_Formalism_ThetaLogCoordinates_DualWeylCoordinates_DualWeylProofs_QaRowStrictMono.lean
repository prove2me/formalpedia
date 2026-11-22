-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:08.675752+00:00
-- url     : https://prove2.me/theorems/e5a83e86-b10c-4acd-b745-28a8017851ea
-- title:
--   Qa Row Strict Mono
-- statement:
--   Definitions and structural lemmas for Qa Row Strict Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaRowStrictMono.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def qa_nu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin n → ℕ := fun t => (mu t - mu (lastIdx n)).toNat
def qa_row {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) : Fin (colH mu c) → Fin n :=
  fun p => (I c).1.orderEmbOfFin (I c).2 p
def qa_exp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : Fin n × Fin n →₀ ℕ :=
  ∑ c : ↥(TCols mu), ∑ p : Fin (colH mu c), Finsupp.single (qa_row I c p, Fin.castLE (colH_le mu c) p) 1
def qa_cnt {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (a : Fin n) : ℕ :=
  ((I c).1.filter (· ≤ a)).card
end Formalism.InvariantFactorPaths.ColumnFamilies


