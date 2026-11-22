-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:18.970234+00:00
-- url     : https://prove2.me/theorems/d2acf754-ddf2-4335-903a-0d6bcea50669
-- title:
--   Qa Nu Antitone
-- statement:
--   Definitions and structural lemmas for Qa Nu Antitone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaNuAntitone.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
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
def qa_S {n : ℕ} (m : Fin n × Fin n →₀ ℕ) (a p : Fin n) : ℕ := ∑ b : Fin n with b ≤ a, m (b, p)
def qa_g {n : ℕ} [NeZero n] (m : Fin n × Fin n →₀ ℕ) (k : ℤ) (p : Fin n) : Fin n :=
  if h : (univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card < n then
    ⟨(univ.filter fun a : Fin n => (qa_S m a p : ℤ) < k).card, h⟩ else lastIdx n
end Formalism.InvariantFactorPaths.ColumnFamilies


