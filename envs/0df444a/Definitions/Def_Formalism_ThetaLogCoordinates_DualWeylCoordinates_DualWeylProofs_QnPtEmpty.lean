-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:47.446299+00:00
-- url     : https://prove2.me/theorems/dfc1953e-ea4a-48cc-8a94-e3892d264c74
-- title:
--   Qn Pt Empty
-- statement:
--   Definitions and structural lemmas for Qn Pt Empty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnPtEmpty.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
def qn_pt (n : ℕ) (D : Finset (Fin n × Fin n)) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℚ :=
  open Classical in
  fun v => (if v.1 = v.2 then 1 else 0) + (if v ∈ D then X v else 0)
def qn_IntS (n : ℕ) : Subring (MvPolynomial (Fin n × Fin n) ℚ) :=
  (MvPolynomial.map (σ := Fin n × Fin n) (Int.castRingHom ℚ)).range
def qn_low (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun v => v.2 < v.1
def qn_off {n : ℕ} (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun v => v.2 < v.1
end Formalism.InvariantFactorPaths.ColumnFamilies


