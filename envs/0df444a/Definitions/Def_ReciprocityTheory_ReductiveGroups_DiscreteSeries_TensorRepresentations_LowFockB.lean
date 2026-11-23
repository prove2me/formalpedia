-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:06.317937+00:00
-- url     : https://prove2.me/theorems/9973df9b-90ca-43ec-9bf9-d6fa846179f3
-- title:
--   Low Fock B
-- statement:
--   Definitions and structural lemmas for Low Fock B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def lfPhysModes (ε : Fin n → Bool) : Finset (Fin (n * n)) :=
  univ.filter fun m => ε (finProdFinEquiv.symm m).1 = true ∧ ε (finProdFinEquiv.symm m).2 = false
abbrev LfIdx (ε : Fin n → Bool) : Type := {S : Finset (Fin (n * n)) // S ⊆ lfPhysModes ε}
def lfMatFull (ε : Fin n → Bool) (a b : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (sgE ε cpFock cmFock a b)
def lfMat (ε : Fin n → Bool) (a b : Fin n) : Matrix (LfIdx ε) (LfIdx ε) ℂ :=
  (lfMatFull ε a b).submatrix Subtype.val Subtype.val
def lfP (i a : Fin n) : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ :=
  LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a)
end ReciprocityTheory.ChartRestriction.DS


