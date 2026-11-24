-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMap
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:35.507528+00:00
-- url     : https://prove2.me/theorems/c3690469-6edd-40e2-af08-f7b427cb7e6b
-- title:
--   Continuous Cell Map
-- statement:
--   Definitions and structural lemmas for Continuous Cell Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousCellMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace GlobalTheory.FlagPts
namespace GlobalTheory.FlagPts.CellCont
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def polyMat (i : ι) :
    Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) (MvPolynomial (CellIdx k V) k) :=
  fun a c => if a = c then 1 else if h : c < a then MvPolynomial.X ⟨i, (a, c), h⟩ else 0
def polyOnCell (b : Frames k V) : Subalgebra k (Frames k V → k) where
  carrier := {f | ∃ P : MvPolynomial (CellIdx k V) k, ∀ u, f (cellFrame b u) = MvPolynomial.eval u P}
  mul_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P * Q, fun u => by simp [hP, hQ]⟩
  add_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun u => by simp [hP, hQ]⟩
  algebraMap_mem' := fun c => ⟨MvPolynomial.C c, fun u => (MvPolynomial.eval_C (f := u) c).symm⟩
end GlobalTheory.FlagPts.CellCont
namespace GlobalTheory.FlagPts
end GlobalTheory.FlagPts


