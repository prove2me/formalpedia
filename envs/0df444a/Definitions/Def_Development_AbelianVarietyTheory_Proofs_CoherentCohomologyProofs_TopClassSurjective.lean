-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:00.464797+00:00
-- url     : https://prove2.me/theorems/d3cdfd9c-6c88-43f7-a2f9-541576a7b00e
-- title:
--   Top Class Surjective
-- statement:
--   Definitions and structural lemmas for Top Class Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/TopClassSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_pi
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
namespace GlobalTheory.CubeTop
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
omit [LinearOrder ι] in

theorem univ_subset {n : ℕ} (hn : Fintype.card ι = n) (s : {s : Finset ι // s.card = n}) :
    (Finset.univ : Finset ι) ⊆ s.1 :=
  (Finset.eq_univ_of_card s.1 (s.2.trans hn.symm)).ge
def topTerm (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    A.obj Finset.univ →ₗ[R] Cube.Term A n :=
  LinearMap.pi fun s => Cube.res A (univ_subset hn s)
theorem d_top (A : Cube.{0} ι R) :
    (cubeComplex A).d (Fintype.card ι) (Fintype.card ι + 1) = 0 := by
  rw [cubeComplex_d]
  have := Cube.subsingleton_term A (Nat.lt_succ_self (Fintype.card ι))
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)
def topClass (A : Cube.{0} ι R) :
    A.obj Finset.univ →ₗ[R] (cubeComplex A).homology (Fintype.card ι) :=
  ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv).hom ∘ₗ topTerm A rfl
end GlobalTheory.CubeTop


