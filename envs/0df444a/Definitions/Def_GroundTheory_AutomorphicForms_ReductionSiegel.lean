-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel
-- name    : GroundTheory_AutomorphicForms_ReductionSiegel
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:12:55.511101+00:00
-- url     : https://prove2.me/theorems/750dc0b8-49f8-5bff-b155-c56d2fe471fb
-- title:
--   Reduction Siegel
-- statement:
--   Definitions and structural lemmas for Reduction Siegel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Reduction_coe_blockOneHom
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finEval_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infAt_apply
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infEval_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Reduction.coe_blockOneHom
attribute [local simp] GroundTheory.Automorphic.Reduction.finAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.finEval_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infAt_apply
attribute [local simp] GroundTheory.Automorphic.Reduction.infEval_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
namespace GroundTheory.Automorphic
noncomputable section
namespace Reduction
variable {K : Type*} [Field K] [NumberField K]
section Unipotent
variable {R : Type*} [CommRing R] {n : ℕ}
def IsUnitriangular (M : Matrix (Fin n) (Fin n) R) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1
def unitriangular (p : Fin n → Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if i = j then 1 else if i < j then p i j else 0
theorem isUnitriangular_unitriangular (p : Fin n → Fin n → R) :
    IsUnitriangular (unitriangular p) := by
  refine ⟨fun i j hij => ?_, fun i => by simp [unitriangular]⟩
  have h1 : i ≠ j := fun h => (lt_irrefl j) (h ▸ hij)
  have h2 : ¬ i < j := not_lt.2 hij.le
  simp [unitriangular, h1, h2]
theorem IsUnitriangular.det_eq_one {M : Matrix (Fin n) (Fin n) R} (hM : IsUnitriangular M) :
    M.det = 1 := by
  rw [det_of_isUpperTriangular hM.1]
  simp [hM.2]
end Unipotent
section LastCol
variable {R : Type*} [CommRing R] {m : ℕ}
def lastColMat (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (v i') (fun j' => A i' j') j) i
@[simp] theorem lastColMat_last_last (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) :
    lastColMat A v (Fin.last m) (Fin.last m) = 1 := by simp [lastColMat]
@[simp] theorem lastColMat_last_castSucc (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (j : Fin m) :
    lastColMat A v (Fin.last m) j.castSucc = 0 := by simp [lastColMat]
@[simp] theorem lastColMat_castSucc_last (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R) (i : Fin m) :
    lastColMat A v i.castSucc (Fin.last m) = v i := by simp [lastColMat]
@[simp] theorem lastColMat_castSucc_castSucc (A : Matrix (Fin m) (Fin m) R) (v : Fin m → R)
    (i j : Fin m) : lastColMat A v i.castSucc j.castSucc = A i j := by simp [lastColMat]
end LastCol
section Diag
variable (n : ℕ)
def diagUnits {R : Type*} [CommRing R] : (Fin n → Rˣ) →* GL (Fin n) R where
  toFun d := ⟨diagonal fun i => (d i : R), diagonal fun i => ((d i)⁻¹ : Rˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' d e := Units.ext (by simp [diagonal_mul_diagonal])
def unitriangularGL (p : Fin n → Fin n → 𝔸[K]) : AdelicGLn.AdelicGL K n :=
  ⟨unitriangular p, adjugate (unitriangular p),
    by rw [mul_adjugate, (isUnitriangular_unitriangular p).det_eq_one, one_smul],
    by rw [adjugate_mul, (isUnitriangular_unitriangular p).det_eq_one, one_smul]⟩
end Diag
def siegelTorus (n : ℕ) (t : ℝ) : Set (AdelicGLn.AdelicGL K n) :=
  {a | ∃ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧
    a = diagUnits n fun i => posIdele (r i) (hr i)}
def siegelSet (n : ℕ) (ω : Set (AdelicGLn.AdelicGL K n)) (t : ℝ) : Set (AdelicGLn.AdelicGL K n) :=
  {g | ∃ b ∈ ω, ∃ a ∈ siegelTorus n t, ∃ k ∈ maxCompact, g = b * a * k}
end Reduction
end
end GroundTheory.Automorphic


