-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:00.982668+00:00
-- url     : https://prove2.me/theorems/584dbc80-e31d-49d0-8249-b30fba78cdcb
-- title:
--   Full To Gl Is Self Adjoint
-- statement:
--   Definitions and structural lemmas for Full To Gl Is Self Adjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FullToGlIsSelfAdjoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace GlobalTheory.JR.Step
section Alg
variable {r : ℕ} {k : Type} [CommRing k]
def eL (r : ℕ) (k : Type) [CommRing k] : Fin (r + 1) → k := Pi.single (Fin.last r) 1
def blocks (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) : Gl r k :=
  (A.submatrix Fin.castSucc Fin.castSucc, fun i => A (Fin.castSucc i) (Fin.last r),
    fun j => A (Fin.last r) (Fin.castSucc j), A (Fin.last r) (Fin.last r))
def lift (Z : Gl r k) (μ l : k) : Gl (r + 1) k := (full Z, μ • eL r k, eL r k, l)
def embHom (r : ℕ) (k : Type) [CommRing k] :
    Matrix (Fin r) (Fin r) k →* Matrix (Fin (r + 1)) (Fin (r + 1)) k where
  toFun g := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  map_one' := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  map_mul' g h := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
def emb (r : ℕ) (k : Type) [CommRing k] : GL (Fin r) k →* GL (Fin (r + 1)) k := Units.map (embHom r k)
def glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) : Gl r k' :=
  (Y.1.map φ, fun i => φ (Y.2.1 i), fun i => φ (Y.2.2.1 i), φ Y.2.2.2)
end Alg
section Herm
variable {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
theorem full_toGl_isSelfAdjoint (X : Hn r F E) (hl : star (algebraMap F E X.2.2) = algebraMap F E X.2.2) :
    IsSelfAdjoint (full X.toGl) := by
  have hA : X.1.1ᴴ = X.1.1 := X.1.2
  unfold IsSelfAdjoint full Hn.toGl
  simp only [Matrix.star_eq_conjTranspose, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.fromBlocks_conjTranspose, hA]
  congr 1
  congr 1
  all_goals (ext i j; simp [hl])
end Herm
section Unr
variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]
def liftH (X : Hn r F E) (ν : E) (l : F) : Hn (r + 1) F E :=
  (⟨full X.toGl, full_toGl_isSelfAdjoint X (Unram.star_fix _)⟩, ν • eL r E, l)
def uEmb (r : ℕ) (E : Type) [Field E] [StarRing E] :
    Matrix.unitaryGroup (Fin r) E →* Matrix.unitaryGroup (Fin (r + 1)) E where
  toFun g := ⟨embHom r E g.1, by
    have hs : star (embHom r E g.1) = embHom r E (star g.1) := by
      simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
        Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
        Matrix.conjTranspose_one]
    rw [Matrix.mem_unitaryGroup_iff, hs, ← map_mul, Matrix.mem_unitaryGroup_iff.mp g.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)
end Unr
end GlobalTheory.JR.Step


