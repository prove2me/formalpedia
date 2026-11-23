-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:36.881187+00:00
-- url     : https://prove2.me/theorems/aae4b02d-6196-419f-a99f-7ec9ec3d4fe5
-- title:
--   Companion Matrix Of Coeffs Pow Mul Vec First Basis Vector
-- statement:
--   Definitions and structural lemmas for Companion Matrix Of Coeffs Pow Mul Vec First Basis Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean

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
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.ImgSec
section Alg
variable {k : Type} [CommRing k] {r : ℕ}
def e1 : Fin r → k := fun i => if (i : ℕ) = 0 then 1 else 0
def hankelShift (a : Inv r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => mom (sec a) ((i : ℕ) + (j : ℕ) + 1)
theorem hankelShift_isSymm (a : Inv r k) : (hankelShift a).IsSymm := by
  ext i j; simp [hankelShift]; ring_nf
end Alg
section Herm
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}
theorem map_isSelfAdjoint {N : Matrix (Fin r) (Fin r) F} (hN : N.IsSymm) :
    IsSelfAdjoint (N.map (algebraMap F E)) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j
  simp [Matrix.conjTranspose_apply, Unram.star_fix, hN.apply i j]
def mkX (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : Hn r F E :=
  (⟨star h⁻¹ * (hankelShift a).map (algebraMap F E) * h⁻¹, by
      have h1 := (map_isSelfAdjoint (E := E) (hankelShift_isSymm a)).conjugate (star h⁻¹)
      rw [star_star] at h1
      exact h1⟩, h *ᵥ e1, a.2.2)
variable {a : Inv r F} {h : Matrix (Fin r) (Fin r) E}
end Herm
section Top
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}
end Top
section Unit
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}
end Unit
end GlobalTheory.JR.ImgSec


