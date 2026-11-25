-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:04:19.914799+00:00
-- url     : https://prove2.me/theorems/3f363056-a7ae-4ac1-ba15-70627297c60b
-- title:
--   Psi Ker Iff
-- statement:
--   Definitions and structural lemmas for Psi Ker Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/PsiKerIff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
import Theorems.Thm_MassDataIdxCore_conjP_int
import Theorems.Thm_MassDataIdxCore_conjP_mul
import Theorems.Thm_MassDataIdxCore_conjP_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
def toO (M : Matrix n n K) (hM : IntM O M) : Matrix n n O := fun i j => ⟨M i j, hM i j⟩
theorem toO_map (M : Matrix n n K) (hM : IntM O M) : (toO O M hM).map (algebraMap O K) = M := by
  ext i j
  rfl
theorem map_inj : Function.Injective fun M : Matrix n n O => M.map (algebraMap O K) := by
  intro M N h
  ext i j
  have h1 := congrFun (congrFun h i) j
  exact h1
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K) {H : Type} [Group H] (m : H →* GL n T)
  (hK : ∀ h x, x ∈ Lat O θ J P ↔ ((m h : GL n T) : Matrix n n T) *ᵥ x ∈ Lat O θ J P)
include hK in
theorem int_of (h : H) : IntM O (conjPrime₂ θ P (m h)) :=
  conjP_int O θ J P (m h) fun x hx => (hK h x).mp hx
def psiU (h : H) : GL n O :=
  ⟨toO O _ (int_of O θ J P m hK h), toO O _ (int_of O θ J P m hK h⁻¹), by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, mul_inv_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm, by
    apply map_inj O
    simp only [Matrix.map_mul, toO_map, ← conjP_mul, ← map_mul, inv_mul_cancel, map_one, conjP_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm⟩
theorem psiU_map (h : H) : ((psiU O θ J P m hK h : GL n O) : Matrix n n O).map (algebraMap O K) =
    conjPrime₂ θ P (m h) :=
  toO_map O _ (int_of O θ J P m hK h)
def psi : H →* GL n O where
  toFun := psiU O θ J P m hK
  map_one' := by
    apply Units.ext
    apply map_inj O
    simp only [psiU_map, map_one, conjP_one, Units.val_one]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  map_mul' _ _ := by
    apply Units.ext
    apply map_inj O
    simp only [Units.val_mul, Matrix.map_mul, psiU_map, map_mul, conjP_mul]
end MassDataIdxCore


