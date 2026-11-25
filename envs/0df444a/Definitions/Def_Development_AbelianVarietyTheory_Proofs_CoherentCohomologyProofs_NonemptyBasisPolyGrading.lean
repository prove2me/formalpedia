-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:02.756839+00:00
-- url     : https://prove2.me/theorems/37a677f9-c544-4ff3-ba52-a561dd4d4342
-- title:
--   Nonempty Basis Poly Grading
-- statement:
--   Definitions and structural lemmas for Nonempty Basis Poly Grading, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_codRestrict
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_finite_neg_sum_eq
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id


set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
namespace GlobalTheory.ProjCoh
section Top
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
def topCech (A : Cube.{0} ι R) {N : ℕ} (hN : Fintype.card ι = N + 1) :
    A.obj Finset.univ →ₗ[R] (cechComplex A).homology N :=
  cechClass A N ∘ₗ (CubeTop.topTerm A hN).codRestrict _ fun _ =>
    (Cube.subsingleton_term A (p := N + 1 + 1) (by omega)).elim _ _
end Top
section Count
abbrev NegExp (N : ℕ) (n : ℤ) : Type := {a : Fin (N + 1) → ℤ // ∑ i, a i = n ∧ ∀ i, a i < 0}
def negExpEquiv (N : ℕ) (n : ℤ) :
    NegExp N n ≃ {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = -n - (N + 1)} where
  toFun a := ⟨fun i => (-a.1 i - 1).toNat, by
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (a := -a.1 i - 1)
      (by have := a.2.2 i; omega)]
    simp [Finset.sum_sub_distrib, a.2.1]⟩
  invFun a := ⟨fun i => -(a.1 i : ℤ) - 1, by simp [Finset.sum_sub_distrib, a.2],
    fun i => show -(a.1 i : ℤ) - 1 < 0 by omega⟩
  left_inv a := Subtype.ext (funext fun i => by have := a.2.2 i; simp only; omega)
  right_inv a := Subtype.ext (funext fun i => by simp)
instance finite_negExp (N : ℕ) (n : ℤ) : Finite (NegExp N n) := by
  have := (finite_neg_sum_eq (Fin (N + 1)) n).to_subtype
  refine Finite.of_injective (β := {a : {a : Fin (N + 1) → ℤ // ∑ i, a i = n} |
      Finset.univ.filter (fun i => a.1 i < 0) = Finset.univ})
    (fun a => ⟨⟨a.1, a.2.1⟩, Finset.filter_eq_self.2 fun i _ => a.2.2 i⟩) fun a b h => ?_
  exact Subtype.ext (congrArg (·.1.1) h)
end Count
section Poly
variable (R : Type) [CommRing R] (N : ℕ) (n : ℤ)
instance finite_natVec : Finite {a : Fin (N + 1) → ℕ // ∑ i, (a i : ℤ) = n} :=
  Finite.of_equiv _ ((negExpEquiv N (-n - (N + 1))).trans
    (Equiv.subtypeEquivRight fun a => by rw [show -(-n - (N + 1)) - ((N : ℤ) + 1) = n by ring]))
end Poly
end GlobalTheory.ProjCoh


