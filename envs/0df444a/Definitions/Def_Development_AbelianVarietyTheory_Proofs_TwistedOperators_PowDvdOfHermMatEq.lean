-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:28.50481+00:00
-- url     : https://prove2.me/theorems/9e787992-73c3-4f87-aacc-6fd3029a28a0
-- title:
--   Pow Dvd Of Herm Mat Eq
-- statement:
--   Definitions and structural lemmas for Pow Dvd Of Herm Mat Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/PowDvdOfHermMatEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
namespace GlobalTheory.SatakeBound
section Hermite
variable {R : Type} [CommRing R] {n : ℕ}
abbrev HermIdx (p : R) (a : Fin n → ℕ) : Type :=
  ∀ i : Fin n, {j : Fin n // i < j} → R ⧸ Ideal.span {p ^ a i}
def hermMat (p : R) (a : Fin n → ℕ) (c : HermIdx p a) : Matrix (Fin n) (Fin n) R := fun i j =>
  if h : i < j then (c i ⟨j, h⟩).out else if i = j then p ^ a i else 0
variable {p : R} {a a' : Fin n → ℕ}
theorem hermMat_diag (c : HermIdx p a) (i : Fin n) : hermMat p a c i i = p ^ a i := by simp [hermMat]
theorem hermMat_gt (c : HermIdx p a) {i j : Fin n} (h : j < i) : hermMat p a c i j = 0 := by
  simp [hermMat, h.not_gt, h.ne']
theorem det_hermMat (c : HermIdx p a) : (hermMat p a c).det = p ^ ∑ i, a i := by
  rw [Matrix.det_of_isUpperTriangular (M := hermMat p a c) (fun _ _ h => hermMat_gt c h), ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => hermMat_diag c i
variable [IsDomain R]
end Hermite
section Count
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}
def hermGL (hp : Irreducible p) (a : Fin n → ℕ) (c : HermIdx p a) : GL (Fin n) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((algebraMap 𝒪[k] k).mapMatrix (hermMat p a c)) (by
    rw [← RingHom.map_det, det_hermMat]
    simpa using fun h => absurd h hp.ne_zero)
end Count
end GlobalTheory.SatakeBound


