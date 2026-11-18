-- Prove2me | solution 1 for ArtinKP.F.zPsi_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:33.258283+00:00
-- url     : https://prove2.me/submissions/9a9734f2-a4d9-4c50-a4ef-a62d053089a0

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_F_zPsi_add
import Theorems.Thm_ArtinKP_F_zPsi_smul

section
-- module Solutions.Artin.KP.F_Per_Z
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 5: the residue `z_Ψ` — linearity, translations, `ρ_∞`

* `zPsi_of_mD`: `z_Ψ` from a continuation of `mD D Ψ` over a strict cell.
* `zPsi_add`, `zPsi_smul`, `zPsi_sum`: `Ψ ↦ z_Ψ` is linear.
* `zPsi_translate_nMat`: `z_{n(t)·Ψ} = z_Ψ` for `t ∈ R`.
* **`zPsi_restrict`**: `z_{Φρ_∞} = q/(q+1) · z_Φ` for every genuine section `Φ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA ArtinKP.N2

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

/-! ### Finite sums of twisted sections -/

section z

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

include hG hz6 in
theorem zPsi_zero : zPsi P hG hz6 (0 : TSection ι 𝔪) = 0 := by
  have h := zPsi_smul (P := P) hG hz6 0 (0 : TSection ι 𝔪)
  have e : (0 : ℂ) • (0 : TSection ι 𝔪) = 0 := by ext s p; simp
  rw [e, zero_mul] at h
  exact h

include hG hz6 in
/-- **`z` of a finite sum.** -/
theorem zPsi_sum_oai {α : Type*} (Tf : Finset α) (Ψ : α → TSection ι 𝔪) :
    zPsi P hG hz6 (∑ t ∈ Tf, Ψ t) = ∑ t ∈ Tf, zPsi P hG hz6 (Ψ t) := by
  classical
  induction Tf using Finset.induction_on with
  | empty => simpa using zPsi_zero (P := P) hG hz6
  | insert a Tf ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact zPsi_add hG hz6 _ _

/-! ### Translations -/

/-! ### `ρ_∞` -/

end z

end

end ArtinKP.F
end

theorem solution.{u_1, u_2} : type_of% @ArtinKP.F.zPsi_sum_oai.{u_1, u_2} := @ArtinKP.F.zPsi_sum_oai.{u_1, u_2}
