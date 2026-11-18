-- Prove2me | solution 1 for ArtinKP.N2.zRes_eq_zPsi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:44.02558+00:00
-- url     : https://prove2.me/submissions/edb96c40-4ccc-4cfe-ae9e-22f4b17fd715

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
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_N2_zRes_congr

section
-- module Solutions.Artin.KP.N2_Cor
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N2, file 5: Corollary N without hypotheses; the intrinsic residue `z_Ψ`

* **`corollaryN`**, **`corollaryN_of_continuation`**: `N.corollaryN`, `N.corollaryN_of_continuation`
  with both named hypotheses discharged (`CuspOrth` by `N2.cuspOrth`, `EisEigen` by `GL.eisEigen`).
* `corollaryN_reps`, `corollaryN_of_continuation_reps`: the same, testing only the finitely many
  cusps `cuspMat Γ o` (`o` a `Γ`-orbit of pair classes on which the weights of `Ψ` at `4/3` do not
  vanish).
* `zPsi Ψ`: the residue `z_Ψ` of the `ht^{2−s}`-coefficient of the constant term at `∞`, defined
  with a chosen level group and cell; **`zRes_eq_zPsi`**: every `zRes Γ Ψ D n` (`n ≥ 1`) equals it.
* `cf_theta_translate_zPsi`: the constant term of `θ_Ψ` at the cusp `σ⁻¹∞` is `z_{σ·Ψ}·ht^{2/3}`.
* **`theta_eq_zero_iff`**, **`theta_eq_zero_iff_reps`**: `θ_Ψ = 0` iff `z_{σ·Ψ} = 0` for all
  `σ ∈ SL₂(R)`, iff for the finitely many representatives.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

section

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}

/-! ### Corollary N -/

/-! ### The intrinsic residue -/

lemma inv_levelGroup (Ψ : TSection ι 𝔪) : Inv (levelGroup Pk hG hz6 Ψ) Ψ :=
  (exists_finiteIndex_inv Pk hG hz6 Ψ).choose_spec.2

lemma cell_level (Ψ : TSection ι 𝔪) :
    Cell (levelGroup Pk hG hz6 Ψ) (levelCell Pk hG hz6 Ψ) (levelN Pk hG hz6 Ψ) :=
  (exists_strict_cell (levelGroup Pk hG hz6 Ψ)).choose_spec.choose_spec.2.2.2.2

lemma one_le_levelN (Ψ : TSection ι 𝔪) : 1 ≤ levelN Pk hG hz6 Ψ :=
  (exists_strict_cell (levelGroup Pk hG hz6 Ψ)).choose_spec.choose_spec.2.2.2.1

/-- **`zRes` is intrinsic**: every `zRes Γ Ψ D n` with `n ≥ 1` is `zPsi Ψ`. -/
theorem zRes_eq_zPsi_oai (hΓ : Inv Γ Ψ) {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n)
    (hn : 1 ≤ n) : zRes Γ Ψ D n = zPsi Pk hG hz6 Ψ :=
  zRes_congr hG hΓ (inv_levelGroup Pk hG hz6 Ψ) hD hn (cell_level Pk hG hz6 Ψ)
    (one_le_levelN Pk hG hz6 Ψ)

end

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.zRes_eq_zPsi_oai.{u_1} := @ArtinKP.N2.zRes_eq_zPsi_oai.{u_1}
