-- Prove2me | solution 1 for ArtinKP.T.integral_theta_of_hasCoef
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:46:33.939204+00:00
-- url     : https://prove2.me/submissions/424f663b-a7da-4aa1-ac9c-fa50c63d5aa9

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
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_T_hasSeed
import Theorems.Thm_ArtinKP_T_integral_theta_of_hasCoefT

section
-- module Solutions.Artin.KP.T_Theta
/-! # WP-T, file 6: genuine sections — `aCont`, `tau`, the instance `E.Theta`, coefficients of `θ`

For `ν ∈ R ∖ 0` and a genuine section `Φ` (`Ψ = Φ.twist hG hz6`, `a₀ = (B.kubota hG hz6).aSer Φ ν`):

* `aCont hG hz6 Φ ν = contSlit a₀` — holomorphic on `E.slit` (`differentiableOn_aCont`), equal to
  the series on `Re s > 2` (`aCont_eq`), unique (`aCont_unique`);
* `tau hG hz6 Φ ν = resSlit a₀ = lim_{t↓0} (s_t − 4/3)·aCont(s_t)` (`tendsto_tau`);
* **`theta hG hz6 : E.Theta (B.kubota hG hz6) (4/3)`** with `toResFun = E.resFunSlit`;
* **`coeff_theta`** (item 3): the Fourier coefficients of `C5.theta Γ (Φ.twist)` for the cells of
  any `Γ`; `coeff_cont`: the same for the continuation on `E.slit`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {ν}

/-- **Fourier coefficients of `θ` over an admissible cell** (MATH2 §2.1(d) for `ν ≠ 0`). -/
theorem integral_theta_of_hasCoef_oai (hν : ν ≠ 0) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) {D : Set (InfinitePlace F → ℂ)} {κ : ℂ} {n : ℕ}
    {φ : (InfinitePlace F → ℝ) → ℂ} (hc : HasCoef hG hz6 Φ ν D κ) (hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    ∫ Q in X.box n, conj (stripFn D (freq (ν : F)) φ Q)
        * X.lift Γ (C5.theta Γ (Φ.twist hG hz6)) Q ∂X.vol F
      = κ * tau hG hz6 Φ ν * Wc D n φ (ν : F) (4 / 3) :=
  integral_theta_of_hasCoefT P hG hz6 (coe_ne_zero hν) (hasSeed hG hz6 Φ hν) hΓ hc hDm hb hφ hφ1

/-! ### The archimedean factor as an integral over `v` -/


/-! ### Fourier coefficients of `θ` for the cells of `Γ` -/

end

end ArtinKP.T
end

theorem solution.{u_1} : type_of% @ArtinKP.T.integral_theta_of_hasCoef_oai.{u_1} := @ArtinKP.T.integral_theta_of_hasCoef_oai.{u_1}
