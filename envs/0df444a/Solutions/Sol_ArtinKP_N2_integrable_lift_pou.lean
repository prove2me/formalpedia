-- Prove2me | solution 1 for ArtinKP.N2.integrable_lift_pou
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:35:28.895516+00:00
-- url     : https://prove2.me/submissions/d83707fb-f81b-4355-822a-3a1c6097a062

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
import Definitions.Def_ArtinKPB002
import Definitions.Def_ArtinKPB012
import Theorems.Thm_ArtinKP_N2_lintegral_lift_pou_ne_top
import Theorems.Thm_ArtinKP_X_X_isPOU_pou

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.stronglyMeasurable_lift (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) :
    StronglyMeasurable (X.lift Γ u) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  stronglyMeasurable_liftQ u

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_QuotC
/-! # WP-X, file 8: unfolding for complex-valued functions (absolutely convergent case)

Complex versions of the Tonelli lemmas of `X_Quot`, under an absolute-integrability hypothesis
stated as finiteness of a lower integral.  Weights are the real numbers `(η a).toReal`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma IsPOU.le_one {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≤ 1 := by
  have h := ENNReal.le_tsum (f := fun g : G => η (g • a)) 1
  rwa [one_smul, hη.tsum_eq] at h

lemma IsPOU.ne_top {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≠ ⊤ :=
  ((hη.le_one a).trans_lt ENNReal.one_lt_top).ne

lemma IsPOU.enorm_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ‖(((η a).toReal : ℝ) : ℂ)‖ₑ = η a := by
  rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
  exact Real.enorm_toReal (hη.ne_top a)

lemma IsPOU.measurable_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    Measurable fun a => (((η a).toReal : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp hη.measurable.ennreal_toReal

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.N2_Main
/-! # WP-N2, file 4: stub N-1 (`N.CuspOrth`) and the unconditional Corollary N

* `Orb Γ S`: the (finitely many) `Γ`-orbits of pair classes; `orbEquiv`: an orbit is `Γ / stab`.
* `pe_decomp`, `pe_aOrb`: the pseudo-Eisenstein series is the finite sum over the orbits of the
  sums `Σ_{γ ∈ stab\Γ} g(log ht_{p₀}(γP))` (steps 1 of stub N-1).
* `orbit_integral_eq_zero`: unfolding to the stabilizer (step 2) and `cusp_integral_eq_zero`.
* **`inner_src_theta_eq_zero`**: `⟪[F_{4/3}], θ⟫ = 0` if the constant terms of `θ` vanish at the
  finitely many cusps `cuspMat Γ o` (one per orbit `o` in the support of the weights).
* **`cuspOrth`**: stub N-1, with no hypothesis left.
* **`corollaryN`, `corollaryN_of_continuation`**: Corollary N of MATH2 §2.2, unconditional.
* `zPsi`: the intrinsic residue `z_Ψ`; `zRes_eq_zPsi`; `theta_eq_zero_iff`,
  `theta_eq_zero_iff_reps` (all `σ`, resp. the finitely many representatives).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Orbits of pair classes -/

/-! ### The pseudo-Eisenstein series by orbits -/

/-! ### `L¹` bounds -/

lemma integrable_lift_pou_oai (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (v : X.L2 Γ) :
    Integrable (fun P => X.lift Γ v P * (((X.pou Γ P).toReal : ℝ) : ℂ)) (X.vol F) := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  refine ⟨((X.stronglyMeasurable_lift Γ v).measurable.mul
    (X.isPOU_pou Γ).measurable_toReal).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  simp only [enorm_mul, (X.isPOU_pou Γ).enorm_toReal]
  exact lt_of_le_of_ne le_top (lintegral_lift_pou_ne_top hG Γ v)

/-! ### One orbit -/

/-! ### Cusp representatives -/

/-! ### Stub N-1 -/

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.integrable_lift_pou_oai.{u_1} := @ArtinKP.N2.integrable_lift_pou_oai.{u_1}
