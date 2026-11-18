-- Prove2me | Definitions.Def_ArtinKPB015
-- name    : ArtinKPB015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:39:23.296303+00:00
-- url     : https://prove2.me/theorems/c3d1525c-b538-4fb7-8f27-5ef0d42a7b41
-- title:
--   Definitions bundle ArtinKPB015 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 407 declarations of that development: 222 definitions, 7 inductive types or structures, 21 instances and 157 theorems. The definitions and types are `ArtinKP.A.kappaHom`, `ArtinKP.B.AI`, `ArtinKP.B.IsHom`, `ArtinKP.B.Ninf`, `ArtinKP.B.Row.inf`, `ArtinKP.B.RowClass`, `ArtinKP.B.RowClass.act`, `ArtinKP.B.RowClass.actEquiv`, `ArtinKP.B.RowClass.ht`, `ArtinKP.B.RowClass.inf`, `ArtinKP.B.RowClass.mk`, `ArtinKP.B.Tfun`, `ArtinKP.B.ValidDepth`, `ArtinKP.B.Winf`, `ArtinKP.B.aCoeff`, `ArtinKP.B.cI`, `ArtinKP.B.chiInf`, `ArtinKP.B.eis`, `ArtinKP.B.eisRaw`, `ArtinKP.B.gTerm`, `ArtinKP.B.hI`, `ArtinKP.B.hKer`, `ArtinKP.B.jFun`, `ArtinKP.B.jTerm`, `ArtinKP.B.kerA`, `ArtinKP.B.kerInt`, `ArtinKP.B.kubota`, `ArtinKP.B.sI`, `ArtinKP.B.sPl`, `ArtinKP.B.term`, `ArtinKP.B.tildeC`, `ArtinKP.B1.E₂`, `ArtinKP.B1.FiniteCusps`, `ArtinKP.B1.G`, `ArtinKP.B1.IsSMat`, `ArtinKP.B1.PairClass`, `ArtinKP.B1.PairClass.act`, `ArtinKP.B1.PairClass.actEquiv`, `ArtinKP.B1.PairClass.actR`, `ArtinKP.B1.PairClass.actREquiv` and 189 more.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.A_Kubota`, `KP.B1_Bound`, `KP.B1_Const`, `KP.B1_Conv`, `KP.B1_Cusp`, `KP.B1_G`, `KP.B1_L2`, `KP.B1_Lattice`, `KP.B1_Pairs`, `KP.B7_Sum`, `KP.B_Def`, `KP.B_Def2`, `KP.B_FourArch`, `KP.B_FourCoeff`, `KP.B_FourIndex`, `KP.B_FourMain`, `KP.B_FourRows`, `KP.B_Kub`, `KP.C5_Level`, `KP.C5_Main`, `KP.C5_PE`, `KP.C5_Profile`, `KP.C5_Series`, `KP.CAbs_Form`, `KP.CAbs_Limit`, `KP.CAbs_Residue`, `KP.E_Model`, `KP.E_Pairing`, `KP.E_Series`, `KP.K_Bessel`, `KP.K_Jacquet`, `KP.N_Cont`, `KP.N_Orbit`, `KP.N_Shape`, `KP.RC_Compact`, `KP.RC_Cusp`, `KP.RC_CuspVol`, `KP.RC_Cutoff`, `KP.RF_Deriv1`, `KP.RF_Deriv2`, `KP.RF_Eis`, `KP.RF_Fourier`, `KP.RF_Strip`, `KP.RO_Bridge`, `KP.RO_Cusps`, `KP.RO_Orbits`, `KP.RO_Ring`, `KP.S2_Kubota`, `KP.S2_Lattice`, `KP.S2_Symbol`, `KP.S_Basic`, `KP.S_BigCell`, `KP.S_Ops`, `KP.S_Twisted`, `KP.T_Arch`, `KP.T_Coef`, `KP.T_Cont`, `KP.T_Lat`, `KP.T_Mean`, `KP.T_Theta`, `KP.X2_Calc`, `KP.X2_H1`, `KP.X2_Lattice`, `KP.X2_Prod`, `KP.X2_Weak`, `KP.X_Cusp`, `KP.X_Discrete`, `KP.X_Disjoint`, `KP.X_Fourier`, `KP.X_Friedrichs`, `KP.X_H3`, `KP.X_L2`, `KP.X_Meas`, `KP.X_Space`, `KP.X_Units`.
--
--   **Imports.** It imports the published bundles `Def_ArtinHecke`, `Def_ArtinHeckeLocalCoeff`, `Def_ArtinHeckePoissonLocal`, `Def_ArtinHeckeProbe`, `Def_ArtinHeckeSModel`, `Def_ArtinHeckeTheta`, `Def_DedekindDomain_Completion_BaseChange`, `Def_ExtCitation_LocalLevelResidues`, `Def_IsDedekindDomain_FiniteUnitIdeles`, `Def_IsDedekindDomain_FiniteUnitIdelesOutside`, `Def_LanglandsTunnell_ArtinCoreCTM`, `Def_M4aHerbrand_GenuineDescent`, `Def_M4aHerbrand_IdeleClassVocab`, `Def_M4aHerbrand_SIdeleClassGroup`, `Def_NormIndex_AdmissibleExpOfDegree`, `Def_NumberField_ArchimedeanIdeleModule`, `Def_NumberField_PlaceDecompositionAction` and `Def_NumberField_TateGlobalZeta`; the bundles `ArtinKPB004`, `ArtinKPB012`, `ArtinKPB013` and `ArtinKPB014` of this split; the published statements `ArtinKP.A.kappa_mul_of_mem_Gamma`, `ArtinKP.B.summable_kTerm_of_two_lt_re`, `ArtinKP.X.X.coreL2_injective`, `ArtinKP.X.X.dense_range_coreL2`, `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreL2_coreLap_self`, `ArtinKP.X.X.inner_coreLap_coreL2`, `ArtinKP.X.X.isPOU_pou` and `ArtinKP.X.X.tsum_indicator_box_le_boxMult`.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB016`; the statements `ArtinKP.B1.PairClass.exists_top`, `ArtinKP.B1.Tinf_le`, `ArtinKP.B1.lintegral_G_pow_lt_top`, `ArtinKP.B1.summable_sHt_rpow`, `ArtinKP.B.continuous_eis`, `ArtinKP.B.eis_eq_add_tsum_Tfun`, `ArtinKP.B.fourier_coeff`, `ArtinKP.B.tsum_lintegral_hI_ne_top`, `ArtinKP.C5.differentiableOn_functional_resPart`, `ArtinKP.C5.exists_norm_hpart_le`, `ArtinKP.C5.exists_single`, `ArtinKP.C5.l2Rep_src`, `ArtinKP.C5.lap_upart`, `ArtinKP.C5.norm_upart_le`, `ArtinKP.C5.smooth_src`, `ArtinKP.C5.tendsto_ray_functional_resPart_theta`, `ArtinKP.G2a.jac_bound`, `ArtinKP.GK.tau_eq_zero_of_theta`, `ArtinKP.GL.eisEigen_of_two_lt_re`, `ArtinKP.N.coeff_resPart_add_hInt`, `ArtinKP.N.differentiable_hInt`, `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray`, `ArtinKP.N.lift_theta_translate`, `ArtinKP.RC.exists_compact_top_le`, `ArtinKP.RC.exists_isWeakSol_of_lap_eq`, `ArtinKP.RC.exists_single`, `ArtinKP.RC.grad2_chi_le`, `ArtinKP.RC.lintegral_G_pow_lt_top`, `ArtinKP.RC.smooth_chi`, `ArtinKP.T.HasCoefT.smulFun`, `ArtinKP.T.coeffFunctional_theta_twist_eq`, `ArtinKP.T.differentiableOn_Afun`, `ArtinKP.T.hasCoef_transLat`, `ArtinKP.T.hasResOn_kubota_aSer`, `ArtinKP.T.hasSeed`, `ArtinKP.T.integral_theta_of_hasCoef`, `ArtinKP.T.integral_theta_of_hasCoefT`, `ArtinKP.T.resSlit_add_of_seed`, `ArtinKP.T.resSlit_mul_of_seed`, `ArtinKP.T.tau_smulFun`, `ArtinKP.T.tendsto_ray_Afun` and `ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff`; the proofs of `ArtinKP.B1.PairClass.exists_top`, `ArtinKP.B1.Tinf_le`, `ArtinKP.B1.lintegral_G_pow_lt_top`, `ArtinKP.B1.summable_sHt_rpow`, `ArtinKP.B.continuous_eis`, `ArtinKP.B.eis_eq_add_tsum_Tfun`, `ArtinKP.B.fourier_coeff`, `ArtinKP.B.tsum_lintegral_hI_ne_top`, `ArtinKP.C5.differentiableOn_functional_resPart`, `ArtinKP.C5.exists_norm_hpart_le`, `ArtinKP.C5.exists_single`, `ArtinKP.C5.l2Rep_src`, `ArtinKP.C5.lap_upart`, `ArtinKP.C5.norm_upart_le`, `ArtinKP.C5.quotVol_lt_top`, `ArtinKP.C5.smooth_src`, `ArtinKP.C5.tendsto_ray_functional_resPart_theta`, `ArtinKP.GL.eisEigen_of_two_lt_re`, `ArtinKP.N2.lintegral_lift_pou_ne_top`, `ArtinKP.N.coeff_resPart_add_hInt`, `ArtinKP.N.differentiable_hInt`, `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray`, `ArtinKP.RC.exists_compact_top_le`, `ArtinKP.RC.exists_isWeakSol_of_lap_eq`, `ArtinKP.RC.exists_single`, `ArtinKP.RC.grad2_chi_le`, `ArtinKP.RC.lintegral_G_pow_lt_top`, `ArtinKP.RC.smooth_chi`, `ArtinKP.T.HasCoefT.smulFun`, `ArtinKP.T.differentiableOn_Afun`, `ArtinKP.T.hasCoef_transLat`, `ArtinKP.T.hasResOn_kubota_aSer`, `ArtinKP.T.hasSeed`, `ArtinKP.T.integral_theta_of_hasCoef`, `ArtinKP.T.integral_theta_of_hasCoefT`, `ArtinKP.T.resSlit_add_of_seed`, `ArtinKP.T.resSlit_mul_of_seed`, `ArtinKP.T.tau_smulFun`, `ArtinKP.T.tendsto_ray_Afun`, `ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff`, `ArtinKP.X.X.ims`, `ArtinKP.X.X.integrable_pou_mul` and `ArtinKP.X.X.mem_core_of_support`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

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
import Definitions.Def_ArtinKPB004
import Definitions.Def_ArtinKPB012
import Definitions.Def_ArtinKPB013
import Definitions.Def_ArtinKPB014
import Theorems.Thm_ArtinKP_A_kappa_mul_of_mem_Gamma
import Theorems.Thm_ArtinKP_B_summable_kTerm_of_two_lt_re
import Theorems.Thm_ArtinKP_X_X_coreL2_injective
import Theorems.Thm_ArtinKP_X_X_dense_range_coreL2
import Theorems.Thm_ArtinKP_X_X_inner_coreL2_coreLap
import Theorems.Thm_ArtinKP_X_X_inner_coreL2_coreLap_self
import Theorems.Thm_ArtinKP_X_X_inner_coreLap_coreL2
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.A_Kubota
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-A: the Kubota symbol on `SL₂(R)`, `R = SInt 𝔪`

* `kappa ι 𝔪 γ = (d/c)⁻¹` (`1` if `c = 0`), with `(d/c) = cubicExt`.
* `sigmaS P 𝔪 g₁ g₂ = (X(g₁g₂)/X(g₁), X(g₁g₂)/X(g₂))_S` on rational matrices.
* `kappa_mul` (Lemma A5): `κ(γ₁γ₂) = κ(γ₁) κ(γ₂) σ_S(γ₁,γ₂)⁻¹`.

  **Orientation.**  With the symbols oriented by `CubicPkg.tame` the exponent is `ε = -1`
  (equivalently `ε = +1` for the opposite pairing `(b,a)_S`).  It is forced: for
  `γ₁ = diag(ε₁⁻¹, ε₁)` with an `S`-unit `ε₁`, and `c₂ ≠ 0`,
  `κ(γ₁γ₂)/κ(γ₂) = (ε₁/c₂)⁻¹ = (c₂, ε₁)_S⁻¹ = σ_S(γ₁, γ₂)⁻¹` by the unit law.
* `sigmaS_eq_one`: `σ_S(g₁, g₂) = 1` as soon as `a₂`, `d₁` and `d₃` lie in the radical of `(·,·)_S`.
* `Gamma 𝔪 𝔫`: the image in `SL₂(R)` of the principal congruence subgroup of `SL₂(𝓞 F)` of level
  `𝔫`; `kappa_mul_of_mem_Gamma` (Corollary A6): `κ` is multiplicative on `Γ(𝔫)` for `𝔫 ≤ 𝔪^N`,
  `N ≥ 1` any deep level of the package (`CubicPkg.IsDeepLevel`); `kappaHom`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots Matrix

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Triviality of `σ_S` on deep matrices -/

/-! ### The principal congruence subgroup and Corollary A6 -/

theorem kappa_one (ι : F →+* ℂ) : kappa ι 𝔪 1 = 1 := by
  simp [kappa]

/-- `κ` as a monoid homomorphism on `Γ(𝔫)`. -/
def kappaHom (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N)
    {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≤ 𝔪 ^ N) : Gamma 𝔪 𝔫 →* ℂ where
  toFun γ := kappa ι 𝔪 γ
  map_one' := kappa_one ι
  map_mul' γ₁ γ₂ := kappa_mul_of_mem_Gamma ι P hG hz6 hN1 hN h𝔫 γ₁.2 γ₂.2

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol
/-! # WP-X, file 1: one factor — hyperbolic 3-space and the action of `SL(2,ℂ)`

`H3 = {(x, v) : ℂ × ℝ | 0 < v}` with the quaternionic Möbius action
`g • (x, v) = (((a x + b) conj(c x + d) + a conj(c) v²) / D, v / D)`,
`D = |c x + d|² + |c|² v²`.  The action axioms are proved through the quaternion `x + v j`:
`a P + b = (g • P) (c P + d)` in `ℍ[ℝ]`.
-/

open scoped MatrixGroups Quaternion ComplexConjugate

namespace ArtinKP.X

noncomputable section

namespace H3

instance instT2Space : T2Space H3 := inferInstanceAs (T2Space {p : ℂ × ℝ // 0 < p.2})

end H3

open H3

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Meas
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X, file 2: the invariant measure `dx dv / v³` on `H3`

`H3.vol` is the comap to `H3` of `(volume.restrict {v > 0}).withDensity v⁻³` on `ℂ × ℝ`.
Invariance under `SL(2,ℂ)` is proved on the generators `n(b)` and `w` (the Weyl element acts by
the Euclidean inversion followed by `x ↦ -conj x`), and `SL(2,ℂ)` is generated by them.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set

namespace ArtinKP.X

noncomputable section

/-! ### The Euclidean inversion -/

/-! ### The measure on `H3` -/

/-! ### Regularity of the action -/

instance instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 : ContinuousConstSMul (SL(2, ℂ)) H3 := ⟨continuous_mob⟩

/-! ### Generators -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace X

/-- The height `ht P = ∏_w v_w`. -/
def ht (P : X F) : ℝ := ∏ w, P.v w

/-- The denominator of the pair `(c, d) ∈ F²` at `P`: `∏_w (|c_w x_w + d_w|² + |c_w|² v_w²)`. -/
def pairDen (c d : F) (P : X F) : ℝ := ∏ w, H3.rowDen (w.embedding c) (w.embedding d) (P w)

/-- The pair height `I_{(c,d)}(P) = ∏_w v_w / (|c_w x_w + d_w|² + |c_w|² v_w²)`. -/
def pairHt (c d : F) (P : X F) : ℝ := ht P / pairDen c d P

end X

/-! ### Topology and measure -/

instance instContinuousConstSMulGinfX : ContinuousConstSMul (Ginf F) (X F) :=
  ⟨fun g => continuous_pi fun w => (continuous_const_smul (g w)).comp (continuous_apply w)⟩

instance instContinuousConstSMulSpecialLinearGroupFinOfNatNatX : ContinuousConstSMul (SL(2, F)) (X F) :=
  ⟨fun γ => continuous_const_smul (sigma F γ)⟩

instance instSigmaFiniteXVol : SigmaFinite (X.vol F) := by unfold X.vol; infer_instance

instance instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol : SMulInvariantMeasure (SL(2, F)) (X F) (X.vol F) :=
  ⟨fun γ s hs => (measurePreserving_smul γ).measure_preimage hs.nullMeasurableSet⟩

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

instance instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX : ContinuousConstSMul (SL(2, 𝓞 F)) (X F) :=
  ⟨fun γ => continuous_const_smul (intSL F γ)⟩

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Units
/-! # WP-X, file 10: Dirichlet's unit theorem and the cusp section

The unit lattice is cocompact in the trace-zero hyperplane of the logarithmic space, hence:
there is `C ≥ 1` such that for every `v ∈ (ℝ_{>0})^r` there is a unit `ε` with all the numbers
`|ε_w|² v_w` within the ratio `C` of each other (`exists_unit_balanced`).  For `X` this says that
every point is `diag(ε, ε⁻¹)`-equivalent to one with balanced heights; in particular the
norm-one slice `{∏ v_w = 1}` modulo units is covered by the compact cube `[C⁻¹, C]^r`
(`exists_unit_smul_balanced`, `balanced_bounds`).  Only place where the unit rank enters.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The diagonal matrix `diag(ε, ε⁻¹)` of a unit. -/
def unitDiag (ε : (𝓞 F)ˣ) : SL(2, 𝓞 F) :=
  ⟨!![(ε : 𝓞 F), 0; 0, ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)], by simp [Matrix.det_fin_two]⟩

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Lattice
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-! # WP-B1, file 1: the lattice `𝓞_F² ⊂ ℂ^r × ℂ^r` and the Minkowski bound for the top height

`F` totally complex, `ι = InfinitePlace F`.  `emb : F →+ (ι → ℂ)` is the diagonal embedding,
`latE` the `ℝ`-basis of `ι → ℂ` given by an integral basis, `pairLattice` the `ℤ`-span of the
product basis of `(ι → ℂ) × (ι → ℂ)`; it is exactly `{(emb c, emb d) | c d ∈ 𝓞_F}` (`mem_pairLattice`).

**Lemma M** (`exists_integer_pair_pairHt_ge`): there is `c₀ > 0` such that for every `P ∈ X` some
nonzero pair `(c,d) ∈ 𝓞_F²` has `I_{(c,d)}(P) ≥ c₀`.  Proof: Minkowski's convex body theorem for the
body `{|c_w| ≤ λ/√v_w, |c_w x_w + d_w| ≤ λ√v_w}`, whose volume `(π²λ⁴)^r` does not depend on `P`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The ambient space of pairs. -/
abbrev E₂ (F : Type*) [Field F] [NumberField F] : Type _ :=
  (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ)

variable [IsTotallyComplex F]

/-- For a totally complex field the mixed space is `ι → ℂ`. -/
def mixedEquiv : mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℂ) where
  toFun y := fun w => y.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun x := (fun _ => 0, fun w => x w.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    refine Prod.ext (funext fun w => ?_) rfl
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2).elim
  right_inv x := rfl

/-- The `ℝ`-basis of `ι → ℂ` coming from an integral basis of `F`. -/
def latE : Basis (Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (InfinitePlace F → ℂ) :=
  (mixedEmbedding.latticeBasis F).map mixedEquiv

lemma latE_apply (i : Free.ChooseBasisIndex ℤ (𝓞 F)) :
    latE i = emb ((RingOfIntegers.basis F i : 𝓞 F) : F) := by
  ext w
  simp only [latE, Basis.map_apply, mixedEmbedding.latticeBasis_apply, integralBasis_apply]
  rfl

lemma emb_int_eq_sum (c : 𝓞 F) :
    emb (c : F) = ∑ i, (RingOfIntegers.basis F).repr c i • latE i := by
  conv_lhs => rw [← (RingOfIntegers.basis F).sum_repr c]
  rw [show ((∑ i, (RingOfIntegers.basis F).repr c i • RingOfIntegers.basis F i : 𝓞 F) : F) =
      ∑ i, (RingOfIntegers.basis F).repr c i • ((RingOfIntegers.basis F i : 𝓞 F) : F) by
    simp [zsmul_eq_mul], map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, latE_apply]

/-- The basis of the space of pairs. -/
def pairBasis : Basis (Free.ChooseBasisIndex ℤ (𝓞 F) ⊕ Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (E₂ F) :=
  latE.prod latE

/-- The lattice `𝓞_F² ⊂ ℂ^r × ℂ^r`. -/
def pairLattice (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F] :
    Submodule ℤ (E₂ F) := Submodule.span ℤ (Set.range (pairBasis (F := F)))

instance instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice : DiscreteTopology (pairLattice F) := by
  unfold pairLattice; infer_instance

/-! ### The Minkowski body -/

/-- The convex body `{(c,d) : |c_w| ≤ λ/√v_w, |c_w x_w + d_w| ≤ λ√v_w ∀ w}`. -/
def mkSet (P : X F) (lam : ℝ) : Set (E₂ F) :=
  {z | ∀ w, ‖z.1 w‖ ≤ lam / √(P.v w) ∧ ‖z.1 w * P.x w + z.2 w‖ ≤ lam * √(P.v w)}

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.X_Disjoint
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X, file 4: disjointness of cusp neighbourhoods

For two pairs `(c,d)`, `(c',d')` with `Δ = c d' - c' d ≠ 0`:
`I_{(c,d)}(P) · I_{(c',d')}(P) ≤ 1 / ∏_w |Δ_w|²`.  With the `S`-normalized heights
`ht^S_{(c,d)} = I_{(c,d)} / ∏_{v ∈ S} max(|c|_v, |d|_v)` and `Δ` an `S`-integer the product formula
gives `ht^S_{(c,d)} · ht^S_{(c',d')} ≤ 1`: the regions `{ht^S_{(c,d)} > 1}` of non-proportional
pairs are disjoint.  No reduction theory is used.
-/

open scoped MatrixGroups ComplexConjugate
open NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

namespace X

/-- In a totally complex field `∏_w |x_w|² = |N_{F/ℚ} x|`. -/
lemma prod_normSq_embedding [IsTotallyComplex F] (x : F) :
    ∏ w : InfinitePlace F, Complex.normSq (w.embedding x) = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [← h]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [IsTotallyComplex.mult_eq, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]

/-- A finite product over `S` dominates the full product of a function which is `≤ 1` off `S`. -/
lemma finprod_finitePlace [IsTotallyComplex F] {x : F} (hx : x ≠ 0) :
    ∏ᶠ v : FinitePlace F, v x = (∏ w : InfinitePlace F, Complex.normSq (w.embedding x))⁻¹ := by
  rw [prod_normSq_embedding, FinitePlace.prod_eq_inv_abs_norm hx]
  push_cast
  rfl

/-- The `S`-normalized pair height `I_{(c,d)}(P) / ∏_{v ∈ S} max(|c|_v, |d|_v)`. -/
def sHt (S : Finset (FinitePlace F)) (c d : F) (P : X F) : ℝ := pairHt c d P / sNorm S c d

/-- Scaling a pair: `I_{(tc,td)} = I_{(c,d)} / ∏_w |t_w|²`. -/
lemma pairHt_smul_pair (t c d : F) (P : X F) :
    pairHt (t * c) (t * d) P =
      pairHt c d P / ∏ w : InfinitePlace F, Complex.normSq (w.embedding t) := by
  unfold pairHt pairDen
  rw [div_div, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  unfold H3.rowDen
  rw [map_mul, map_mul, mul_assoc, ← mul_add, map_mul, map_mul]
  ring

/-- The `S`-normalized height is invariant under scaling the pair by an `S`-unit. -/
theorem sHt_unit_smul [IsTotallyComplex F] (S : Finset (FinitePlace F)) {u : F} (hu : u ≠ 0)
    (hunit : ∀ v : FinitePlace F, v ∉ S → v u = 1) (c d : F) (P : X F) :
    sHt S (u * c) (u * d) P = sHt S c d P := by
  have hprod : (∏ w : InfinitePlace F, Complex.normSq (w.embedding u)) * ∏ v ∈ S, v u = 1 := by
    have h2 : ∏ᶠ v : FinitePlace F, v u = ∏ v ∈ S, v u := by
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      by_contra hvS
      exact hv (hunit v hvS)
    rw [← h2, finprod_finitePlace hu]
    exact mul_inv_cancel₀ (Finset.prod_pos fun w _ =>
      Complex.normSq_pos.mpr ((map_ne_zero _).mpr hu)).ne'
  have hsn : sNorm S (u * c) (u * d) = (∏ v ∈ S, v u) * sNorm S c d := by
    unfold sNorm
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, map_mul, mul_max_of_nonneg _ _ (apply_nonneg v u)]
  have hpos : 0 < ∏ w : InfinitePlace F, Complex.normSq (w.embedding u) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hu)
  have hpos2 : (∏ v ∈ S, v u) ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact zero_ne_one hprod
  unfold sHt
  rw [pairHt_smul_pair, hsn, div_div]
  congr 1
  rw [← mul_assoc, hprod, one_mul]

end X

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Conv
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-B1, file 2: convergence of the Eisenstein majorant over `𝓞_F`-pairs modulo units

For a family of nonzero pairs `(c,d) ∈ 𝓞_F²`, pairwise inequivalent under scaling by units,
`∑ I_{(c,d)}(P)^σ < ∞` for `σ > 2` (`summable_pairHt_rpow`).  Proof: by Dirichlet's unit theorem
every class has a representative whose local denominators are balanced; for it
`I(P) ≤ C(P) ‖(c,d)‖^{-2r}`, and the lattice sum `∑ ‖z‖^{-2rσ}` over `𝓞_F² ⊂ ℝ^{4r}` converges.

Local uniformity is obtained from the comparison `I_{(c,d)}(P) ≤ cmp P P₀ · I_{(c,d)}(P₀)`, valid for
all pairs, with `cmp · P₀` continuous (`pairHt_le_cmp`, `continuous_cmp`,
`exists_summable_majorant`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

/-- The local comparison constant: `|c|², |d|² ≤ kap Q · (|c x + d|² + |c|² v²)`. -/
def kap (Q : H3) : ℝ := 2 + (1 + 2 * ‖Q.x‖ ^ 2) / Q.v ^ 2

variable {F : Type*} [Field F] [NumberField F]

/-- The comparison factor between two points of `X`. -/
def cmp (P P₀ : X F) : ℝ :=
  ∏ w, P.v w / P₀.v w * ((2 * ‖P₀.x w‖ ^ 2 + P₀.v w ^ 2 + 2) * kap (P w))

/-- `∑_w kap (P w)`. -/
def kapX (P : X F) : ℝ := ∑ w, kap (P w)

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Pairs
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-B1, file 4: primitive pairs of `S`-integers modulo `S`-units; convergence and top height

`S` is any finite set of finite places of the totally complex field `F`; `IsSInt S`, `IsSUnit S`
describe the ring `R = 𝓞_S` and its units inside `F`.  `SPair S` = primitive pairs of `R²`
(`a c + b d = 1` solvable in `R`), `PairClass S = SPair S / U_S`, `PairClass.ht p P = ht_p(P)` the
`S`-normalized height, `PairClass.act` the right action of `SL₂(𝓞_F)`:
`(p.act γ).ht P = p.ht (γ • P)`.

* `summable_sHt_rpow`, `exists_summable_majorant_sHt`: (B1) for any family of pairwise
  `U_S`-inequivalent nonzero pairs of `S`-integers (primitive or not), `σ > 2`.
* `PairClass.summable_ht_rpow`, `PairClass.exists_summable_majorant`, `PairClass.exists_max_ht`.
* `PairClass.exists_ht_ge` (Lemma M): `sup_p ht_p(P) ≥ c₀ > 0`, under `SBezout S` (true when `R` is a PID).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

variable {S : Finset (FinitePlace F)}

lemma finitePlace_int_le_one (v : FinitePlace F) (a : 𝓞 F) : v (a : F) ≤ 1 := by
  rw [← FinitePlace.mk_maximalIdeal v, FinitePlace.mk_apply]
  exact FinitePlace.norm_le_one _ _ _

lemma isSInt_int (a : 𝓞 F) : IsSInt S (a : F) := fun v _ => finitePlace_int_le_one v a

lemma IsSInt.sub {a b : F} (ha : IsSInt S a) (hb : IsSInt S b) : IsSInt S (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

lemma isSUnit_one : IsSUnit S (1 : F) := ⟨one_ne_zero, fun v _ => by simp⟩

lemma IsSUnit.mul {u u' : F} (hu : IsSUnit S u) (hu' : IsSUnit S u') : IsSUnit S (u * u') :=
  ⟨mul_ne_zero hu.1 hu'.1, fun v hv => by rw [map_mul, hu.2 v hv, hu'.2 v hv, mul_one]⟩

lemma isSUnit_unit (ε : (𝓞 F)ˣ) : IsSUnit S ((ε : 𝓞 F) : F) := by
  refine ⟨by simp, fun v _ => le_antisymm (finitePlace_int_le_one v _) ?_⟩
  have h1 := finitePlace_int_le_one v ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  have h2 : v ((ε : 𝓞 F) : F) * v (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    rw [← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel]; simp
  have h3 : 0 ≤ v ((ε : 𝓞 F) : F) := apply_nonneg v _
  nlinarith

/-! ### The raw right action of `SL₂(𝓞_F)` on pairs -/

/-- `(c, d) ↦ (c, d) γ`. -/
def actF (q : F × F) (γ : SL(2, 𝓞 F)) : F × F :=
  (q.1 * (γ 0 0 : 𝓞 F) + q.2 * (γ 1 0 : 𝓞 F), q.1 * (γ 0 1 : 𝓞 F) + q.2 * (γ 1 1 : 𝓞 F))

lemma actF_one (q : F × F) : actF q 1 = q := by
  simp [actF]

lemma actF_mul (q : F × F) (γ₁ γ₂ : SL(2, 𝓞 F)) : actF q (γ₁ * γ₂) = actF (actF q γ₁) γ₂ := by
  simp only [actF, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine Prod.ext ?_ ?_ <;> push_cast <;> ring

lemma actF_smul (u : F) (q : F × F) (γ : SL(2, 𝓞 F)) :
    actF (u * q.1, u * q.2) γ = (u * (actF q γ).1, u * (actF q γ).2) := by
  simp only [actF]; refine Prod.ext ?_ ?_ <;> ring

/-! ### Primitive pairs and pair classes -/

namespace SPair

/-- The pair `(0, 1)` (the cusp at infinity). -/
def inf (S : Finset (FinitePlace F)) : SPair S :=
  ⟨0, 1, isSInt_zero, isSInt_one, 0, 1, isSInt_zero, isSInt_one, by simp⟩

/-- Right action of `SL₂(𝓞_F)`. -/
def act (p : SPair S) (γ : SL(2, 𝓞 F)) : SPair S where
  c := (actF (p.c, p.d) γ).1
  d := (actF (p.c, p.d) γ).2
  hc := (p.hc.mul (isSInt_int _)).add (p.hd.mul (isSInt_int _))
  hd := (p.hc.mul (isSInt_int _)).add (p.hd.mul (isSInt_int _))
  prim := by
    obtain ⟨a, b, ha, hb, hab⟩ := p.prim
    have hdet : ((γ 0 0 : 𝓞 F) : F) * (γ 1 1 : 𝓞 F) - (γ 0 1 : 𝓞 F) * (γ 1 0 : 𝓞 F) = 1 := by
      have h := γ.det_coe
      rw [Matrix.det_fin_two] at h
      exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) h
    refine ⟨a * (γ 1 1 : 𝓞 F) - b * (γ 0 1 : 𝓞 F), b * (γ 0 0 : 𝓞 F) - a * (γ 1 0 : 𝓞 F),
      (ha.mul (isSInt_int _)).sub (hb.mul (isSInt_int _)),
      (hb.mul (isSInt_int _)).sub (ha.mul (isSInt_int _)), ?_⟩
    simp only [actF]
    linear_combination (a * p.c + b * p.d) * hdet + hab

/-- Equivalence modulo `S`-units. -/
instance setoid (S : Finset (FinitePlace F)) : Setoid (SPair S) where
  r p q := ∃ u : F, IsSUnit S u ∧ q.c = u * p.c ∧ q.d = u * p.d
  iseqv := by
    refine ⟨fun p => ⟨1, isSUnit_one, by simp, by simp⟩, ?_, ?_⟩
    · rintro p q ⟨u, hu, h1, h2⟩
      exact ⟨u⁻¹, hu.inv, by rw [h1, inv_mul_cancel_left₀ hu.1], by rw [h2, inv_mul_cancel_left₀ hu.1]⟩
    · rintro p q r ⟨u, hu, h1, h2⟩ ⟨u', hu', h1', h2'⟩
      exact ⟨u' * u, hu'.mul hu, by rw [h1', h1, mul_assoc], by rw [h2', h2, mul_assoc]⟩

lemma act_equiv {p q : SPair S} (h : p ≈ q) (γ : SL(2, 𝓞 F)) : p.act γ ≈ q.act γ := by
  obtain ⟨u, hu, h1, h2⟩ := h
  refine ⟨u, hu, ?_, ?_⟩
  · change (actF (q.c, q.d) γ).1 = u * (actF (p.c, p.d) γ).1
    rw [h1, h2, actF_smul u (p.c, p.d)]
  · change (actF (q.c, q.d) γ).2 = u * (actF (p.c, p.d) γ).2
    rw [h1, h2, actF_smul u (p.c, p.d)]

end SPair

/-- Pair classes `R²_prim / U_S`. -/
abbrev PairClass (S : Finset (FinitePlace F)) : Type _ := Quotient (SPair.setoid S)

namespace PairClass

/-- The class of `(0, 1)`. -/
def inf (S : Finset (FinitePlace F)) : PairClass S := ⟦SPair.inf S⟧

/-- Right action of `SL₂(𝓞_F)` on pair classes. -/
def act (p : PairClass S) (γ : SL(2, 𝓞 F)) : PairClass S :=
  Quotient.map (fun q : SPair S => q.act γ) (fun _ _ h => SPair.act_equiv h γ) p

lemma act_mk (q : SPair S) (γ : SL(2, 𝓞 F)) : act (⟦q⟧ : PairClass S) γ = ⟦q.act γ⟧ := rfl

lemma act_one (p : PairClass S) : p.act 1 = p := by
  induction p using Quotient.inductionOn with
  | _ q =>
    rw [act_mk]
    congr 1
    ext
    · exact congrArg Prod.fst (actF_one (q.c, q.d))
    · exact congrArg Prod.snd (actF_one (q.c, q.d))

lemma act_mul (p : PairClass S) (γ₁ γ₂ : SL(2, 𝓞 F)) : p.act (γ₁ * γ₂) = (p.act γ₁).act γ₂ := by
  induction p using Quotient.inductionOn with
  | _ q =>
    rw [act_mk, act_mk, act_mk]
    congr 1
    ext
    · exact congrArg Prod.fst (actF_mul (q.c, q.d) γ₁ γ₂)
    · exact congrArg Prod.snd (actF_mul (q.c, q.d) γ₁ γ₂)

/-- The action of `γ` as a permutation of the pair classes. -/
def actEquiv (γ : SL(2, 𝓞 F)) : PairClass S ≃ PairClass S where
  toFun p := p.act γ
  invFun p := p.act γ⁻¹
  left_inv p := by
    change (p.act γ).act γ⁻¹ = p
    rw [← act_mul, mul_inv_cancel, act_one]
  right_inv p := by
    change (p.act γ⁻¹).act γ = p
    rw [← act_mul, inv_mul_cancel, act_one]

variable [IsTotallyComplex F]

/-- The `S`-normalized height `ht_p(P)` of a pair class. -/
def ht (p : PairClass S) (P : X F) : ℝ :=
  Quotient.liftOn p (fun q : SPair S => X.sHt S q.c q.d P) (by
    rintro q q' ⟨u, hu, h1, h2⟩
    rw [h1, h2, X.sHt_unit_smul S hu.1 hu.2])

end PairClass

/-! ### (B1) for families of `S`-integer pairs -/

variable [IsTotallyComplex F]

/-! ### Lemma M for pair classes -/

/-- `R = 𝓞_S` is a Bezout domain in the form needed: every nonzero pair of `S`-integers is an
`S`-integer multiple of a primitive pair.  Holds when `R` is a PID. -/
def SBezout (S : Finset (FinitePlace F)) : Prop :=
  ∀ c d : F, IsSInt S c → IsSInt S d → (c ≠ 0 ∨ d ≠ 0) →
    ∃ t : F, IsSInt S t ∧ ∃ p : SPair S, c = t * p.c ∧ d = t * p.d

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Cusp
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-B1, file 5: the series without the cusp at infinity — invariance and Harnack in `x`

`Tinf S σ P = ∑_{p ≠ ∞} ht_p(P)^σ` (all pair classes except that of `(0,1)`).  It is invariant under
upper triangular elements of `SL₂(𝓞_F)` (`Tinf_smul_of_upper`): translations `nInt β` and diagonal
units.  Harnack inequality in the horizontal variable (`Tinf_harnack`): moving `x_w` by at most `v_w`
changes every pair height by a factor `≤ 3^r`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### Continuity -/

/-! ### Translations -/

/-- The translation `n(β) = [[1, β], [0, 1]]`. -/
def nInt (β : 𝓞 F) : SL(2, 𝓞 F) := ⟨!![1, β; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma nInt_coe (β : 𝓞 F) : (nInt β : Matrix (Fin 2) (Fin 2) (𝓞 F)) = !![1, β; 0, 1] := rfl

lemma nInt_add (β β' : 𝓞 F) : nInt (β + β') = nInt β * nInt β' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nInt_coe, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma nInt_zero : nInt (0 : 𝓞 F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nInt_coe]

variable {S : Finset (FinitePlace F)}

/-- A primitive pair with `c = 0` is the cusp at infinity. -/
lemma SPair.c_ne_zero {q : SPair S} (h : (⟦q⟧ : PairClass S) ≠ PairClass.inf S) : q.c ≠ 0 := by
  intro hc
  apply h
  symm
  obtain ⟨a, b, ha, hb, hab⟩ := q.prim
  rw [hc, mul_zero, zero_add] at hab
  have hd0 : q.d ≠ 0 := by rintro h0; rw [h0, mul_zero] at hab; exact zero_ne_one hab
  refine Quotient.sound ⟨q.d, ⟨hd0, fun v hv => ?_⟩, ?_, ?_⟩
  · have h1 := hb v hv
    have h2 := q.hd v hv
    have h3 : v b * v q.d = 1 := by rw [← map_mul, hab, map_one]
    have h4 : 0 ≤ v b := apply_nonneg v _
    have h5 : 0 ≤ v q.d := apply_nonneg v _
    nlinarith
  · change q.c = q.d * 0
    rw [hc, mul_zero]
  · change q.d = q.d * 1
    rw [mul_one]

/-- Upper triangular matrices fix the cusp at infinity. -/
lemma PairClass.act_inf_of_upper {γ : SL(2, 𝓞 F)} (h : γ 1 0 = 0) :
    (PairClass.inf S).act γ = PairClass.inf S := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  refine Quotient.sound ⟨((Units.mkOfMulEqOne _ _ hdet : (𝓞 F)ˣ) : 𝓞 F),
    isSUnit_unit (Units.mkOfMulEqOne _ _ hdet), ?_, ?_⟩
  · change (0 : F) = _ * (actF (0, 1) γ).1
    simp [actF, h]
  · change (1 : F) = _ * (actF (0, 1) γ).2
    simp only [actF, zero_mul, one_mul, zero_add, Units.val_mkOfMulEqOne]
    exact_mod_cast (congrArg (fun z : 𝓞 F => (z : F)) hdet).symm

variable [IsTotallyComplex F]

/-- `∑_{p ≠ ∞} ht_p(P)^σ`. -/
def Tinf (S : Finset (FinitePlace F)) (σ : ℝ) (P : X F) : ℝ :=
  ∑' p : {p : PairClass S // p ≠ PairClass.inf S}, p.1.ht P ^ σ

/-- The permutation of the classes `≠ ∞` induced by an upper triangular matrix. -/
def upperEquiv {γ : SL(2, 𝓞 F)} (h : γ 1 0 = 0) :
    {p : PairClass S // p ≠ PairClass.inf S} ≃ {p : PairClass S // p ≠ PairClass.inf S} :=
  (PairClass.actEquiv γ).subtypeEquiv fun p => by
    change p ≠ PairClass.inf S ↔ p.act γ ≠ PairClass.inf S
    refine not_congr ⟨fun hp => by rw [hp, PairClass.act_inf_of_upper h], fun hp => ?_⟩
    have := (PairClass.actEquiv (S := S) γ).injective
      (a₁ := p) (a₂ := PairClass.inf S) (by
        change p.act γ = (PairClass.inf S).act γ
        rw [hp, PairClass.act_inf_of_upper h])
    exact this

/-! ### Harnack in the horizontal variable -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Const
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-! # WP-B1, file 6: the constant term of `Tinf` (Lemma K) by unfolding and scaling

`constTerm S σ v = ∫_{ℂ^r/𝓞} ∑_{p ≠ ∞} ht_p(x, v)^σ dx` (integral over the fundamental cell `fundD`).
Unfolding over the free action of the translations `n(β)`, `β ∈ 𝓞_F`, on the classes `≠ ∞`
(`orbEquiv`) turns it into a sum of integrals over all of `ℂ^r`, each of which scales exactly like
`ht(v)^{2-σ}` (`lintegral_sHt_scale`).  Hence `constTerm S σ v = ht(v)^{2-σ} · constTerm S σ 1`
(`constTerm_scale`), and `constTerm S σ 1 < ∞` by the locally uniform convergence (`constTerm_one_lt_top`).
No zeta function and no strong approximation are needed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

variable [IsTotallyComplex F]

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

/-- The lattice `emb(𝓞_F) ⊂ ℂ^r`. -/
def latSub (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F] :
    AddSubgroup (InfinitePlace F → ℂ) :=
  (Submodule.span ℤ (Set.range (latE (F := F)))).toAddSubgroup

/-- A fundamental cell of `ℂ^r / 𝓞_F`. -/
def fundD (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F] :
    Set (InfinitePlace F → ℂ) := ZSpan.fundamentalDomain (latE (F := F))

lemma mem_latSub {x : InfinitePlace F → ℂ} : x ∈ latSub F ↔ ∃ β : 𝓞 F, x = emb (β : F) := by
  change x ∈ Submodule.span ℤ (Set.range (latE (F := F))) ↔ _
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact ⟨RingOfIntegers.basis F i, latE_apply i⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by simp⟩
    | smul n x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      have h : ((n • c : 𝓞 F) : F) = n • (c : F) := by simp [zsmul_eq_mul]
      exact ⟨n • c, by rw [h, map_zsmul]⟩
  · rintro ⟨c, rfl⟩
    rw [emb_int_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- `𝓞_F ≃ emb(𝓞_F)`. -/
def latEquiv : 𝓞 F ≃ latSub F :=
  Equiv.ofBijective (fun β => ⟨emb (β : F), mem_latSub.mpr ⟨β, rfl⟩⟩) ⟨by
    intro a b h
    have h' : emb (a : F) = emb (b : F) := congrArg Subtype.val h
    have := emb_eq_zero (by rw [map_sub, h', sub_self] : emb ((a : F) - (b : F)) = 0)
    exact RingOfIntegers.ext (sub_eq_zero.mp this), by
    rintro ⟨x, hx⟩
    obtain ⟨β, rfl⟩ := mem_latSub.mp hx
    exact ⟨β, rfl⟩⟩

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub : Countable (latSub F) :=
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  latEquiv.symm.injective.countable

/-! ### Scaling -/

variable {S : Finset (FinitePlace F)}

/-- The point with all heights equal to one. -/
abbrev mk1 (y : InfinitePlace F → ℂ) : X F := X.mk y (fun _ => 1) (fun _ => one_pos)

/-! ### Orbits of the translations on the classes `≠ ∞` -/

lemma nInt_upper (β : 𝓞 F) : (nInt β) 1 0 = 0 := by simp [nInt_coe]

/-- The translations act freely on the classes `≠ ∞`. -/
lemma act_nInt_free (p : {p : PairClass S // p ≠ PairClass.inf S}) (β : 𝓞 F)
    (h : p.1.act (nInt β) = p.1) : β = 0 := by
  obtain ⟨p, hp⟩ := p
  induction p using Quotient.inductionOn with
  | _ q =>
    have hc := SPair.c_ne_zero hp
    obtain ⟨u, hu, h1, h2⟩ := Quotient.exact h
    change q.c = u * (actF (q.c, q.d) (nInt β)).1 at h1
    change q.d = u * (actF (q.c, q.d) (nInt β)).2 at h2
    simp only [actF, nInt_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1 h2
    push_cast at h1 h2
    have hu1 : u = 1 := by
      have : q.c * (u - 1) = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc
      · exact sub_eq_zero.mp h
    rw [hu1] at h2
    have : q.c * (β : F) = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc
    · exact_mod_cast h

/-- The orbit relation of the translations on the classes `≠ ∞`. -/
def transSetoid (S : Finset (FinitePlace F)) : Setoid {p : PairClass S // p ≠ PairClass.inf S} where
  r p q := ∃ β : 𝓞 F, q.1 = p.1.act (nInt β)
  iseqv := by
    refine ⟨fun p => ⟨0, by rw [nInt_zero, PairClass.act_one]⟩, ?_, ?_⟩
    · rintro p q ⟨β, h⟩
      exact ⟨-β, by rw [h, ← PairClass.act_mul, ← nInt_add, add_neg_cancel, nInt_zero,
        PairClass.act_one]⟩
    · rintro p q r ⟨β, h⟩ ⟨β', h'⟩
      exact ⟨β + β', by rw [h', h, ← PairClass.act_mul, ← nInt_add]⟩

/-- Classes `≠ ∞` = (translation orbits) × `𝓞_F`. -/
def orbEquiv (S : Finset (FinitePlace F)) :
    Quotient (transSetoid S) × 𝓞 F ≃ {p : PairClass S // p ≠ PairClass.inf S} :=
  Equiv.ofBijective (fun z => upperEquiv (nInt_upper z.2) z.1.out) ⟨by
    rintro ⟨ω, β⟩ ⟨ω', β'⟩ h
    have h1 : ω.out.1.act (nInt β) = ω'.out.1.act (nInt β') := congrArg Subtype.val h
    have h2 : ω'.out.1 = ω.out.1.act (nInt (β - β')) := by
      rw [sub_eq_add_neg, nInt_add, PairClass.act_mul, h1, ← PairClass.act_mul, ← nInt_add,
        add_neg_cancel, nInt_zero, PairClass.act_one]
    have hω : ω = ω' := by
      rw [← Quotient.out_eq ω, ← Quotient.out_eq ω']
      exact Quotient.sound ⟨β - β', h2⟩
    subst hω
    have := act_nInt_free ω.out (β - β') h2.symm
    rw [sub_eq_zero.mp this], by
    intro p
    obtain ⟨β, hβ⟩ := Quotient.mk_out (s := transSetoid S) p
    exact ⟨(⟦p⟧, β), Subtype.ext hβ.symm⟩⟩

/-! ### The constant term -/

/-- The constant term of `Tinf`: `∫_{ℂ^r/𝓞} ∑_{p ≠ ∞} ht_p(x, v)^σ dx`. -/
def constTerm (S : Finset (FinitePlace F)) (σ : ℝ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) : ℝ≥0∞ :=
  ∫⁻ x in fundD F, ∑' p : {p : PairClass S // p ≠ PairClass.inf S},
    ENNReal.ofReal (p.1.ht (X.mk x v hv) ^ σ)

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Bound
/-! # WP-B1, file 7: the majorant bound away from the top cusp (item 2)

`Tinf_le`: for `σ > 2` there is `K` with
`∑_{p ≠ ∞} ht_p(Q)^σ ≤ K · (ht(Q)^{2-σ} + ht(Q)^{-σ})` for **all** `Q ∈ X`.

Proof (MATH2 §1.3, with the average taken in `x` only): Harnack in `x` over the polydisc of radii
`v_w`, covering of the polydisc by translates of the fundamental cell (a volume count), the
constant term `constTerm v = ht(v)^{2-σ} constTerm 1 < ∞`, and Dirichlet's unit theorem to make
`v` balanced.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-- The polydisc with centre `x` and radii `r`. -/
def polydisc (x : InfinitePlace F → ℂ) (r : InfinitePlace F → ℝ) : Set (InfinitePlace F → ℂ) :=
  Set.pi univ fun w => Metric.closedBall (x w) (r w)

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_G
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-B1, file 8: all cusps; boundedness of `G` (Proposition B of MATH2 §1.3)

* `IsSMat S τ`: `τ ∈ SL₂(F)` with `S`-integral entries (`SL₂(R)`); `PairClass.actR` its right action
  on pair classes; heights change by at most the factor `cS S τ` / `cS S τ⁻¹`.
* `Tcusp S σ p₀ P = ∑_{p ≠ p₀} ht_p(P)^σ`; `Tcusp_le`: under `FiniteCusps S` there are `K`, `C` with
  `Tcusp S σ p₀ P ≤ K (h^{2-σ} + h^{-σ})` for some `h ≥ ht_{p₀}(P)/C`.
* `G S σ P = ∑_p 1[ht_p(P) < 3] ht_p(P)^σ` is `SL₂(𝓞_F)`-invariant and bounded on `X` (`G_le`), under
  `SBezout S` (Lemma M) and `FiniteCusps S` (finitely many `SL₂(𝓞_F)`-orbits of pair classes).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {S : Finset (FinitePlace F)}

/-! ### The action of `SL₂(R)` -/

/-- `τ ∈ SL₂(R)`: a matrix of `SL₂(F)` with `S`-integral entries. -/
def IsSMat (S : Finset (FinitePlace F)) (τ : SL(2, F)) : Prop := ∀ i j, IsSInt S (τ i j)

lemma IsSMat.inv {τ : SL(2, F)} (h : IsSMat S τ) : IsSMat S τ⁻¹ := by
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · simpa using h 1 1
  · simpa using (h 0 1).neg
  · simpa using (h 1 0).neg
  · simpa using h 0 0

/-- `(c, d) ↦ (c, d) τ` for `τ ∈ SL₂(F)`. -/
def actFF (q : F × F) (τ : SL(2, F)) : F × F :=
  (q.1 * τ 0 0 + q.2 * τ 1 0, q.1 * τ 0 1 + q.2 * τ 1 1)

lemma actFF_one (q : F × F) : actFF q 1 = q := by simp [actFF]

lemma actFF_mul (q : F × F) (τ₁ τ₂ : SL(2, F)) : actFF q (τ₁ * τ₂) = actFF (actFF q τ₁) τ₂ := by
  simp only [actFF, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine Prod.ext ?_ ?_ <;> ring

lemma actFF_smul (u : F) (q : F × F) (τ : SL(2, F)) :
    actFF (u * q.1, u * q.2) τ = (u * (actFF q τ).1, u * (actFF q τ).2) := by
  simp only [actFF]; refine Prod.ext ?_ ?_ <;> ring

/-- The distortion of `‖·‖_S` by `τ`. -/
def cS (S : Finset (FinitePlace F)) (τ : SL(2, F)) : ℝ :=
  ∏ v ∈ S, max 1 (max (max (v (τ 0 0)) (v (τ 0 1))) (max (v (τ 1 0)) (v (τ 1 1))))

/-- Right action of `SL₂(R)` on primitive pairs. -/
def SPair.actR (p : SPair S) (τ : SL(2, F)) (hτ : IsSMat S τ) : SPair S where
  c := (actFF (p.c, p.d) τ).1
  d := (actFF (p.c, p.d) τ).2
  hc := (p.hc.mul (hτ 0 0)).add (p.hd.mul (hτ 1 0))
  hd := (p.hc.mul (hτ 0 1)).add (p.hd.mul (hτ 1 1))
  prim := by
    obtain ⟨a, b, ha, hb, hab⟩ := p.prim
    have hdet : τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 = 1 := by
      have h := τ.det_coe
      rwa [Matrix.det_fin_two] at h
    refine ⟨a * τ 1 1 - b * τ 0 1, b * τ 0 0 - a * τ 1 0,
      (ha.mul (hτ 1 1)).sub (hb.mul (hτ 0 1)), (hb.mul (hτ 0 0)).sub (ha.mul (hτ 1 0)), ?_⟩
    simp only [actFF]
    linear_combination (a * p.c + b * p.d) * hdet + hab

lemma SPair.actR_equiv {p q : SPair S} (h : p ≈ q) (τ : SL(2, F)) (hτ : IsSMat S τ) :
    p.actR τ hτ ≈ q.actR τ hτ := by
  obtain ⟨u, hu, h1, h2⟩ := h
  refine ⟨u, hu, ?_, ?_⟩
  · change (actFF (q.c, q.d) τ).1 = u * (actFF (p.c, p.d) τ).1
    rw [h1, h2, actFF_smul u (p.c, p.d)]
  · change (actFF (q.c, q.d) τ).2 = u * (actFF (p.c, p.d) τ).2
    rw [h1, h2, actFF_smul u (p.c, p.d)]

namespace PairClass

/-- Right action of `SL₂(R)` on pair classes. -/
def actR (p : PairClass S) (τ : SL(2, F)) (hτ : IsSMat S τ) : PairClass S :=
  Quotient.map (fun q : SPair S => q.actR τ hτ) (fun _ _ h => SPair.actR_equiv h τ hτ) p

lemma actR_mk (q : SPair S) (τ : SL(2, F)) (hτ : IsSMat S τ) :
    actR (⟦q⟧ : PairClass S) τ hτ = ⟦q.actR τ hτ⟧ := rfl

lemma actR_actR_inv (p : PairClass S) (τ : SL(2, F)) (hτ : IsSMat S τ) :
    (p.actR τ hτ).actR τ⁻¹ hτ.inv = p := by
  induction p using Quotient.inductionOn with
  | _ q =>
    rw [actR_mk, actR_mk]
    congr 1
    have h : actFF (actFF (q.c, q.d) τ) τ⁻¹ = (q.c, q.d) := by
      rw [← actFF_mul, mul_inv_cancel, actFF_one]
    ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

lemma actR_inv_actR (p : PairClass S) (τ : SL(2, F)) (hτ : IsSMat S τ) :
    (p.actR τ⁻¹ hτ.inv).actR τ hτ = p := by
  induction p using Quotient.inductionOn with
  | _ q =>
    rw [actR_mk, actR_mk]
    congr 1
    have h : actFF (actFF (q.c, q.d) τ⁻¹) τ = (q.c, q.d) := by
      rw [← actFF_mul, inv_mul_cancel, actFF_one]
    ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

/-- `actR τ` as a permutation of the pair classes. -/
def actREquiv (τ : SL(2, F)) (hτ : IsSMat S τ) : PairClass S ≃ PairClass S where
  toFun p := p.actR τ hτ
  invFun p := p.actR τ⁻¹ hτ.inv
  left_inv p := actR_actR_inv p τ hτ
  right_inv p := actR_inv_actR p τ hτ

end PairClass

variable [IsTotallyComplex F]

/-! ### The series without one cusp -/

/-- `∑_{p ≠ p₀} ht_p(P)^σ`. -/
def Tcusp (S : Finset (FinitePlace F)) (σ : ℝ) (p₀ : PairClass S) (P : X F) : ℝ :=
  ∑' p : {p : PairClass S // p ≠ p₀}, p.1.ht P ^ σ

/-- Removing the image of a class under a permutation. -/
def neEquiv (e : PairClass S ≃ PairClass S) (p₀ : PairClass S) :
    {p : PairClass S // p ≠ p₀} ≃ {p : PairClass S // p ≠ e p₀} :=
  e.subtypeEquiv fun p => not_congr e.injective.eq_iff.symm

/-- **(O) Finitely many cusps**: finitely many `τ_i ∈ SL₂(R)` such that every pair class is
`(0,1) τ_i γ` with `γ ∈ SL₂(𝓞_F)`.  (True: `SL₂(R)` is transitive on primitive pairs when `R` is a
PID, and `𝒫/SL₂(𝓞_F)` is finite because the class number is finite; MATH2 §0.1 (O).) -/
def FiniteCusps (S : Finset (FinitePlace F)) : Prop :=
  ∃ (n : ℕ) (τ : Fin n → SL(2, F)) (hτ : ∀ i, IsSMat S (τ i)), ∀ p : PairClass S,
    ∃ (i : Fin n) (γ : SL(2, 𝓞 F)), p = ((PairClass.inf S).actR (τ i) (hτ i)).act γ

/-! ### The function `G` -/

/-- `G(P) = ∑_p 1[ht_p(P) < 3] · ht_p(P)^σ` (sum over all pair classes). -/
def G (S : Finset (FinitePlace F)) (σ : ℝ) (P : X F) : ℝ :=
  ∑' p : PairClass S, if p.ht P < 3 then p.ht P ^ σ else 0

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_L2
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-B1, file 9: `G ∈ L¹ ∩ L²(Γ\X)`, and compactness of the truncated space at the cusp `∞`

* `measurable_G`; `lintegral_G_pow_lt_top`: `∫_{Γ\X} G^k dμ < ∞` (in the partition-of-unity form of
  WP-X) for every `k`, from the boundedness of `G` and **finite volume of `Γ\X`** (hypothesis `hvol`).
* `H3.isCompact_box`, `X.isCompact_box`.
* `exists_reduced`: every point of `X` is `Γ_∞`-equivalent (`Γ_∞ ⊂ SL₂(𝓞_F)` upper triangular) to a point
  with `x` in the fundamental cell and balanced `v`; `siegel S' T` is compact; hence
  `subset_orbit_siegel`: the points whose top class is in the `SL₂(𝓞_F)`-orbit of `∞` and whose top
  height is in `[c, T]` lie in `SL₂(𝓞_F) · (compact)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Compactness of the truncated space at the cusp `∞` (item 5) -/

/-- The box `{P : |x_w| ≤ B, m ≤ v_w ≤ M ∀ w}`. -/
def siegelBox (F : Type*) [Field F] [NumberField F] (m M B : ℝ) : Set (X F) :=
  {P | ∀ w, P w ∈ H3.box m M B}

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B7_Sum
/-! # B7_Sum: sums over residues modulo a principal ideal

For a commutative ring `R`, `c : R` and `f : R → ℂ`, `rsum c f` is the sum of `f` over chosen
representatives of `R ⧸ (c)` (the same `Function.surjInv` choice as `ArtinPrimitiveRoots.quotLift`).
For `f` periodic modulo `c` (`Per c f`) it does not depend on the choice, and we prove the
reindexing lemmas used for Gauss sums: translation, multiplication by a unit modulo `c`, the
Chinese remainder theorem, and the fibre formula for a function periodic modulo a divisor.
-/

namespace ArtinKP.B7

variable {R : Type*} [CommRing R]

/-- `f` is periodic modulo `c`. -/
def Per (c : R) (f : R → ℂ) : Prop :=
  ∀ a b : R, c ∣ a - b → f a = f b

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinKP.S.TSection.instCoeFunForallComplexForallRow
attribute [-simp] _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.add_apply _root_.ArtinKP.S.TSection.smulFun_apply _root_.ArtinKP.S.TSection.smul_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S.TSection.zero_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 1: `S_f`-adic smallness, norms, the pairing `⟨·,·⟩` on `F`, rows of `SL₂(R)`

* `Small 𝔪 N x`: `v(x) ≤ exp(-N)` at every `v ∣ 𝔪` (`N : ℤ`; `N < 0` means "bounded").
* `absS 𝔪 x = |x|_{S_f}`, `normS 𝔪 c d = ‖(c,d)‖ = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`.
* `brk ι P 𝔪 x y = ⟨x, y⟩ = ι (x, y)_S` for `x, y ≠ 0`, and `1` if `x = 0` or `y = 0`.
  With WP-A's orientation `⟨c, d⟩ = (d/c)(c/d)⁻¹` on coprime elements of `R` (`brk_reciprocity`).
* `sig`: Kubota's `σ_S` evaluated on a pair and a matrix, through `ι`.
* `Row 𝔪`: primitive pairs of `R = SInt 𝔪`; right action of `SL₂(R)`; scaling by `Rˣ`;
  `kappaRow` and its transformation laws (`kappaRow_act` is Lemma A5 on rows).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-! ### Smallness at the places of `S_f` -/

/-! ### Absolute values at `S_f` -/

open NumberField.HeightOneSpectrum in
theorem abv_eq_one_of_val_eq_one (v : HeightOneSpectrum (𝓞 F)) {x : F}
    (h : v.valuation F x = 1) : adicAbv F v x = 1 := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
  have h1 : adicAbv F v x ≤ 1 := by
    have := abv_le_of_val_le v (x := x) (n := 0) (by simp [h])
    simpa using this
  have h2 : adicAbv F v x⁻¹ ≤ 1 := by
    have := abv_le_of_val_le v (x := x⁻¹) (n := 0) (by simp [h])
    simpa using this
  rw [map_inv₀] at h2
  have hpos : 0 < adicAbv F v x := (adicAbv F v).pos hx0
  have h3 : 1 ≤ adicAbv F v x := by
    by_contra hlt
    rw [not_le] at hlt
    have := (one_lt_inv₀ hpos).mpr hlt
    linarith
  exact le_antisymm h1 h3

section abs

variable {𝔪 : Ideal (𝓞 F)}

open NumberField.HeightOneSpectrum

theorem absS_mul (x y : F) : absS 𝔪 (x * y) = absS 𝔪 x * absS 𝔪 y := by
  simp only [absS, map_mul, Finset.prod_mul_distrib]

theorem absS_nonneg (x : F) : 0 ≤ absS 𝔪 x :=
  Finset.prod_nonneg fun v _ => (adicAbv F v).nonneg x

theorem absS_inv (x : F) : absS 𝔪 x⁻¹ = (absS 𝔪 x)⁻¹ := by
  simp only [absS, map_inv₀, Finset.prod_inv_distrib]

theorem absS_pow (x : F) (n : ℕ) : absS 𝔪 (x ^ n) = absS 𝔪 x ^ n := by
  simp only [absS, map_pow, Finset.prod_pow]

theorem absS_eq_one_of_val (h𝔪 : 𝔪 ≠ ⊥) {x : F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F x = 1) : absS 𝔪 x = 1 :=
  Finset.prod_eq_one fun v hv =>
    abv_eq_one_of_val_eq_one v (h v ((CubicPkg.mem_sFin h𝔪 v).mp hv))

end abs

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

section brk

variable {ι : F →+* ℂ} {P : CubicPkg F} {𝔪 : Ideal (𝓞 F)}

theorem brk_inv_eq_sq (x y : F) : (brk ι P 𝔪 x y)⁻¹ = brk ι P 𝔪 x y ^ 2 := by
  have h := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) x y
  have h0 := brk_ne_zero (ι := ι) (P := P) (𝔪 := 𝔪) x y
  field_simp
  rw [← h]

theorem brk_inv_left (x y : F) : brk ι P 𝔪 x⁻¹ y = (brk ι P 𝔪 x y)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  lift x to Fˣ using IsUnit.mk0 x hx
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [← Units.val_inv_eq_inv_val, brk_units, brk_units, map_inv, MonoidHom.inv_apply, iota3_inv]

theorem brk_div_left {x x' : F} (y : F) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    brk ι P 𝔪 (x / x') y = brk ι P 𝔪 x y * (brk ι P 𝔪 x' y)⁻¹ := by
  rw [div_eq_mul_inv, brk_mul_left y hx (inv_ne_zero hx'), brk_inv_left]

theorem brk_mul_skew (x y : F) : brk ι P 𝔪 x y * brk ι P 𝔪 y x = 1 := by
  rw [brk_skew x y, inv_mul_cancel₀ (brk_ne_zero _ _)]

end brk

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-! ### Primitive rows -/

variable {𝔪 : Ideal (𝓞 F)}

namespace Row

theorem coprime (p : Row 𝔪) : IsCoprime p.c p.d := p.2

instance instMulActionUnitsSInt : MulAction (SInt 𝔪)ˣ (Row 𝔪) where
  one_smul p := by ext <;> simp
  mul_smul ε ε' p := by ext <;> simp [mul_assoc]

end Row

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Twisted
/-!
# WP-S, part 3: twisted sections on primitive rows

A *twisted section* (`TSection`) is MATH2's `Ψ_s = κ·Φ_s` restricted to primitive pairs of `R`:
a family `Ψ : ℂ → Row 𝔪 → ℂ`, entire in `s`, with

* `hom`: `Ψ_s(εp) = |ε|_{S_f}^{-s} Ψ_s(p)` for `ε ∈ U_S` (**no symbol**: the factor `⟨c, ε⟩` of the
  genuine section is cancelled by `κ(εp) = ⟨c, ε⟩⁻¹ κ(p)`, `kappaRow_smul`);
* `bound`: `|Ψ_s(p)| ≤ B ‖p‖^{-Re s}`, `B` uniform for `|s| ≤ M`;
* `level`: `Ψ_s(pγ) = κ(γ) Ψ_s(p)` for `γ ∈ Γ(𝔫)`, some `𝔫 ≠ 0`.

`SL₂(R)` acts by plain right translation (`TSection.translate`), with no cocycle; the
Eisenstein series `E_Ψ(P, s) = Σ_{p ∈ Row/U_S} Ψ_s(p) I_p(P)^s` then satisfies
`E_Ψ(γP) = E_{γ·Ψ}(P)` by reindexing `p ↦ pγ`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Comparison of norms -/

/-! ### Twisted sections -/

namespace TSection

variable {ι : F →+* ℂ}

/-- The degree-zero part `Ψ̃_s(p) = Ψ_s(p) ‖p‖^s`; it is `U_S`-invariant up to nothing. -/
def tilde (Ψ : TSection ι 𝔪) (s : ℂ) (p : Row 𝔪) : ℂ := Ψ s p * ((p.norm : ℝ) : ℂ) ^ s

end TSection

/-! ### `Ψ ↦ Ψ · 1[P ∤ c]` for an exterior prime -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_Def
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-!
# WP-B0, part 1: the Eisenstein series of a twisted section

`eis Ψ s Q = ∑_{p ∈ Row 𝔪 / U_S} Ψ_s(p) · I_p(Q)^s` for a twisted section `Ψ : TSection ι 𝔪`,
`s : ℂ`, `Q : X F`.

* Indexing type: `RowClass 𝔪 = MulAction.orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪)`; the summand is
  evaluated at `Quotient.out` and shown independent of the representative (`term_smul`,
  `term_out_mk`) by the product formula for `S`-units (`Ninf_mul_absS`).
* `sPl 𝔪 : Finset (FinitePlace F)` is the set `S_f` in the form B1 uses; `X.sNorm (sPl 𝔪) = normS 𝔪`,
  `IsSInt (sPl 𝔪) = membership in SInt 𝔪`, `IsSUnit (sPl 𝔪) = units of SInt 𝔪`.
* `RowClass.ht q Q = ht_q(Q) = I_q(Q)/‖q‖`; `eis_eq_tsum_ht : eis Ψ s Q = ∑ Ψ̃_s(q) ht_q(Q)^s`.
* Convergence for `Re s > 2` from `B1.summable_sHt_rpow` / `B1.exists_summable_majorant_sHt`.
* Automorphy: `eis Ψ s (γ • Q) = eis (translate γ⁻¹ Ψ) s Q` for `γ ∈ SL₂(R)` (note the inverse).
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The places of `S_f` as finite places; `S`-integers and `S`-units -/

open scoped Classical in
/-- The set `S_f = {v ∣ 𝔪}` as a `Finset (FinitePlace F)` (the form used by WP-B1 and `X.sHt`). -/
def sPl (𝔪 : Ideal (𝓞 F)) : Finset (FinitePlace F) := (CubicPkg.sFin 𝔪).image FinitePlace.mk

/-! ### The product formula for `S`-units -/

/-- `N_∞(x) = ∏_w |x|_w`, with `|·|_w` the **squared** modulus at the complex place `w`
(MATH2 §0.1). -/
def Ninf (x : F) : ℝ := ∏ w : InfinitePlace F, Complex.normSq (w.embedding x)

/-! ### Rows modulo `S`-units -/

/-- Primitive rows of `R` modulo `U_S = Rˣ`: the index set of the Eisenstein series. -/
abbrev RowClass (𝔪 : Ideal (𝓞 F)) : Type _ := MulAction.orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪)

namespace RowClass

/-- The class of a row. -/
def mk (p : Row 𝔪) : RowClass 𝔪 := Quotient.mk'' p

theorem mk_out (q : RowClass 𝔪) : mk q.out = q := Quotient.out_eq q

theorem mk_smul (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) : mk (ε • p) = mk p :=
  Quotient.sound' (MulAction.orbitRel_apply.mpr ⟨ε, rfl⟩)

/-- Right action of `SL₂(R)` on row classes. -/
def act (q : RowClass 𝔪) (γ : SL(2, SInt 𝔪)) : RowClass 𝔪 :=
  Quotient.map' (fun p : Row 𝔪 => p.act γ) (fun p p' h => by
    obtain ⟨ε, hε⟩ := MulAction.orbitRel_apply.mp h
    refine MulAction.orbitRel_apply.mpr ⟨ε, ?_⟩
    have hε' : ε • p' = p := hε
    change ε • p'.act γ = p.act γ
    rw [← Row.smul_act, hε']) q

theorem act_mk (p : Row 𝔪) (γ : SL(2, SInt 𝔪)) : (mk p).act γ = mk (p.act γ) := rfl

theorem act_one (q : RowClass 𝔪) : q.act 1 = q := by
  rw [← mk_out q, act_mk, Row.act_one]

theorem act_mul (q : RowClass 𝔪) (γ₁ γ₂ : SL(2, SInt 𝔪)) :
    q.act (γ₁ * γ₂) = (q.act γ₁).act γ₂ := by
  rw [← mk_out q, act_mk, act_mk, act_mk, Row.act_mul]

/-- `q ↦ qγ` as a permutation of the row classes. -/
def actEquiv (γ : SL(2, SInt 𝔪)) : RowClass 𝔪 ≃ RowClass 𝔪 where
  toFun q := q.act γ
  invFun q := q.act γ⁻¹
  left_inv q := by
    change (q.act γ).act γ⁻¹ = q
    rw [← act_mul, mul_inv_cancel, act_one]
  right_inv q := by
    change (q.act γ⁻¹).act γ = q
    rw [← act_mul, inv_mul_cancel, act_one]

@[simp] theorem actEquiv_apply (γ : SL(2, SInt 𝔪)) (q : RowClass 𝔪) : actEquiv γ q = q.act γ := rfl

/-- The `S`-normalized height `ht_q(Q) = I_q(Q) / ‖q‖` of a row class (MATH2 §0.1). -/
def ht (q : RowClass 𝔪) (Q : X F) : ℝ := X.sHt (sPl 𝔪) (q.out.c : F) (q.out.d : F) Q

end RowClass

/-! ### Convergence of the height series over row classes (from WP-B1) -/

/-! ### The summand and the series -/

/-- The summand `ψ(p) · I_p(Q)^s` at a row. -/
def term (ψ : Row 𝔪 → ℂ) (s : ℂ) (Q : X F) (p : Row 𝔪) : ℂ :=
  ψ p * ((X.pairHt (p.c : F) (p.d : F) Q : ℝ) : ℂ) ^ s

/-- `U_S`-homogeneity of degree `-s`: `ψ(εp) = |ε|_{S_f}^{-s} ψ(p)` (`TSection.hom` at one `s`). -/
def IsHom (ψ : Row 𝔪 → ℂ) (s : ℂ) : Prop :=
  ∀ (ε : (SInt 𝔪)ˣ) (p : Row 𝔪), ψ (ε • p) = ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s) * ψ p

/-- The series `∑_{q ∈ Row/U_S} ψ(q) I_q(Q)^s` for a function `ψ` on rows (meaningful when
`IsHom ψ s`). -/
def eisRaw (ψ : Row 𝔪 → ℂ) (s : ℂ) (Q : X F) : ℂ := ∑' q : RowClass 𝔪, term ψ s Q q.out

/-- **The Eisenstein series of a twisted section**:
`E_Ψ(Q, s) = ∑_{p ∈ Row 𝔪 / U_S} Ψ_s(p) · I_p(Q)^s`. -/
def eis {ι : F →+* ℂ} (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) : ℂ := eisRaw (Ψ s) s Q

/-! ### Height form (MATH2 §0.2) -/

section height

variable {ι : F →+* ℂ}

/-- `Ψ̃_s` on row classes. -/
def tildeC (Ψ : TSection ι 𝔪) (s : ℂ) (q : RowClass 𝔪) : ℂ := Ψ.tilde s q.out

/-! ### Bounds and convergence -/

end height

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Def2
attribute [-simp] _root_.ArtinKP.S.GSection.twist_apply
/-!
# WP-B0, part 2: regularity, automorphy, the term at `(0, 1)`

* `continuousOn_eis`: joint continuity of `(s, Q) ↦ E_Ψ(Q, s)` on `{Re s > 2} × X`;
  `continuous_eis`, `measurable_eis` (in `Q`); `differentiableOn_eis` (holomorphy in `s`).
* `eis_smul`: `E_Ψ(γ • Q) = E_{γ⁻¹·Ψ}(Q)` for `γ ∈ SL₂(R)` (the action on `X` through `toF 𝔪`),
  equivalently `eis_translate`: `E_{γ·Ψ}(Q) = E_Ψ(γ⁻¹ • Q)`.
* `TSection.stab Ψ`, `eis_smul_of_mem_stab`; `exists_level_eis`, `exists_level_eis_invariant`.
* `eis_eq_add`: `E_Ψ = Ψ_s(0,1) ht^s + ∑_{q ≠ ∞} Ψ̃_s(q) ht_q^s`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Local compactness of `X` -/

/-! ### Regularity of the summands -/

/-! ### Automorphy by reindexing -/

/-- The subgroup of `SL₂(R)` fixing `Ψ` under right translation: `Ψ_s(pγ) = Ψ_s(p)`. -/
def _root_.ArtinKP.S.TSection.stab (Ψ : TSection ι 𝔪) : Subgroup (SL(2, SInt 𝔪)) where
  carrier := {γ | ∀ (s : ℂ) (p : Row 𝔪), Ψ s (p.act γ) = Ψ s p}
  one_mem' := fun s p => by rw [Row.act_one]
  mul_mem' := fun {a b} ha hb s p => by rw [Row.act_mul, hb, ha]
  inv_mem' := fun {a} ha s p => by
    have := ha s (p.act a⁻¹)
    rw [← Row.act_mul, inv_mul_cancel, Row.act_one] at this
    exact this.symm

/-- `Ψ` is fixed by the elements of its level group on which `κ` is trivial. -/
theorem _root_.ArtinKP.S.TSection.exists_level_le_stab (Ψ : TSection ι 𝔪) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ ∀ γ ∈ Gamma 𝔪 𝔫, kappa ι 𝔪 γ = 1 → γ ∈ Ψ.stab := by
  obtain ⟨𝔫, h𝔫, h⟩ := Ψ.level
  refine ⟨𝔫, h𝔫, fun γ hγ hκ => ?_⟩
  intro s p
  rw [h γ hγ, hκ, one_mul]

/-! ### The term at the class of `(0, 1)` -/

/-- The row `(0, 1)`. -/
def Row.inf (𝔪 : Ideal (𝓞 F)) : Row 𝔪 := ⟨(0, 1), isCoprime_zero_left.mpr isUnit_one⟩

@[simp] theorem Row.inf_c : (Row.inf 𝔪).c = 0 := rfl
@[simp] theorem Row.inf_d : (Row.inf 𝔪).d = 1 := rfl

/-- The class of `(0, 1)` (the cusp `∞`). -/
def RowClass.inf (𝔪 : Ideal (𝓞 F)) : RowClass 𝔪 := RowClass.mk (Row.inf 𝔪)

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.K_Bessel
/-! # WP-K, file 1: the K-Bessel function

`besselK μ z = ½ ∫_0^∞ t^{μ−1} exp(−(z/2)(t + 1/t)) dt` (`μ : ℂ`, `z : ℝ`; meaningful for `z > 0`),
defined as half the Mellin transform of `besselKer z`.  Mathlib only.

* `besselK_differentiable`: entire in `μ`;
* `besselK_neg`: `K_{−μ} = K_μ`;
* `besselK_ofReal`, `besselKR_pos`: real and positive for real `μ`;
* `norm_besselK_le`: `‖K_μ(z)‖ ≤ K_{Re μ}(z)`;
* `besselKR_le_exp_mul`: `K_μ(z) ≤ e^{−(z−z₀)} K_μ(z₀)` for `z ≥ z₀ > 0`;
* `besselKR_le_gamma`: `K_μ(z) ≤ ½ Γ(|μ|) (z/2)^{−|μ|}` (`μ ≠ 0`);
* `besselKR_le_two_mul`: `K_μ(z) ≤ 2 K_M(z)` for `|μ| ≤ M`;
* `besselKR_le_min`: `K_μ(z) ≤ C min(z^{−|μ|}, z^{−N})` uniformly for `a ≤ |μ| ≤ M ≤ N`;
* `besselK_eq_schlafli`: the Schläfli form `½ (z/2)^{−μ} ∫ t^{μ−1} exp(−t − z²/(4t)) dt`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter Asymptotics Topology

noncomputable section

/-- The kernel `exp(−(z/2)(t + 1/t))`. -/
def besselKer (z t : ℝ) : ℝ := Real.exp (-(z / 2) * (t + t⁻¹))

/-- `K_μ(z) = ½ ∫_0^∞ t^{μ−1} exp(−(z/2)(t + 1/t)) dt`. -/
def besselK (μ : ℂ) (z : ℝ) : ℂ := (1 / 2 : ℂ) * mellin (fun t => (besselKer z t : ℂ)) μ

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.K_Jacquet
/-! # WP-K, file 2: the Jacquet integral at a complex place

Additive character: `archChar z = exp(2πi (z + z̄)) = exp(2πi · 2 Re z)` (the trace form `e(Tr z)`
of `ℂ/ℝ`; the goal's `sAddChar` is `exp(−2πi Tr_{F/ℚ}(·))` on fractional parts, whose factor at a
complex place `w` is `archChar (−σ_w ·)`; the Jacquet integral is even in `ν`, so the sign is
immaterial).

`jacquet s ν v = ∫_ℂ (v / (|x|² + v²))^s · archChar(−ν x) dx`. For `Re s > 1`, `v > 0`:

* `jacquet_zero`: `jacquet s 0 v = π/(s−1) · v^{2−s}`;
* `jacquet_eq`: for `ν ≠ 0`,
  `jacquet s ν v = (2π/Γ(s)) · (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`
  `= (2π^s/Γ(s)) · (2|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)` (`jacquet_eq'`).

The proof is OpenAI's (`OAI.CubicEisenstein.sourceFourierKernel_bessel`, openai/math family 003,
`Eisenstein/HyperbolicSpace.lean`, Apache 2.0; in our port `Definitions.Def_OAIHecke78B005`),
**copied** and restated for `besselK` (importing the bundle would drag B000–B004, ~45k lines).
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

noncomputable section

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

/-- `(1 + |z|²)^{−s}`. -/
def hyperbolicKernel (s : ℂ) (z : ℂ) : ℂ := ((1+‖z‖^2 : ℝ) : ℂ) ^ (-s)

/-- The Fourier transform `∫ (1+|z|²)^{−s} archChar(−freq·z) dz` (OpenAI's `sourceFourierKernel`). -/
def sourceFourierKernel (s freq : ℂ) : ℂ :=
  ∫ z : ℂ, hyperbolicKernel s z * archChar (-freq*z)

/-- OpenAI's `gaussianMixture`. -/
def gaussianMixture (s freq : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ)^(s-1) * Complex.exp (-t) *
    Complex.exp (-(t : ℂ)*‖z‖^2) * archChar (-freq*z)

/-! ## The Bessel form (ours, for `besselK`) -/

/-! ## The Jacquet integral -/

/-- The Jacquet integral at a complex place:
`∫_ℂ (v / (|x|² + v²))^s · e(−Tr(ν x)) dx`. -/
def jacquet (s ν : ℂ) (v : ℝ) : ℂ :=
  ∫ x : ℂ, ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s * archChar (-ν * x)

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.S_Ops
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 5: operations on genuine sections

* `GSection.nT t`: `(n(t)Φ)_s(c, d) = Φ_s(c, d + ct)`, `t ∈ F` (no symbol).
* `wFun`: `(wΦ)_s(c, d) = ⟨c, d⟩ Φ_s(d, -c)`; `twist_wFun`: its twist is the `w`-translate of the
  twist of `Φ` (MATH §5.2; the symbol is `σ_S((c,d), w)⁻¹·κ(w) = ⟨c, d⟩`).
* `GSection.torus β`: `(A(β)Φ)_s(c, d) = ⟨c, β⟩² Φ_s(β²c, βd)` for `c ≠ 0`, and
  `⟨d, β⟩ Φ_s(0, βd)` on the cell `c = 0` (MATH2 §6.1, with the `c = 0` factor decided by proof);
  `GSection.torusT β = |β|^{2s-1} A(β)` is `Ã(β)`.
  `torus_torus`: `A(β) A(β') = ⟨β, β'⟩ A(β β')`.
* `GSection.sharp π`: `Φ♯_s(c, d) = Φ_s(c, d/π³)`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The Weyl element -/

/-! ### The formal torus action `A(β)` -/

open Classical in
/-- The symbol factor of `A(β)`: `⟨c, β⟩²` on the big cell, `⟨d, β⟩` on the cell `c = 0`. -/
def tf (ι : F →+* ℂ) (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) (β c d : F) : ℂ :=
  if c = 0 then brk ι P 𝔪 d β else brk ι P 𝔪 c β ^ 2

section torus

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem tf_pow_three (β c d : F) : tf ι P 𝔪 β c d ^ 3 = 1 := by
  unfold tf
  split_ifs
  · exact brk_pow_three _ _
  · rw [← pow_mul, mul_comm, pow_mul, brk_pow_three, one_pow]

theorem norm_tf (β c d : F) : ‖tf ι P 𝔪 β c d‖ = 1 := by
  have h := congrArg norm (tf_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) β c d)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

/-- The factor of `A(β)` against `U_S`-scaling. -/
theorem tf_hom (β : F) (hβ : β ≠ 0) (ε : (SInt 𝔪)ˣ) (c d : F) (hcd : c ≠ 0 ∨ d ≠ 0) :
    tf ι P 𝔪 β (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * d)
        * brk ι P 𝔪 (Xs (β ^ 2 * c) (β * d)) ((ε : SInt 𝔪) : F)
      = brk ι P 𝔪 (Xs c d) ((ε : SInt 𝔪) : F) * tf ι P 𝔪 β c d := by
  set e : F := ((ε : SInt 𝔪) : F) with he
  have he0 : e ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
  have hskew := brk_mul_skew (ι := ι) (P := P) (𝔪 := 𝔪) e β
  by_cases hc : c = 0
  · have hd : d ≠ 0 := hcd.resolve_left (not_not.mpr hc)
    rw [hc, mul_zero, mul_zero, tf, if_pos rfl, tf, if_pos rfl, Xs_zero, Xs_zero,
      brk_mul_left _ he0 hd, brk_mul_left _ hβ hd]
    linear_combination (brk ι P 𝔪 d β * brk ι P 𝔪 d e) * hskew
  · rw [tf, if_neg (mul_ne_zero he0 hc), tf, if_neg hc,
      Xs_of_ne _ (mul_ne_zero (pow_ne_zero 2 hβ) hc), Xs_of_ne _ hc, brk_mul_left _ he0 hc,
      brk_mul_left _ (pow_ne_zero 2 hβ) hc, pow_two β, brk_mul_left _ hβ hβ]
    linear_combination (brk ι P 𝔪 c β ^ 2 * brk ι P 𝔪 c e
      * (brk ι P 𝔪 e β * brk ι P 𝔪 β e + 1)) * hskew

theorem tf_cube (β t : F) (ht : t ≠ 0) (c d : F) :
    tf ι P 𝔪 β (t ^ 3 * c) (t ^ 3 * d) = tf ι P 𝔪 β c d := by
  have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht
  by_cases hc : c = 0
  · rw [hc, mul_zero, tf, if_pos rfl, tf, if_pos rfl]
    by_cases hd : d = 0
    · rw [hd, mul_zero]
    · rw [brk_mul_left _ ht3 hd, brk_pow_three_left, one_mul]
  · rw [tf, if_neg (mul_ne_zero ht3 hc), tf, if_neg hc, brk_mul_left _ ht3 hc,
      brk_pow_three_left, one_mul]

/-- **Lemma 6.1 (S4) of MATH2**, as an identity of symbols: conjugating `γ` by `diag(β², β)`
changes `σ_S` exactly by the factor of `A(β)`.  Uses only bimultiplicativity, `⟨x,x⟩ = 1`,
cubes, and triviality on deep units. -/
theorem sig_torus (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) {β : F}
    (hβ : β ≠ 0) {a b c' d' : F} (hK : IsK 𝔪 N a b c' d') (c d : F) (hcd : c ≠ 0 ∨ d ≠ 0) :
    tf ι P 𝔪 β (c * a + d * c') (c * b + d * d')
        * sig ι P 𝔪 (β ^ 2 * c) (β * d) a (b / β) (β * c') d'
      = sig ι P 𝔪 c d a b c' d' * tf ι P 𝔪 β c d := by
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hN1' : (1 : ℤ) ≤ N := by exact_mod_cast hN1
  have ha0 : a ≠ 0 := by
    intro h
    have := hK.ha.val_eq_one hN1' v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hd0 : d' ≠ 0 := by
    intro h
    have := hK.hd.val_eq_one hN1' v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hal : ∀ y, brk ι P 𝔪 a y = 1 := fun y => brk_deep_left hG hN y hK.ha
  have hdl : ∀ y, brk ι P 𝔪 d' y = 1 := fun y => brk_deep_left hG hN y hK.hd
  set c₁ := c * a + d * c' with hc₁
  set d₁ := c * b + d * d' with hd₁
  have e1 : (β ^ 2 * c) * a + (β * d) * (β * c') = β ^ 2 * c₁ := by rw [hc₁]; ring
  have e2 : (β ^ 2 * c) * (b / β) + (β * d) * d' = β * d₁ := by rw [hd₁]; field_simp
  have hs' : sig ι P 𝔪 (β ^ 2 * c) (β * d) a (b / β) (β * c') d'
      = brk ι P 𝔪 (Xs (β ^ 2 * c₁) (β * d₁) / Xs (β ^ 2 * c) (β * d))
          (Xs (β ^ 2 * c₁) (β * d₁) / Xs (β * c') d') := by
    rw [sig, e1, e2]
  have hs : sig ι P 𝔪 c d a b c' d' = brk ι P 𝔪 (Xs c₁ d₁ / Xs c d) (Xs c₁ d₁ / Xs c' d') := rfl
  rw [hs', hs]
  have hβ2 : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  by_cases hc : c = 0
  · have hd : d ≠ 0 := hcd.resolve_left (not_not.mpr hc)
    have hc₁' : c₁ = d * c' := by rw [hc₁, hc]; ring
    have hd₁' : d₁ = d * d' := by rw [hd₁, hc]; ring
    by_cases hc' : c' = 0
    · have hc₁0 : c₁ = 0 := by rw [hc₁', hc', mul_zero]
      rw [hc₁0, hc, hc', tf, if_pos rfl, tf, if_pos rfl, hd₁']
      simp only [mul_zero, Xs_zero]
      rw [show β * (d * d') / (β * d) = d' by field_simp, show d * d' / d = d' by field_simp,
        hdl, hdl, brk_mul_left _ hd hd0, hdl]
      ring
    · have hc₁0 : c₁ ≠ 0 := by rw [hc₁']; exact mul_ne_zero hd hc'
      rw [tf, if_neg hc₁0, tf, if_pos hc, hc]
      simp only [mul_zero, Xs_zero]
      rw [Xs_of_ne _ (mul_ne_zero hβ2 hc₁0), Xs_of_ne _ (mul_ne_zero hβ hc'), Xs_of_ne _ hc₁0,
        Xs_of_ne _ hc', hc₁']
      rw [show β ^ 2 * (d * c') / (β * d) = β * c' by field_simp,
        show β ^ 2 * (d * c') / (β * c') = β * d by field_simp,
        show d * c' / d = c' by field_simp, show d * c' / c' = d by field_simp]
      rw [brk_mul_left _ hd hc', brk_mul_left _ hβ hc', brk_mul_right _ hβ hd,
        brk_mul_right _ hβ hd, brk_self, one_mul]
      have hskew := brk_mul_skew (ι := ι) (P := P) (𝔪 := 𝔪) d β
      have hC3 := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) c' β
      linear_combination (brk ι P 𝔪 d β * brk ι P 𝔪 c' β ^ 3 * brk ι P 𝔪 c' d) * hskew
        + (brk ι P 𝔪 d β * brk ι P 𝔪 c' d) * hC3
  · by_cases hc₁0 : c₁ = 0
    · have hdc' : d * c' = -(c * a) := by
        have := hc₁0
        rw [hc₁] at this
        linear_combination this
      have hc' : c' ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hdc'
        exact (mul_ne_zero hc ha0) (by linear_combination hdc')
      have hd₁c : d₁ * c' = -c := by
        rw [hd₁]; linear_combination d' * hdc' - c * hK.det
      have hd₁0 : d₁ ≠ 0 := by
        intro h
        rw [h, zero_mul] at hd₁c
        exact hc (by linear_combination hd₁c)
      have hd₁e : d₁ = -(c / c') := by
        field_simp
        linear_combination hd₁c
      have hY3 := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) c' β
      have hYY : (brk ι P 𝔪 c' β * brk ι P 𝔪 c' β)⁻¹ = brk ι P 𝔪 c' β :=
        inv_eq_of_mul_eq_one_right (by linear_combination hY3)
      have h1 : brk ι P 𝔪 d₁ β = brk ι P 𝔪 c β * brk ι P 𝔪 c' β ^ 2 := by
        rw [hd₁e, brk_neg_left, brk_div_left _ hc hc', brk_inv_eq_sq]
      have h2 : (brk ι P 𝔪 β (d₁ / c'))⁻¹ = brk ι P 𝔪 c β * brk ι P 𝔪 c' β := by
        rw [brk_skew β, inv_inv, hd₁e, show -(c / c') / c' = -(c / (c' * c')) by field_simp,
          brk_neg_left, brk_div_left _ hc (mul_ne_zero hc' hc'), brk_mul_left _ hc' hc', hYY]
      rw [tf, if_pos hc₁0, tf, if_neg hc, hc₁0]
      simp only [mul_zero, Xs_zero]
      rw [Xs_of_ne _ (mul_ne_zero hβ2 hc), Xs_of_ne _ (mul_ne_zero hβ hc'), Xs_of_ne _ hc,
        Xs_of_ne _ hc']
      rw [show β * d₁ / (β ^ 2 * c) = (d₁ / c) / β by field_simp,
        show β * d₁ / (β * c') = d₁ / c' by field_simp,
        brk_div_left _ (div_ne_zero hd₁0 hc) hβ, h1, h2]
      linear_combination (brk ι P 𝔪 (d₁ / c) (d₁ / c') * brk ι P 𝔪 c β ^ 2) * hY3
    · rw [tf, if_neg hc₁0, tf, if_neg hc, Xs_of_ne _ (mul_ne_zero hβ2 hc₁0),
        Xs_of_ne _ (mul_ne_zero hβ2 hc), Xs_of_ne _ hc₁0, Xs_of_ne _ hc]
      rw [show β ^ 2 * c₁ / (β ^ 2 * c) = c₁ / c by field_simp]
      by_cases hc' : c' = 0
      · have hc₁a : c₁ = c * a := by rw [hc₁, hc']; ring
        have hq : c₁ / c = a := by rw [hc₁a]; field_simp
        rw [hq]
        simp only [hal, one_mul, mul_one]
        rw [hc₁a, brk_mul_left _ hc ha0, hal, mul_one]
      · rw [Xs_of_ne _ (mul_ne_zero hβ hc'), Xs_of_ne _ hc',
          show β ^ 2 * c₁ / (β * c') = (c₁ / c') * β by field_simp,
          brk_mul_right _ (div_ne_zero hc₁0 hc') hβ, brk_div_left β hc₁0 hc, brk_inv_eq_sq]
        have hZ3 := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) c₁ β
        linear_combination (brk ι P 𝔪 (c₁ / c) (c₁ / c') * brk ι P 𝔪 c β ^ 2) * hZ3

end torus

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- **The formal torus action** `(A(β)Φ)_s(c, d) = ⟨c, β⟩² Φ_s(β²c, βd)` (`c ≠ 0`),
`⟨d, β⟩ Φ_s(0, βd)` (`c = 0`), for `β ∈ Fˣ` (MATH2 §6.1).  It maps sections to sections. -/
def torus (hG : Good 𝔪) (β : F) (hβ : β ≠ 0) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 where
  toFun s c d := tf ι P 𝔪 β c d * Φ s (β ^ 2 * c) (β * d)
  zero s := by simp [Φ.zero]
  hom s ε c d := by
    by_cases h0 : c = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp [Φ.zero]
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
    have e1 : β ^ 2 * (((ε : SInt 𝔪) : F) * c) = ((ε : SInt 𝔪) : F) * (β ^ 2 * c) := by ring
    have e2 : β * (((ε : SInt 𝔪) : F) * d) = ((ε : SInt 𝔪) : F) * (β * d) := by ring
    rw [e1, e2, Φ.hom]
    linear_combination (((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s) * Φ s (β ^ 2 * c) (β * d))
      * tf_hom (ι := ι) (P := P) β hβ ε c d hcd
  cube s t ht c d := by
    have e1 : β ^ 2 * (t ^ 3 * c) = t ^ 3 * (β ^ 2 * c) := by ring
    have e2 : β * (t ^ 3 * d) = t ^ 3 * (β * d) := by ring
    rw [e1, e2, Φ.cube s t ht, tf_cube β t ht]
    ring
  level := by
    obtain ⟨N₀, hN₀1, hN₀⟩ := P.exists_isDeepLevel hG.ne_bot
    obtain ⟨B, hB⟩ := exists_small_neg hG.ne_bot β
    obtain ⟨B', hB'⟩ := exists_small_neg hG.ne_bot β⁻¹
    obtain ⟨N, hNle, hN⟩ := Φ.level_ge N₀
    refine ⟨N + B + B', fun a b c' d' hK s c d => ?_⟩
    have hN' : ((N + B + B' : ℕ) : ℤ) = N + B + B' := by push_cast; ring
    rw [hN'] at hK
    have hK₁ : IsK 𝔪 N a (b / β) (β * c') d' := by
      refine ⟨?_, hK.ha.mono (by omega), ?_, ?_, hK.hd.mono (by omega)⟩
      · have := hK.det
        field_simp
        linear_combination this
      · rw [div_eq_mul_inv]
        exact Small.mono (by omega) (hK.hb.mul hB')
      · exact Small.mono (by omega) (hB.mul hK.hc)
    have hK₀ : IsK 𝔪 N₀ a b c' d' := hK.mono (by omega)
    have h := hN a (b / β) (β * c') d' hK₁ s (β ^ 2 * c) (β * d)
    have e1 : (β ^ 2 * c) * a + (β * d) * (β * c') = β ^ 2 * (c * a + d * c') := by ring
    have e2 : (β ^ 2 * c) * (b / β) + (β * d) * d' = β * (c * b + d * d') := by field_simp
    rw [e1, e2] at h
    rw [h]
    by_cases h0 : c = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp [Φ.zero]
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
    linear_combination (Φ s (β ^ 2 * c) (β * d)) * sig_torus (ι := ι) hG hN₀1 hN₀ hβ hK₀ c d hcd
  holo c d := (differentiable_const _).mul (Φ.holo _ _)
  bound M := by
    obtain ⟨B, -, hB⟩ := Φ.bound_comp M (β ^ 2) 0 0 β (β ^ 2)⁻¹ 0 0 β⁻¹ (fun c d => by
      constructor <;> field_simp <;> ring)
    refine ⟨B, fun s hs c d => ?_⟩
    have e : Φ s (β ^ 2 * c) (β * d) = Φ s (c * β ^ 2 + d * 0) (c * 0 + d * β) := by
      congr 1 <;> ring
    rw [norm_mul, norm_tf, one_mul, e]
    exact hB s hs c d

/-- **`Ã(β) = |β|_{S_f}^{2s-1} A(β)`** (MATH2 §6.1). -/
def torusT (hG : Good 𝔪) (β : F) (hβ : β ≠ 0) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 :=
  smulFun (fun s => ((absS 𝔪 β : ℝ) : ℂ) ^ (2 * s - 1))
    (((differentiable_id.const_mul (2 : ℂ)).sub_const 1).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (absS_pos hβ).ne')))
    (Φ.torus hG β hβ)

theorem torusT_apply (hG : Good 𝔪) (β : F) (hβ : β ≠ 0) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    Φ.torusT hG β hβ s c d
      = ((absS 𝔪 β : ℝ) : ℂ) ^ (2 * s - 1) * (tf ι P 𝔪 β c d * Φ s (β ^ 2 * c) (β * d)) := rfl

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_BigCell
/-!
# WP-S, part 6: big-cell and small-cell sections

For `η ∈ Fˣ`, a deep level `N ≥ 1`, and a lattice coset `L = {u : Small M (u - t₀)}`:

* `InClass 𝔪 N η c`: `c ∈ η · U_S · (Fˣ)³ · U_N` (`U_N` = units `N`-close to `1`); this is the
  rational form of MATH2's cube-saturated class `η U_S U_𝔫 (F_{S_f}ˣ)³`.
* `bigCell`: `Φ^{big}_s(c, d) = ⟨η, c⟩ |c|_{S_f}^{-s} 1[c ∈ class η] 1[d/c ∈ L]`.
  The unitary factor `⟨η, c⟩` equals MATH2's `⟨η₀, ε⟩` for `c = η₀ ε t³ u` and needs no choice.
* `smallCell = w · bigCell`: `⟨c, d⟩ ⟨η, d⟩ |d|^{-s} 1[d ∈ class η] 1[-c/d ∈ L]`.
* `nT_bigCell`, `twist_smallCell`: the translates by `n(t)` and `w`.
* `sum_bigCell_apply`: the sum over pairwise disjoint classes (MATH2 §3.1, `Φ^Σ`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem ofReal_mul_cpow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a * b : ℝ) : ℂ) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha hb]

theorem ofReal_pow_cpow {x : ℝ} (hx : 0 < x) (n : ℕ) (s : ℂ) :
    ((x ^ n : ℝ) : ℂ) ^ s = (x : ℂ) ^ (n * s) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxn : ((x ^ n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos hx n).ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hxn,
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log (pow_pos hx n).le, Real.log_pow]
  push_cast
  ring_nf

/-! ### Classes -/

/-! ### The support of a big-cell section and its stability -/

/-! ### Small-cell sections -/

/-! ### Finite sums: the sum over classes and additive projections -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
/-!
# WP-B, part 2: the characters and the archimedean integral

* `eInf x = ∏_w archChar (-x_w)` on `ℂ^r`; `eInf (emb a) = exp(-2πi Tr a)` for `a ∈ F`.
* `psiS h𝔪 : SfChar 𝔪`, `ψ_{S_f}(x) = sAddChar 𝔪 x · conj (eInf (emb x))`; it is trivial on
  `𝔩_0`, and `eInf (emb x) = sAddChar 𝔪 x · conj ψ_{S_f}(x)` (`eInf_emb_eq`).
* `kerA v x = ∏_w v_w / (|x_w|² + v_w²)`; `I_{(c,d)}(x, v) = N_∞(c)⁻¹ · kerA v (x + d/c)`.
* `Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; the integral of a shifted kernel against
  `conj eInf(ν x)` (`integral_shift_kernel`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The archimedean character -/

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

/-- `∏_w v_w / (|x_w|² + v_w²)`. -/
def kerA (v : InfinitePlace F → ℝ) (x : InfinitePlace F → ℂ) : ℝ :=
  ∏ w, v w / (‖x w‖ ^ 2 + v w ^ 2)

/-- `W_s(ν; v) = ∏_w jacquet s (-σ_w ν) v_w` (the Jacquet integral is even in `ν`). -/
def Winf (s : ℂ) (ν : F) (v : InfinitePlace F → ℝ) : ℂ :=
  ∏ w : InfinitePlace F, jacquet s (-(w.embedding ν)) (v w)

/-- The character `x ↦ conj e_∞(ν x)` against which the `ν`-th coefficient is taken. -/
def chiInf (ν : F) (x : InfinitePlace F → ℂ) : ℂ := conj (eInf (emb ν * x))

/-! ### Shifted kernels -/

/-- The summand of the Eisenstein series for a row `(c, d)`, `c ≠ 0`, as a function of `x`:
`A · (N⁻¹ · kerA v (x + e))^s` with `N = N_∞(c)`, `e = emb (d/c)`. -/
def hKer (A : ℂ) (N : ℝ) (e : InfinitePlace F → ℂ) (s : ℂ) (v : InfinitePlace F → ℝ)
    (x : InfinitePlace F → ℂ) : ℂ :=
  A * ((N⁻¹ * kerA v (x + e) : ℝ) : ℂ) ^ s

/-- `C_σ(v) = ∫ (kerA v)^σ` (`= (π/(σ-1))^r · ht^{2-σ}`; only its finiteness is used). -/
def kerInt (σ : ℝ) (v : InfinitePlace F → ℝ) : ℝ := ∫ y : InfinitePlace F → ℂ, kerA v y ^ σ

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.E_Series
/-! # E_Series: the Kubota coefficient series and its splitting at a prime (corrected (4.1))

Abstract setting (`R` a domain; in the application `R = SInt 𝔪`):

* `Cls R` = nonzero classes of `R` modulo units (`(R∖0)/U_S`), `ClsP π` = those prime to `π`;
  `tsum_split`: a unit-invariant absolutely summable family over `Cls R` is the iterated sum over
  `c = π^j c'`, `π ∤ c'`.
* `Pairing S`: the pairing `⟨c, d⟩` (in the application `ι (c, d)_S`, WP-A's `HS`).
* `Kubota S A Sec`: the **interface** to the analytic packages.  A section `Φ : Sec` is seen only
  through its normalized finite Jacquet functional `Lam Φ c ν s = |c|_{S_f}^s · J_Φ(c; ν, s)`, and
  `act β = Ã(β)` (MATH2 §6.1).  The coefficient series is
  `aSer Φ ν s = ∑_{c ∈ (R∖0)/U} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`.
* `aSer_split` — **(4.1′)**: for `π ∤ ν₀`, `Re s > 2`,
  `aSer Φ (ν₀ π^k) s = Cform q G G' x (m ↦ Y_m(Ã(π)^k Φ)) k`, with B7's `Cform` verbatim, `x = q^{-s}`,
  and the three `π`-coprime twisted series `Y_m(Ψ) = ∑_{π ∤ c'} g(ν₀,c') ((π/c')(c'/π))^{-m}
  Lam Ψ (π^m c') ν₀ s N(c')^{-s}`.
* `aSer_unit` (MATH2 Lemma 6.2), `Lam_act_act` (`Ã(β)Ã(β') = ⟨β,β'⟩ Ã(ββ')` on `Lam`),
  `Lam_iter_eq_pow`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### Classes modulo units -/

/-! ### The norm `N(c) = #(R/cR)` -/

/-! ### Symbols -/

/-- The pairing `⟨c, d⟩` of MATH2 §0.1 (hypothesis (P)); in the application
`br c d = ι (c, d)_S` (`A.iota3 ι (P.HS 𝔪 cu du)`), and `br_coprime` is `cubicExt_reciprocity`. -/
structure Pairing (S : CubicSymbol R) where
  /-- `br c d = ⟨c, d⟩` -/
  br : R → R → ℂ
  br_mul_left : ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → br (a * b) c = br a c * br b c
  br_mul_right : ∀ a b c : R, a ≠ 0 → b ≠ 0 → c ≠ 0 → br a (b * c) = br a b * br a c
  br_self : ∀ a : R, a ≠ 0 → br a a = 1
  br_pow_three : ∀ a b : R, a ≠ 0 → b ≠ 0 → br a b ^ 3 = 1
  br_coprime : ∀ c d : R, c ≠ 0 → d ≠ 0 → IsCoprime c d → br c d * S.sym c d = S.sym d c

/-! ### Gauss sums: units and the splitting `c = π^j c'` -/

/-! ### The interface -/

/-- **Interface to the analytic packages** (WP-E.md §1).  `Sec` is the type of sections;
`Lam Φ c ν s = |c|_{S_f}^s · J_Φ(c; ν, s)` is the normalized finite Jacquet functional
(MATH2 §0.2), and `act β = Ã(β) = |β|_{S_f}^{2s−1} A(β)` (MATH2 §6.1).  All laws are required for
`Re s > 2` and nonzero `c` only. -/
structure Kubota (S : CubicSymbol R) (A : AddData R K) (Sec : Type*) extends Pairing S where
  /-- `act β Φ = Ã(β)Φ` -/
  act : R → Sec → Sec
  /-- `Lam Φ c ν s = |c|^s J_Φ(c; ν, s)` -/
  Lam : Sec → R → R → ℂ → ℂ
  /-- (S1)/(J1): `J_Φ(εc;ν) = ⟨c,ε⟩|ε|^{-s} J_Φ(c;ν)`, `⟨c,ε⟩ = (ε/c)`. -/
  Lam_unit : ∀ (Φ : Sec) (u c ν : R) (s : ℂ), IsUnit u → c ≠ 0 → 2 < s.re →
    Lam Φ (u * c) ν s = S.sym u c * Lam Φ c ν s
  /-- (S1³): `J_Φ(t³c;ν) = |t|^{-3s} J_Φ(c;ν)`. -/
  Lam_cube : ∀ (Φ : Sec) (t c ν : R) (s : ℂ), t ≠ 0 → c ≠ 0 → 2 < s.re →
    Lam Φ (t ^ 3 * c) ν s = Lam Φ c ν s
  /-- MATH2 Lemma 6.1(iii): `J_{A(β)Φ}(c;ν) = ⟨c,β⟩² |β| J_Φ(β²c; βν)`. -/
  Lam_act : ∀ (Φ : Sec) (β c ν : R) (s : ℂ), β ≠ 0 → c ≠ 0 → 2 < s.re →
    Lam (act β Φ) c ν s = br c β ^ 2 * Lam Φ (β ^ 2 * c) (β * ν) s
  /-- `Ã(β)` is onto (its inverse is `Ã(β⁻¹)`, MATH2 Lemma 6.1 for `β ∈ Fˣ`). -/
  act_surj : ∀ (β : R) (Φ : Sec), β ≠ 0 → ∃ Φ' : Sec, ∀ (c ν : R) (s : ℂ), c ≠ 0 → 2 < s.re →
    Lam (act β Φ') c ν s = Lam Φ c ν s
  /-- absolute convergence of the Kubota series for `Re s > 2` -/
  summable : ∀ (Φ : Sec) (ν : R) (s : ℂ), ν ≠ 0 → 2 < s.re →
    Summable (fun a : Cls R => gauss S A ν (rp a.1) * Lam Φ (rp a.1) ν s * nrm (rp a.1) ^ (-s))

namespace Kubota

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

/-- The summand `g(ν,c) · Lam Φ c ν s · N(c)^{-s}` of the Kubota series. -/
noncomputable def term (Φ : Sec) (ν : R) (s : ℂ) (c : R) : ℂ :=
  gauss S A ν c * D.Lam Φ c ν s * nrm c ^ (-s)

/-- **The coefficient series** `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/U} g(ν,c) Lam Φ c ν s N(c)^{-s}`. -/
noncomputable def aSer (Φ : Sec) (ν : R) (s : ℂ) : ℂ := ∑' a : Cls R, D.term Φ ν s (rp a.1)

end Kubota

/-! ### The prime datum and the splitting (4.1′) -/

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.B_FourIndex
/-!
# WP-B, part 4: the index set of the unfolded sum

* `exists_sInt_sub_small`: strong approximation `F = R + 𝔩_M` (from `B7.hasWit_all`).
* `latR 𝔪 M = R ∩ 𝔩_M`, `transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r` (the translation lattice `Λ_M`).
* `sec`: for `c ≠ 0` a section of `R → R/cR × F/𝔩_M`, `d ↦ (d mod c, d/c mod 𝔩_M)`.
* `thetaEquiv`: `((Σ a, R/c_a R) × F/𝔩_M) × Λ_M ≃ (R∖0)/Rˣ × R`,
  `(((a, α), u), b) ↦ (a, sec(α, u) + c_a b)` — MATH2's `R/cΛ ≅ R/cR × F_{S_f}/cΛ̂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Strong approximation -/

/-! ### The translation lattice -/

/-! ### The section -/

/-! ### The index equivalence -/

/-! ### Rows with `c ≠ 0` modulo units -/

theorem out_c_ne_zero {q : RowClass 𝔪} (hq : q ≠ RowClass.inf 𝔪) : q.out.c ≠ 0 := by
  intro h
  apply hq
  have hu : IsUnit q.out.d := by
    have := q.out.coprime
    rw [h] at this
    exact isCoprime_zero_left.mp this
  obtain ⟨ε, hε⟩ := hu
  have e : q.out = ε • Row.inf 𝔪 := Row.ext (by simp [h]) (by simp [hε])
  rw [← RowClass.mk_out q, e, RowClass.mk_smul]
  rfl

theorem exists_unit_mul_eq_rp (c : SInt 𝔪) :
    ∃ u : (SInt 𝔪)ˣ, (u : SInt 𝔪) * c = rp (Associates.mk c) := by
  obtain ⟨u, hu⟩ := Associates.mk_eq_mk_iff_associated.mp (mk_rp (Associates.mk c))
  refine ⟨u⁻¹, ?_⟩
  conv_lhs => rw [← hu]
  rw [mul_comm, mul_assoc, Units.mul_inv, mul_one]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.E_Pairing
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
/-! # E_Pairing: the pairing `⟨c, d⟩ = ι (c, d)_S` of WP-A is a `Pairing`

`pairingHS`: for any `S : CubicSymbol (SInt 𝔪)` that agrees with WP-A's `cubicExt` (for nonzero
denominators), `br c d = iota3 ι (P.HS 𝔪 c d)` satisfies the interface `Pairing S` of `E_Series`:
bimultiplicative, alternating, cube-valued, and `⟨c, d⟩ (c/d) = (d/c)` for coprime `c, d`
(`cubicExt_reciprocity`).  This is hypothesis (P) of MATH2 §0.1 on `R ∖ 0`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

namespace ArtinKP.E

open ArtinKP.B7 ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

open Classical in
/-- A nonzero element of `R` as a unit of `F` (junk `1` at `0`). -/
noncomputable def uF (c : SInt 𝔪) : Fˣ := if h : (c : F) = 0 then 1 else Units.mk0 (c : F) h

lemma coe_ne_zero {c : SInt 𝔪} (hc : c ≠ 0) : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)

lemma uF_coe {c : SInt 𝔪} (hc : c ≠ 0) : ((uF c : Fˣ) : F) = c := by
  unfold uF; rw [dif_neg (coe_ne_zero hc)]; rfl

lemma uF_mul {c d : SInt 𝔪} (hc : c ≠ 0) (hd : d ≠ 0) : uF (c * d) = uF c * uF d := by
  apply Units.ext
  rw [Units.val_mul, uF_coe (mul_ne_zero hc hd), uF_coe hc, uF_coe hd]
  rfl

/-- **WP-A's `S`-pairing as the interface `Pairing`.** -/
noncomputable def pairingHS (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (S : CubicSymbol (SInt 𝔪))
    (hsym : ∀ d c : SInt 𝔪, c ≠ 0 → S.sym d c = cubicExt ι 𝔪 d c) : Pairing S where
  br := fun c d => iota3 ι (P.HS 𝔪 (uF c) (uF d))
  br_mul_left := fun a b c ha hb _ => by
    rw [uF_mul ha hb, map_mul, MonoidHom.mul_apply, map_mul]
  br_mul_right := fun a b c _ hb hc => by
    rw [uF_mul hb hc, map_mul, map_mul]
  br_self := fun a _ => by rw [P.HS_self, map_one]
  br_pow_three := fun a b _ _ => iota3_pow_three ι _
  br_coprime := fun c d hc hd h => by
    rw [hsym c d hd, hsym d c hc,
      cubicExt_reciprocity ι P hG hz6 c d (uF c) (uF d) (uF_coe hc) (uF_coe hd)
        (val_of_isCoprime h)]
    ring

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.S2_Symbol
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
/-!
# WP-S2, part 4: the cubic symbol of `R = SInt 𝔪` as a `B7.CubicSymbol`, and its `E.Pairing`

* `isCoprime_of_val`: elements of `R` without a common exterior prime are coprime
  (`E.val_of_isCoprime` is the converse).
* `cubicExt_eq_zero_iff`: `(d/c) = 0 ↔ ¬ IsCoprime d c` for `c ≠ 0`.
* `cubicSymbol ι P hG hz6 : B7.CubicSymbol (SInt 𝔪)` with `sym d c = A.cubicExt ι 𝔪 d c`
  (WP-E open issue 1), `cubicSymbol_gen` (the hypothesis `hS` of `E_Link`), and
  `pairing : E.Pairing (cubicSymbol …)` (`E.pairingHS`).
* `span_rowElt` (WP-E open issue 5).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section symbol

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **The `S`-pairing as an `E.Pairing`** of `cubicSymbol`: `br c d = ι (c, d)_S`. -/
def pairing : Pairing (cubicSymbol ι P hG hz6) :=
  pairingHS ι P hG hz6 (cubicSymbol ι P hG hz6) (fun _ _ _ => rfl)

theorem pairing_br {c d : SInt 𝔪} (hc : c ≠ 0) (hd : d ≠ 0) :
    (pairing ι P hG hz6).br c d = brk ι P 𝔪 (c : F) (d : F) := by
  have e1 := uF_coe hc
  have e2 := uF_coe hd
  change iota3 ι (P.HS 𝔪 (uF c) (uF d)) = _
  rw [← e1, ← e2, brk_units]

end symbol

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.B_FourRows
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-!
# WP-B, part 5: the Eisenstein series as a sum over `(c mod units, d ∈ R)`

`Tfun Φ s Q c d = (d/c)⁻¹ Φ_s(c, d) I_{(c,d)}(Q)^s` for all `c, d ∈ R` (zero unless `d` is prime
to `c`).  For `Re s > 2`:

`eis (twist Φ) s Q = Φ_s(0, 1) ht(Q)^s + ∑_{(a, d) ∈ (R∖0)/Rˣ × R} Tfun Φ s Q c_a d`
(`eis_eq_add_tsum_Tfun`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-- The summand of the Eisenstein series of `twist Φ` at the pair `(c, d)`, `c ≠ 0`. -/
def Tfun (Φ : GSection ι P 𝔪) (s : ℂ) (Q : X F) (c d : SInt 𝔪) : ℂ :=
  (cubicExt ι 𝔪 d c)⁻¹ * Φ s (c : F) (d : F) * ((X.pairHt (c : F) (d : F) Q : ℝ) : ℂ) ^ s

section

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)

/-- The injection of the classes of rows with `c ≠ 0` into `(R∖0)/Rˣ × R`. -/
def jFun (q : {q : RowClass 𝔪 // q ≠ RowClass.inf 𝔪}) : Cls (SInt 𝔪) × SInt 𝔪 :=
  (⟨Associates.mk q.1.out.c, by
      rw [Ne, Associates.mk_eq_zero]
      exact out_c_ne_zero q.2⟩,
    ((exists_unit_mul_eq_rp q.1.out.c).choose : SInt 𝔪) * q.1.out.d)

end

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RO_Ring
/-! # WP-RO, file 1: the ring of `S`-integers is a PID; `SBezout`

`SOf 𝔪 : Finset (FinitePlace F)` is the set of finite places dividing `𝔪`, in the form used by
WP-B1.  For `𝔪 ≠ ⊥`, `B1.IsSInt (SOf 𝔪)` is membership in `SInt 𝔪` (`isSInt_SOf_iff`), so
`B1.SIntRing (SOf 𝔪) ≃+* SInt 𝔪` (`sIntEquiv`).

* `isPrincipalIdealRing_SInt (hG : Good 𝔪) : IsPrincipalIdealRing (SInt 𝔪)`: every ideal of `SInt 𝔪`
  is extended from `𝓞 F` (clear denominators by an `S`-unit, `B1.exists_unit_rescale`), and extended
  ideals are principal (`Good.principal`).
* `isPrincipalIdealRing_SIntRing`, `sBezout (hG : Good 𝔪) : B1.SBezout (SOf 𝔪)`.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `S`-units in the sense of WP-B1 are the units of `SInt 𝔪`. -/
theorem isSUnit_coe_unit (h𝔪 : 𝔪 ≠ ⊥) (ε : (SInt 𝔪)ˣ) : IsSUnit (SOf 𝔪) ((ε : SInt 𝔪) : F) := by
  have h3 : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  refine ⟨left_ne_zero_of_mul_eq_one h3, fun v hv => ?_⟩
  have h1 := isSInt_coe h𝔪 (ε : SInt 𝔪) v hv
  have h2 := isSInt_coe h𝔪 ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) v hv
  have h4 : v ((ε : SInt 𝔪) : F) * v (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, h3, map_one]
  have h5 : 0 ≤ v ((ε : SInt 𝔪) : F) := apply_nonneg v _
  nlinarith

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.B_FourMain
/-!
# WP-B, part 6: the unfolded family and its integrals

For a genuine section `Φ`, a depth `M` valid for `(Φ, ν)` (`ValidDepth`), and `i = ((a, α), u)`
in `IdxI 𝔪 M`, with `c = rp a`, `σ = sec(α, u)`:

`hI i x = (σ/c)⁻¹ Φ_s(c, σ) · (N_∞(c)⁻¹ kerA v (x + σ/c))^s`.

* `tsum_hI_eq`: `∑_{(i, b) ∈ IdxI × Λ_M} hI i (b + x) = ∑_{(a, d)} Tfun Φ s (x, v) c_a d`.
* `tsum_lintegral_hI_ne_top`: `∑ᵢ ∫ |hI i| < ∞` for `Re s > 2` (S-1, `∑ N(c)^{1-σ} < ∞`).
* `integral_hI`: `∫ hI i · conj e_∞(ν ·) = gTerm · jTerm · (N_∞(c)⁻¹)^s · W_s(ν; v)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-- The depth `M` is valid for the section `Φ` and the frequency `ν`: `Φ` is invariant under
`n(b)`, `b ∈ 𝔩_M`, and `ψ_{S_f}(ν ·)` is trivial on `𝔩_M`. -/
structure ValidDepth (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (ν : F) (M : ℤ) : Prop where
  unip : ∀ b : F, Small 𝔪 M b → ∀ (s : ℂ) (c d : F), Φ s c (d + c * b) = Φ s c d
  char : ∀ h : F, Small 𝔪 M h → psiS hG.ne_bot (ν * h) = 1

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

/-- `c` of an index. -/
def cI (i : IdxI 𝔪 M) : SInt 𝔪 := rp i.1.1.1

/-- the chosen `d` of an index -/
def sI (i : IdxI 𝔪 M) : SInt 𝔪 := sec hG.ne_bot M (rp i.1.1.1) i.1.2 i.2

/-- the coefficient of an index -/
def AI (i : IdxI 𝔪 M) : ℂ :=
  (cubicExt ι 𝔪 (sI hG M i) (cI M i))⁻¹ * Φ s (cI M i : F) (sI hG M i : F)

/-- The unfolded family. -/
def hI (i : IdxI 𝔪 M) (x : InfinitePlace F → ℂ) : ℂ :=
  hKer (AI hG Φ s M i) (Ninf (cI M i : F)) (emb ((sI hG M i : F) / (cI M i : F))) s v x

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourCoeff
/-!
# WP-B, part 7: the Fourier coefficients of the Eisenstein series at the cusp `∞`

`fourier_coeff`: for a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
and a fundamental cell `D` of `Λ_M = emb (R ∩ 𝔩_M)`:

`∫_D E(x, v) · conj e_∞(νx) dx = Φ_s(0,1) ht(v)^s ∫_D conj e_∞(νx) dx
    + vol(𝔩_M)⁻¹ · W_s(ν; v) · ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · λ(c; ν, s) · N(c)^{-s}`,

`λ(c; ν, s) = lam ψ_{S_f} M Φ c ν s = |c|_{S_f}^s J_Φ(c; ν, s)`, `N(c) = #(R/cR)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

/-! ### The integral of one member of the family -/

/-- The summand of the Gauss sum `g(ν, c_a)` at the residue `α`. -/
def gTerm (ν : SInt 𝔪) (x : Σ a : Cls (SInt 𝔪), SInt 𝔪 ⧸ Ideal.span {rp a.1}) : ℂ :=
  ((S2.cubicSymbol ι P hG hz6).sym (B7.rep (rp x.1.1) x.2) (rp x.1.1))⁻¹
    * (B7.sAdd 𝔪 hG.ne_bot).ψ (ν * B7.rep (rp x.1.1) x.2) (rp x.1.1)

/-- The summand of the finite Jacquet functional `J_Φ(c_a; ν, s)` at the class `u`. -/
def jTerm (ν : SInt 𝔪) (a : Cls (SInt 𝔪)) (u : F ⧸ lat 𝔪 M) : ℂ :=
  Φ s ((rp a.1 : SInt 𝔪) : F) (((rp a.1 : SInt 𝔪) : F) * u.out) * conj (psiS hG.ne_bot ((ν : F) * u.out))

/-! ### Summation -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Lattice
/-!
# WP-S2, part 5: lattices with a depth function; the Kirillov function as a Jacquet functional

* `SmallD 𝔪 k x`: `v(x) ≤ exp(-k v)` at every `v ∣ 𝔪`, for a depth function
  `k : HeightOneSpectrum (𝓞 F) → ℤ`; `latD 𝔪 k`, `volD 𝔪 k`, `jacD ψ k f ν`, `lamD`.
  For a constant depth these are `Small`, `lat`, `vol`, `jac`, `lam` of WP-S, by `rfl`.
* `smallD_mul_iff`: `β · 𝔩_k = 𝔩_{k + ord β}`; `absS_eq_prod`: `|β|_{S_f} = ∏ q_v^{-ord_v β}`.
* `jacD_subst`: the substitution `u = β u'`,
  `∫ g(u/β) conj ψ(νu) du = |β| ∫ g(u') conj ψ(νβu') du'`.
* `kir_eq_lamD` (**MATH2 Lemma 6.1 (iii)** / §6.3): `kir ψ M Φ η β s = λ_η((Ã(β)Φ)_s; 1)`, the
  functional on the right taken on the lattice `β 𝔩_M` (depth `M + ord_v β`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- **`β · 𝔩_{k - ord β} = 𝔩_k`.** -/
theorem smallD_mul_iff (k : HeightOneSpectrum (𝓞 F) → ℤ) {β : F} (hβ : β ≠ 0) (x : F) :
    SmallD 𝔪 k (β * x) ↔ SmallD 𝔪 (fun v => k v - ordv v β) x := by
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  by_cases hx : x = 0
  · simp [hx]
  show v.valuation F (β * x) ≤ WithZero.exp (-(k v))
    ↔ v.valuation F x ≤ WithZero.exp (-(k v - ordv v β))
  rw [map_mul, val_eq_exp_ordv v hβ, val_eq_exp_ordv v hx, ← WithZero.exp_add,
    WithZero.exp_le_exp, WithZero.exp_le_exp]
  constructor <;> intro h <;> omega

theorem mem_latD {k : HeightOneSpectrum (𝓞 F) → ℤ} {x : F} : x ∈ latD 𝔪 k ↔ SmallD 𝔪 k x :=
  Iff.rfl

theorem absNorm_ne_zero' (v : HeightOneSpectrum (𝓞 F)) : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by omega
  exact_mod_cast h0

open NumberField.HeightOneSpectrum in
/-- `|x|_v = q_v^{-ord_v x}`. -/
theorem adicAbv_eq_zpow (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    adicAbv F v x = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) := by
  have hq0 := absNorm_ne_zero' v
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := lt_of_le_of_ne (Nat.cast_nonneg _) hq0.symm
  refine le_antisymm (abv_le_of_val_le v (le_of_eq (val_eq_exp_ordv v hx))) ?_
  have h2 : adicAbv F v x⁻¹ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(-ordv v x)) := by
    refine abv_le_of_val_le v (le_of_eq ?_)
    rw [map_inv₀, val_eq_exp_ordv v hx, ← WithZero.exp_neg]
  rw [map_inv₀, neg_neg] at h2
  have hpos : 0 < adicAbv F v x := (adicAbv F v).pos hx
  rw [zpow_neg]
  rw [inv_le_comm₀ hpos (zpow_pos hq _)] at h2
  exact h2

/-- `|x|_{S_f} = ∏_{v ∣ 𝔪} q_v^{-ord_v x}`. -/
theorem absS_eq_prod {x : F} (hx : x ≠ 0) :
    absS 𝔪 x = ∏ v ∈ CubicPkg.sFin 𝔪, (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) :=
  Finset.prod_congr rfl fun v _ => adicAbv_eq_zpow v hx

theorem volD_sub_ordv (k : HeightOneSpectrum (𝓞 F) → ℤ) {β : F} (hβ : β ≠ 0) :
    volD 𝔪 k = absS 𝔪 β * volD 𝔪 (fun v => k v - ordv v β) := by
  rw [absS_eq_prod hβ, volD, volD, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← zpow_add₀ (absNorm_ne_zero' v)]
  congr 1
  ring

section jacD

variable (ψ : SfChar 𝔪) {k : HeightOneSpectrum (𝓞 F) → ℤ} {f : F → ℂ} {ν : F}

theorem jacD_const_mul (C : ℂ) : jacD ψ k (fun u => C * f u) ν = C * jacD ψ k f ν := by
  simp only [jacD, mul_assoc]
  rw [tsum_mul_left]
  ring

end jacD

/-- Multiplication by `β⁻¹` as an additive automorphism of `F`. -/
def mulInvE (β : F) (hβ : β ≠ 0) : F ≃+ F where
  toFun u := β⁻¹ * u
  invFun u := β * u
  left_inv u := by field_simp
  right_inv u := by field_simp
  map_add' u w := by ring

theorem map_mulInvE (k : HeightOneSpectrum (𝓞 F) → ℤ) {β : F} (hβ : β ≠ 0) :
    (latD 𝔪 k).map (mulInvE β hβ : F →+ F) = latD 𝔪 (fun v => k v - ordv v β) := by
  ext x
  rw [AddSubgroup.mem_map, mem_latD, ← smallD_mul_iff k hβ]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : β * (mulInvE β hβ : F →+ F) y = y := by
      change β * (β⁻¹ * y) = y
      field_simp
    rw [e]
    exact hy
  · intro hx
    refine ⟨β * x, hx, ?_⟩
    change β⁻¹ * (β * x) = x
    field_simp

/-- **Substitution `u = β u'`** in the finite Jacquet functional. -/
theorem jacD_subst (ψ : SfChar 𝔪) {k : HeightOneSpectrum (𝓞 F) → ℤ} {g : F → ℂ} {ν β : F}
    (hβ : β ≠ 0)
    (hg : ∀ x h : F, SmallD 𝔪 (fun v => k v - ordv v β) h → g (x + h) = g x)
    (hψ : ∀ h : F, SmallD 𝔪 (fun v => k v - ordv v β) h → ψ (ν * β * h) = 1) :
    jacD ψ k (fun u => g (u / β)) ν
      = (absS 𝔪 β : ℂ) * jacD ψ (fun v => k v - ordv v β) g (ν * β) := by
  set k' : HeightOneSpectrum (𝓞 F) → ℤ := fun v => k v - ordv v β with hk'
  have hdiv : ∀ h : F, SmallD 𝔪 k h → SmallD 𝔪 k' (h / β) := by
    intro h hh
    rw [hk', ← smallD_mul_iff k hβ]
    rwa [mul_div_cancel₀ _ hβ]
  have hf₁ : ∀ x h : F, SmallD 𝔪 k h → g ((x + h) / β) = g (x / β) := by
    intro x h hh
    rw [add_div]
    exact hg _ _ (hdiv h hh)
  have hψ₁ : ∀ h : F, SmallD 𝔪 k h → ψ (ν * h) = 1 := by
    intro h hh
    have := hψ (h / β) (hdiv h hh)
    rwa [mul_assoc, mul_div_cancel₀ _ hβ] at this
  set φ : F ⧸ latD 𝔪 k ≃+ F ⧸ latD 𝔪 k' :=
    QuotientAddGroup.congr (latD 𝔪 k) (latD 𝔪 k') (mulInvE β hβ) (map_mulInvE k hβ) with hφ
  set G : F ⧸ latD 𝔪 k' → ℂ := fun w => g w.out * (starRingEnd ℂ) (ψ (ν * β * w.out)) with hG
  have key : ∀ u : F ⧸ latD 𝔪 k,
      g (u.out / β) * (starRingEnd ℂ) (ψ (ν * u.out)) = G (φ u) := by
    intro u
    induction u using QuotientAddGroup.induction_on with
    | H x =>
      have e1 := jacD_term ψ (f := fun u => g (u / β)) hf₁ hψ₁ x
      have e2 : φ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (β⁻¹ * x) := rfl
      rw [e1, e2, hG]
      simp only
      rw [jacD_term ψ hg hψ (β⁻¹ * x)]
      congr 2
      · field_simp
      · field_simp
  rw [jacD, jacD]
  simp only [key]
  rw [show (∑' u : F ⧸ latD 𝔪 k, G (φ u)) = ∑' w, G w from φ.toEquiv.tsum_eq G,
    volD_sub_ordv k hβ]
  push_cast
  ring

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem cpow_sq_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x ^ 2 * y : ℝ) : ℂ) ^ s = (y : ℂ) ^ s * ((x : ℂ) ^ (2 * s - 1) * x) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h1 : (x : ℂ) ^ (2 * s - 1) * x = (x : ℂ) ^ s * (x : ℂ) ^ s := by
    have e : (x : ℂ) ^ (2 * s - 1) * x = (x : ℂ) ^ (2 * s - 1) * (x : ℂ) ^ (1 : ℂ) := by
      rw [Complex.cpow_one]
    rw [e, ← Complex.cpow_add _ _ hx0, ← Complex.cpow_add _ _ hx0]
    congr 1
    ring
  have h2 : ((x ^ 2 * y : ℝ) : ℂ) = ((x * x : ℝ) : ℂ) * (y : ℂ) := by push_cast; ring
  rw [h2, Complex.mul_cpow_ofReal_nonneg (mul_nonneg hx.le hx.le) hy.le, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx.le hx.le, h1]
  ring

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S2_Kubota
/-!
# WP-S2, part 8: the normalized finite Jacquet functional `Lam` and the laws of `E.Kubota`

`Lam ψ hG Φ c ν s := |c|_{S_f}^s · J_Φ(c; ν, s)`, the functional of WP-S (`S.lam`) taken at a
valid depth; by `jacD_eq_of_le` it does not depend on the valid depth (`Lam_eq_lamD`).

* `Lam_unit` (J1), `Lam_cube` (S1³), `Lam_act` (MATH2 Lemma 6.1 (iii), any frequency),
  `torusT_torusT_inv` and `Lam_act_surj`: the laws required by the interface `E.Kubota`.
* `kubota`: the instance `E.Kubota (cubicSymbol …) (B7.sAdd 𝔪 h𝔪) (GSection ι P 𝔪)` with
  `act β = Ã(β)`, **given** its field `summable` as a hypothesis.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem jac_const_mul (ψ : SfChar 𝔪) (M : ℤ) (f : F → ℂ) (ν : F) (C : ℂ) :
    jac ψ M (fun u => C * f u) ν = C * jac ψ M f ν :=
  jacD_const_mul ψ (k := fun _ => M) C

theorem cpow_mul_cpow_neg {x : ℝ} (hx : 0 < x) (w : ℂ) : (x : ℂ) ^ w * (x : ℂ) ^ (-w) = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [← Complex.cpow_add _ _ hx0, add_neg_cancel, Complex.cpow_zero]

/-- (J1) `λ(Φ; εc) = ⟨c, ε⟩ λ(Φ; c)` for `ε ∈ U_S`, at any depth. -/
theorem lam_unit (ψ : SfChar 𝔪) (M : ℤ) (Φ : GSection ι P 𝔪) (ε : (SInt 𝔪)ˣ) {c : F}
    (hc : c ≠ 0) (ν : F) (s : ℂ) :
    lam ψ M Φ (((ε : SInt 𝔪) : F) * c) ν s
      = brk ι P 𝔪 c ((ε : SInt 𝔪) : F) * lam ψ M Φ c ν s := by
  have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
  have hfun : (fun u => Φ s (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * c * u))
      = fun u => (brk ι P 𝔪 c ((ε : SInt 𝔪) : F)
          * ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s)) * Φ s c (c * u) := by
    funext u
    rw [mul_assoc, Φ.hom, Xs_of_ne _ hc]
  rw [lam, lam, hfun, jac_const_mul, absS_mul,
    ofReal_mul_cpow (absS_nonneg _) (absS_nonneg _)]
  linear_combination (brk ι P 𝔪 c ((ε : SInt 𝔪) : F) * ((absS 𝔪 c : ℝ) : ℂ) ^ s
    * jac ψ M (fun u => Φ s c (c * u)) ν) * cpow_mul_cpow_neg (absS_pos hε0) s

/-- (S1³) `λ(Φ; t³c) = λ(Φ; c)`, at any depth. -/
theorem lam_cube (ψ : SfChar 𝔪) (M : ℤ) (Φ : GSection ι P 𝔪) {t : F} (ht : t ≠ 0) (c ν : F)
    (s : ℂ) : lam ψ M Φ (t ^ 3 * c) ν s = lam ψ M Φ c ν s := by
  have hfun : (fun u => Φ s (t ^ 3 * c) (t ^ 3 * c * u))
      = fun u => ((absS 𝔪 t : ℝ) : ℂ) ^ (-(3 * s)) * Φ s c (c * u) := by
    funext u
    rw [mul_assoc, Φ.cube s t ht]
  have h3 : ((absS 𝔪 t ^ 3 : ℝ) : ℂ) ^ s = ((absS 𝔪 t : ℝ) : ℂ) ^ (3 * s) := by
    rw [ofReal_pow_cpow (absS_pos ht)]
    norm_num
  rw [lam, lam, hfun, jac_const_mul, absS_mul, absS_pow,
    ofReal_mul_cpow (pow_nonneg (absS_nonneg _) 3) (absS_nonneg _), h3]
  linear_combination (((absS 𝔪 c : ℝ) : ℂ) ^ s * jac ψ M (fun u => Φ s c (c * u)) ν)
    * cpow_mul_cpow_neg (absS_pos ht) (3 * s)

theorem Lam_unit (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (ε : (SInt 𝔪)ˣ) {c : F}
    (hc : c ≠ 0) (ν : F) (s : ℂ) :
    Lam ψ hG Φ (((ε : SInt 𝔪) : F) * c) ν s
      = brk ι P 𝔪 c ((ε : SInt 𝔪) : F) * Lam ψ hG Φ c ν s :=
  lam_unit ψ _ Φ ε hc ν s

theorem Lam_cube (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {t : F} (ht : t ≠ 0)
    (c ν : F) (s : ℂ) : Lam ψ hG Φ (t ^ 3 * c) ν s = Lam ψ hG Φ c ν s :=
  lam_cube ψ _ Φ ht c ν s

/-- MATH2 Lemma 6.1 (iii) at an arbitrary frequency, on the lattice `β 𝔩_M`. -/
theorem lamD_torusT (ψ : SfChar 𝔪) (hG : Good 𝔪) (M : ℤ) (Φ : GSection ι P 𝔪) {c β : F}
    (hc : c ≠ 0) (hβ : β ≠ 0) (ν : F) (s : ℂ)
    (hper : ∀ b : F, Small 𝔪 M b → ∀ c d : F, Φ s c (d + c * b) = Φ s c d)
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * β * h) = 1) :
    lamD ψ (fun v => M + ordv v β) (Φ.torusT hG β hβ) c ν s
      = brk ι P 𝔪 c β ^ 2 * lam ψ M Φ (β ^ 2 * c) (ν * β) s := by
  set g : F → ℂ := fun u => Φ s (β ^ 2 * c) (β ^ 2 * c * u) with hg
  have hfun : (fun u => (Φ.torusT hG β hβ) s c (c * u))
      = fun u => (((absS 𝔪 β : ℝ) : ℂ) ^ (2 * s - 1) * brk ι P 𝔪 c β ^ 2) * g (u / β) := by
    funext u
    rw [GSection.torusT_apply, tf, if_neg hc, hg]
    have e : β * (c * u) = β ^ 2 * c * (u / β) := by field_simp
    simp only
    rw [e]
    ring
  have hk : (fun v : HeightOneSpectrum (𝓞 F) => M + ordv v β - ordv v β) = fun _ => M := by
    funext v; ring
  have hsub := jacD_subst ψ (k := fun v => M + ordv v β) (g := g) (ν := ν) hβ
    (by
      rw [hk]
      intro x h hh
      rw [hg]
      simp only
      rw [mul_add]
      exact hper h hh _ _)
    (by
      rw [hk]
      exact hψ)
  rw [hk, jacD_const] at hsub
  rw [lamD, hfun, jacD_const_mul, hsub, lam, absS_mul, absS_pow,
    cpow_sq_mul (absS_pos hβ) (absS_pos hc)]
  ring

/-- `Ã(β)` shifts the valid depths by `ord β`. -/
theorem valid_torusT (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0)
    {ν : F} {M : ℤ} (h : Valid ψ Φ (β * ν) (fun _ => M)) :
    Valid ψ (Φ.torusT hG β hβ) ν (fun v => M + ordv v β) := by
  have hk : (fun v : HeightOneSpectrum (𝓞 F) => M + ordv v β - ordv v β) = fun _ => M := by
    funext v; ring
  have hdiv : ∀ b : F, SmallD 𝔪 (fun v => M + ordv v β) b → Small 𝔪 M (b / β) := by
    intro b hb
    have h1 : SmallD 𝔪 (fun v => M + ordv v β) (β * (b / β)) := by
      rwa [mul_div_cancel₀ _ hβ]
    have h2 := (smallD_mul_iff _ hβ _).mp h1
    rwa [hk] at h2
  refine ⟨fun b hb s c d => ?_, fun x hx => ?_⟩
  · have htf : tf ι P 𝔪 β c (d + c * b) = tf ι P 𝔪 β c d := by
      by_cases hc : c = 0
      · rw [hc, zero_mul, add_zero]
      · rw [tf, if_neg hc, tf, if_neg hc]
    have e : β * (d + c * b) = β * d + β ^ 2 * c * (b / β) := by field_simp
    rw [GSection.torusT_apply, GSection.torusT_apply, htf, e, h.1 (b / β) (hdiv b hb)]
  · have := h.2 (x / β) (hdiv x hx)
    rwa [mul_comm β ν, mul_assoc, mul_div_cancel₀ _ hβ] at this

/-- **MATH2 Lemma 6.1 (iii)**: `Lam (Ã(β)Φ) c ν = ⟨c, β⟩² Lam Φ (β²c) (βν)`. -/
theorem Lam_act (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β c : F} (hβ : β ≠ 0)
    (hc : c ≠ 0) (ν : F) (s : ℂ) :
    Lam ψ hG (Φ.torusT hG β hβ) c ν s
      = brk ι P 𝔪 c β ^ 2 * Lam ψ hG Φ (β ^ 2 * c) (β * ν) s := by
  have hv := valid_depth ψ hG Φ (β * ν)
  have hv₁ := valid_torusT ψ hG Φ hβ hv
  rw [Lam_eq_lamD ψ hG _ hv₁, Lam,
    lamD_torusT ψ hG _ Φ hc hβ ν s (fun b hb c d => hv.1 b hb s c d)
      (fun h hh => by rw [mul_comm ν β]; exact hv.2 h hh), mul_comm ν β]

/-- `Ã(β) Ã(β⁻¹) = 1`. -/
theorem torusT_torusT_inv (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    (Φ.torusT hG β⁻¹ (inv_ne_zero hβ)).torusT hG β hβ = Φ := by
  ext s c d
  rw [GSection.torusT_apply, GSection.torusT_apply]
  have e1 : β⁻¹ ^ 2 * (β ^ 2 * c) = c := by field_simp
  have e2 : β⁻¹ * (β * d) = d := by field_simp
  rw [e1, e2]
  have key : tf ι P 𝔪 β c d * tf ι P 𝔪 β⁻¹ (β ^ 2 * c) (β * d) = 1 := by
    by_cases hc : c = 0
    · rw [hc, mul_zero, tf, if_pos rfl, tf, if_pos rfl]
      by_cases hd : d = 0
      · simp [hd]
      · rw [brk_mul_left _ hβ hd, brk_inv_right, brk_inv_right, brk_self, inv_one, one_mul]
        exact mul_inv_cancel₀ (brk_ne_zero _ _)
    · have h0 := brk_ne_zero (ι := ι) (P := P) (𝔪 := 𝔪) c β
      rw [tf, if_neg hc, tf, if_neg (mul_ne_zero (pow_ne_zero 2 hβ) hc),
        brk_mul_left _ (pow_ne_zero 2 hβ) hc, brk_inv_right, brk_inv_right, pow_two β,
        brk_mul_left _ hβ hβ, brk_self]
      field_simp
  have hcp : ((absS 𝔪 β : ℝ) : ℂ) ^ (2 * s - 1) * ((absS 𝔪 β⁻¹ : ℝ) : ℂ) ^ (2 * s - 1) = 1 := by
    rw [absS_inv, ← ofReal_mul_cpow (absS_nonneg _) (inv_nonneg.mpr (absS_nonneg _)),
      mul_inv_cancel₀ (absS_pos hβ).ne', Complex.ofReal_one, Complex.one_cpow]
  linear_combination (Φ s c d * tf ι P 𝔪 β c d * tf ι P 𝔪 β⁻¹ (β ^ 2 * c) (β * d)) * hcp
    + (Φ s c d) * key

/-- `Ã(β)` is onto. -/
theorem Lam_act_surj (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    ∃ Φ' : GSection ι P 𝔪, ∀ (c ν : F) (s : ℂ),
      Lam ψ hG (Φ'.torusT hG β hβ) c ν s = Lam ψ hG Φ c ν s :=
  ⟨Φ.torusT hG β⁻¹ (inv_ne_zero hβ), fun c ν s => by rw [torusT_torusT_inv hG Φ hβ]⟩

/-! ### The interface `E.Kubota` -/

section instance_

open ArtinKP.B7 ArtinKP.E

variable (ψ : SfChar 𝔪) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

open Classical in
/-- `Ã(β)` for `β ∈ R` (the identity for `β = 0`). -/
def actR (β : SInt 𝔪) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 :=
  if h : (β : F) = 0 then Φ else Φ.torusT hG (β : F) h

/-- **The `E.Kubota` instance on genuine sections**, with `act β = Ã(β)`,
`Lam Φ c ν s = |c|_{S_f}^s J_Φ(c; ν, s)`, `br = ι (·,·)_S`, for any `S_f`-continuous additive
character `ψ`; the field `summable` is a hypothesis. -/
def kubota
    (hsum : ∀ (Φ : GSection ι P 𝔪) (ν : SInt 𝔪) (s : ℂ), ν ≠ 0 → 2 < s.re →
      Summable (fun a : Cls (SInt 𝔪) =>
        gauss (cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)
          * LamR ψ hG Φ (rp a.1) ν s * nrm (rp a.1) ^ (-s))) :
    Kubota (cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) (GSection ι P 𝔪) where
  toPairing := pairing ι P hG hz6
  act := actR hG
  Lam := LamR ψ hG
  Lam_unit Φ u c ν s hu hc _ := by
    obtain ⟨ε, rfl⟩ := hu
    have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
    have hεF : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
    have h1 := Lam_unit ψ hG Φ ε hcF (ν : F) s
    have h2 : (cubicSymbol ι P hG hz6).sym (ε : SInt 𝔪) c
        = brk ι P 𝔪 (c : F) ((ε : SInt 𝔪) : F) := by
      rw [cubicSymbol_sym, cubicExt_unit_left ι P hG hz6 c (ε : SInt 𝔪) (Units.mk0 _ hcF)
        (Units.mk0 _ hεF) rfl rfl (unit_val_eq_one ε), ← brk_units]
      rfl
    rw [h2]
    exact h1
  Lam_cube Φ t c ν s ht _ _ := by
    have htF : (t : F) ≠ 0 := fun h => ht (Subtype.ext h)
    exact Lam_cube ψ hG Φ htF (c : F) (ν : F) s
  Lam_act Φ β c ν s hβ hc _ := by
    have hβF : (β : F) ≠ 0 := fun h => hβ (Subtype.ext h)
    have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
    have h1 := Lam_act ψ hG Φ hβF hcF (ν : F) s
    have h2 : (pairing ι P hG hz6).br c β = brk ι P 𝔪 (c : F) (β : F) := pairing_br ι P hG hz6 hc hβ
    rw [h2]
    simp only [actR, dif_neg hβF, LamR]
    exact h1
  act_surj β Φ hβ := by
    have hβF : (β : F) ≠ 0 := fun h => hβ (Subtype.ext h)
    obtain ⟨Φ', hΦ'⟩ := Lam_act_surj ψ hG Φ hβF
    refine ⟨Φ', fun c ν s _ _ => ?_⟩
    simp only [actR, dif_neg hβF, LamR]
    exact hΦ' _ _ s
  summable := hsum

end instance_

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.B_Kub
/-!
# WP-B, part 9: the Kubota series — convergence, holomorphy, the `E.Kubota` instance

* `kTerm`, `aCoeff`: `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`, for every
  `ν ∈ R` (`ν = 0` gives the Dirichlet series of the constant term), with
  `Lam = S2.LamR ψ_{S_f}` (WP-S2's normalized finite Jacquet functional at a valid depth).
* `exists_majorant_kTerm`: locally uniform absolute convergence on `Re s > 2`
  (`|g(ν,c)| ≤ N(c)`, `S2.norm_Lam_le`, S-1, `∑ N(c)^{1-σ} < ∞`).
* `differentiableOn_aCoeff`: holomorphy on `Re s > 2`.
* `kubota hG hz6 : E.Kubota (S2.cubicSymbol …) (B7.sAdd 𝔪 _) (GSection ι P 𝔪)` — no hypothesis left.
* `fourier_coeff_aSer`, `const_term_aCoeff`: the Fourier coefficients in this normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

/-- **The Kubota series** `𝔞_Φ(ν, s)`, for every `ν ∈ R`. -/
def aCoeff (s : ℂ) : ℂ := ∑' a : Cls (SInt 𝔪), kTerm hG hz6 Φ ν a s

/-- **The `E.Kubota` instance on genuine sections** (WP-E §1, §4 item 2): `act β = Ã(β)`,
`Lam Φ c ν s = |c|_{S_f}^s J_Φ(c; ν, s)` for `ψ_{S_f} = psiS`, `br = ι (·,·)_S`. -/
def kubota : Kubota (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) (GSection ι P 𝔪) :=
  S2.kubota (psiS hG.ne_bot) hG hz6 fun Φ ν _ _ hs => summable_kTerm_of_two_lt_re hG hz6 Φ ν hs

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RO_Cusps
/-! # WP-RO, file 2: finitely many cusp orbits ((O) of MATH2 §0.1)

`S` is an arbitrary finite set of finite places of the number field `F`.

* `exists_SL2_of_span_eq`: in a Dedekind domain, two pairs generating the same nonzero ideal differ
  by a matrix of `SL₂` (entries in `𝔞𝔞⁻¹`, written without fractional ideals).
* `HasClass q g`: the primitive pair `q` has an `S`-unit multiple in `𝓞²` generating an ideal of
  class `g ∈ Cl(F)`; every `q` has a class (`exists_hasClass`, from `B1.exists_unit_rescale`), and two
  pairs with a common class are in one `SL₂(𝓞)`-orbit modulo `S`-units (`exists_act_of_hasClass`).
* `finiteCusps S : B1.FiniteCusps S`, unconditionally; `finite_orbits_SL2` the same as a finite set of
  classes.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.B1 ArtinKP.X

noncomputable section

/-! ### Pairs generating the same ideal -/

variable {F : Type*} [Field F] [NumberField F] {S : Finset (FinitePlace F)}

/-! ### Proportional primitive pairs -/

/-! ### The ideal class of a pair -/

/-- `q` has an `S`-unit multiple in `𝓞²` generating an ideal of class `g`. -/
def HasClass (q : SPair S) (g : ClassGroup (𝓞 F)) : Prop :=
  ∃ (u : F) (c d : 𝓞 F) (I : nonZeroDivisors (Ideal (𝓞 F))), IsSUnit S u ∧ (c : F) = u * q.c ∧
    (d : F) = u * q.d ∧ (I : Ideal (𝓞 F)) = Ideal.span {c, d} ∧ ClassGroup.mk0 I = g

/-! ### Finiteness -/

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.RO_Bridge
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.B.Row.inf_d _root_.ArtinKP.S.GSection.twist_apply
/-! # WP-RO, file 3: the bridge `S.Row 𝔪 / U_S ≃ B1.PairClass (SOf 𝔪)`

`h𝔪 : 𝔪 ≠ ⊥` throughout (no other hypothesis on `𝔪`).

* `rowPair`, `rowClass h𝔪 : Row 𝔪 → PairClass (SOf 𝔪)`; `rowClass_eq_iff` (fibres = `U_S`-orbits),
  `rowClass_surjective`, `rowClassEquiv : orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪) ≃ PairClass (SOf 𝔪)`.
* actions: `intMat 𝔪 : SL₂(𝓞) →* SL₂(R)` (the map defining `Gamma 𝔪 𝔫`), `rowClass_act_intMat`
  (`SL₂(𝓞)`), `rowClass_act` (`SL₂(R)`, through `A.toF` and `B1.PairClass.actR`), `rowClass_bot`,
  `exists_toF_eq` (every `IsSMat` matrix comes from `SL₂(R)`).
* norms and heights: `sNorm_SOf` (`X.sNorm (SOf 𝔪) = S.normS 𝔪`), `ht_rowClass`
  (`ht_p(P) = I_p(P) / ‖p‖`), `prod_SOf_eq_absS`, and the product formula for `S`-units
  `prod_normSq_mul_absS : N_∞(ε) · |ε|_{S_f} = 1` (WP-S open issue 7), `pairHt_smul_row`.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1 ArtinKP.X ArtinKP.S

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Rows and pair classes -/

/-- A primitive row of `SInt 𝔪` as a primitive pair in the sense of WP-B1. -/
def rowPair (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) : SPair (SOf 𝔪) where
  c := (p.c : F)
  d := (p.d : F)
  hc := isSInt_coe h𝔪 p.c
  hd := isSInt_coe h𝔪 p.d
  prim := by
    obtain ⟨u, v, huv⟩ := p.2
    refine ⟨(u : F), (v : F), isSInt_coe h𝔪 u, isSInt_coe h𝔪 v, ?_⟩
    exact congrArg (fun x : SInt 𝔪 => (x : F)) huv

@[simp] theorem rowPair_c (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) : (rowPair h𝔪 p).c = (p.c : F) := rfl

@[simp] theorem rowPair_d (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) : (rowPair h𝔪 p).d = (p.d : F) := rfl

/-- The pair class of a row. -/
def rowClass (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) : PairClass (SOf 𝔪) := ⟦rowPair h𝔪 p⟧

/-- A primitive pair in the sense of WP-B1 as a row. -/
def pairRow (h𝔪 : 𝔪 ≠ ⊥) (q : SPair (SOf 𝔪)) : Row 𝔪 :=
  ⟨(⟨q.c, (isSInt_SOf_iff h𝔪 _).mp q.hc⟩, ⟨q.d, (isSInt_SOf_iff h𝔪 _).mp q.hd⟩), by
    obtain ⟨a, b, ha, hb, hab⟩ := q.prim
    exact ⟨⟨a, (isSInt_SOf_iff h𝔪 _).mp ha⟩, ⟨b, (isSInt_SOf_iff h𝔪 _).mp hb⟩, Subtype.ext hab⟩⟩

theorem rowClass_surjective (h𝔪 : 𝔪 ≠ ⊥) : Function.Surjective (rowClass (𝔪 := 𝔪) h𝔪) := by
  intro p
  induction p using Quotient.inductionOn with
  | _ q => exact ⟨pairRow h𝔪 q, rfl⟩

theorem rowClass_smul (h𝔪 : 𝔪 ≠ ⊥) (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) :
    rowClass h𝔪 (ε • p) = rowClass h𝔪 p :=
  (Quotient.sound ⟨((ε : SInt 𝔪) : F), isSUnit_coe_unit h𝔪 ε, rfl, rfl⟩ :
    rowClass h𝔪 p = rowClass h𝔪 (ε • p)).symm

/-- **The fibres of `rowClass` are the `U_S`-orbits.** -/
theorem rowClass_eq_iff (h𝔪 : 𝔪 ≠ ⊥) {p q : Row 𝔪} :
    rowClass h𝔪 p = rowClass h𝔪 q ↔ ∃ ε : (SInt 𝔪)ˣ, q = ε • p := by
  constructor
  · intro h
    obtain ⟨u, hu, h1, h2⟩ := Quotient.exact h
    obtain ⟨ε, hε⟩ := exists_unit_of_isSUnit h𝔪 hu
    refine ⟨ε, Row.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · change (q.c : F) = ((ε : SInt 𝔪) : F) * (p.c : F)
      rw [hε]; exact h1
    · change (q.d : F) = ((ε : SInt 𝔪) : F) * (p.d : F)
      rw [hε]; exact h2
  · rintro ⟨ε, rfl⟩
    exact (rowClass_smul h𝔪 ε p).symm

/-- `Row 𝔪 / U_S ≃ PairClass (SOf 𝔪)`. -/
def rowClassEquiv (h𝔪 : 𝔪 ≠ ⊥) :
    MulAction.orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪) ≃ PairClass (SOf 𝔪) :=
  Equiv.ofBijective
    (Quotient.lift (rowClass h𝔪) (by
      rintro p q ⟨ε, rfl⟩
      exact rowClass_smul h𝔪 ε q))
    ⟨by
      intro a b
      induction a using Quotient.inductionOn with
      | _ p =>
      induction b using Quotient.inductionOn with
      | _ q =>
        intro h
        obtain ⟨ε, rfl⟩ := (rowClass_eq_iff h𝔪).mp h
        exact (Quotient.sound ⟨ε, rfl⟩ : (⟦ε • p⟧ : MulAction.orbitRel.Quotient _ _) = ⟦p⟧).symm,
     fun c => by
      obtain ⟨p, rfl⟩ := rowClass_surjective h𝔪 c
      exact ⟨⟦p⟧, rfl⟩⟩

@[simp] theorem rowClassEquiv_mk (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) :
    rowClassEquiv h𝔪 (⟦p⟧ : MulAction.orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪)) = rowClass h𝔪 p := rfl

/-! ### Actions -/

/-- `SL₂(𝓞_F) → SL₂(R)`; `Gamma 𝔪 𝔫` is the image under this map of the principal congruence
subgroup. -/
def intMat (𝔪 : Ideal (𝓞 F)) : SL(2, 𝓞 F) →* SL(2, SInt 𝔪) :=
  Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) (SInt 𝔪))

@[simp] theorem intMat_apply (γ : SL(2, 𝓞 F)) (i j : Fin 2) :
    (((intMat 𝔪 γ) i j : SInt 𝔪) : F) = ((γ i j : 𝓞 F) : F) := rfl

/-! ### Norms and heights -/

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.X2_Calc
/-! # WP-X2, file 2: calculus in the logarithmic chart

On `Coord F = InfinitePlace F → ℂ × ℝ` (coordinates `(x_w, t_w)`, `v_w = exp t_w`):

* `pd w k U` — partial derivative in the direction `bvec w k` (`k = 0, 1`: real and imaginary
  part of `x_w`; `k = 2`: `t_w`);
* `lapE U = ∑_w (-(e^{2t_w}(∂₀² + ∂₁²) + ∂₂²) U + 2 ∂₂ U)` — the Laplacian
  `∑_w (-v_w²(∂²_{x₁} + ∂²_{x₂} + ∂²_v) + v_w ∂_v)` in the chart;
* `gamE U W = ∑_w (e^{2t_w}(∂₀U ∂₀W + ∂₁U ∂₁W) + ∂₂U ∂₂W)` — the (bilinear) carré du champ
  `∑_w v_w² ∇_w U · ∇_w W`;
* `green_E`: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` when one of `T`, `U` has compact support;
* Leibniz rules, compatibility with conjugation.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

lemma acoef_pos (k : Fin 3) (p : E1) : 0 < acoef k p := by
  unfold acoef; split_ifs <;> positivity

/-! ### Regularity -/

/-! ### Algebraic rules -/

/-! ### The weights `ρ · a_k` -/

/-! ### Green's identity on the chart -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
/-! # WP-X, file 7: `L²` of the quotient and local restriction maps (abstract)

For a partition of unity `η` and a measurable set `B` meeting each orbit at most `m < ∞` times,
pulling back and restricting is a bounded operator
`restrictL2 : L²(G \ α) →L[ℂ] L²(B, μ)` of norm `≤ √m`.  Every functional
`u ↦ ∫_B conj ψ · u` with `ψ ∈ L²(B)` is therefore continuous on `L²(G \ α)`
(`pairingL2`).  This is the continuity of Fourier-coefficient functionals (MATH (C6)).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {η : α → ℝ≥0∞}

/-- **Restriction to a set of finite multiplicity** as a bounded operator
`L²(G \ α) → L²(B, μ)`. -/
def restrictL2 (hη : IsPOU G η) {B : Set α} (hB : MeasurableSet B) {m : ℝ≥0∞} (hmtop : m ≠ ⊤)
    (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m) :
    Lp ℂ 2 (quotMeasure G η μ) →L[ℂ] Lp ℂ 2 (μ.restrict B) :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_liftQ_restrict hη hB hmtop hm u).toLp (liftQ u)
      map_add' := by
        intro u v
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (ae_restrict_of_ae ?_)
        exact liftQ_ae_eq hη (Lp.coeFn_add u v)
      map_smul' := by
        intro c u
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (ae_restrict_of_ae ?_)
        exact liftQ_ae_eq hη (Lp.coeFn_smul c u) }
    ((m ^ (1 / 2 : ℝ)).toReal)
    (by
      intro u
      change ‖(memLp_liftQ_restrict hη hB hmtop hm u).toLp (liftQ u)‖ ≤ _
      rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono
        (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hmtop)
          (Lp.eLpNorm_ne_top u))
        (eLpNorm_liftQ_restrict_le hη hB m hm u))

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
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

/-- **Restriction to a box** is a bounded operator `L²(Γ\X) → L²(box n)`. -/
def X.restrictBox (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) :
    X.L2 Γ →L[ℂ] Lp ℂ 2 ((X.vol F).restrict (X.box n)) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  restrictL2 (X.isPOU_pou Γ) (X.measurableSet_box n) (ENNReal.natCast_ne_top _)
    (X.tsum_indicator_box_le_boxMult Γ n)

/-- A bounded measurable function as an element of `L²(box n)`. -/
def X.boxLp (n : ℕ) (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) :
    Lp ℂ 2 ((X.vol F).restrict (X.box n)) :=
  (MemLp.of_bound (μ := (X.vol F).restrict (X.box n)) (p := 2) hψ.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)).toLp ψ

/-- **Coefficient functionals** (MATH (C6)): for bounded measurable `ψ`,
`u ↦ ∫_{box n} conj ψ · u` is a continuous linear functional on `L²(Γ\X)`. -/
def X.coeffFunctional (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (ψ : X F → ℂ) (hψ : Measurable ψ)
    (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) : X.L2 Γ →L[ℂ] ℂ :=
  (innerSL ℂ (X.boxLp n ψ hψ C hC)).comp (X.restrictBox Γ n)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.CAbs_Residue
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-!
# WP-C-abs, part 1: the strong residue of the resolvent of a bounded self-adjoint operator

`T` bounded self-adjoint on a complex Hilbert space `H`, `t₀` real, `P₀` the orthogonal projection
onto `ker (T - t₀)`.  For `z → t₀` inside a cone `|Re (z - t₀)| ≤ C * |Im z|`,
`(t₀ - z) • (T - z)⁻¹ x → P₀ x` for every `x` (MATH.md, Lemma C1).  No spectral theorem is used.
-/

namespace ArtinKP.CAbs

open Filter Topology ComplexConjugate
open scoped InnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `(T - z)⁻¹` as a bounded operator (junk value `0` when `T - z` is not invertible). -/
def shiftInv (T : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  Ring.inverse (T - z • (1 : H →L[ℂ] H))

/-- The eigenspace `ker (T - t)` as a (closed) submodule of `H`. -/
def eigenspace (T : H →L[ℂ] H) (t : ℂ) : Submodule ℂ H :=
  LinearMap.ker ((T - t • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)

lemma isClosed_eigenspace (T : H →L[ℂ] H) (t : ℂ) : IsClosed (eigenspace T t : Set H) := by
  have : (eigenspace T t : Set H) = (T - t • (1 : H →L[ℂ] H)) ⁻¹' {0} := by
    ext x; simp [eigenspace]
  rw [this]
  exact isClosed_singleton.preimage (T - t • (1 : H →L[ℂ] H)).continuous

instance instCompleteSpaceSubtypeMemSubmoduleComplexEigenspace (T : H →L[ℂ] H) (t : ℂ) : CompleteSpace (eigenspace T t) :=
  (isClosed_eigenspace T t).completeSpace_coe

instance instHasOrthogonalProjectionComplexEigenspace (T : H →L[ℂ] H) (t : ℂ) : (eigenspace T t).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The orthogonal projection of `H` onto `ker (T - t)`. -/
def eigenProj (T : H →L[ℂ] H) (t : ℂ) : H →L[ℂ] H :=
  (eigenspace T t).starProjection

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.CAbs_Form
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-!
# WP-C-abs, part 2: the form operator and the variational resolvent

Abstract setting (MATH.md §3.1): `H` plays `L²`, `V` plays `H¹`.  The data is a bounded map
`j : V →L[ℂ] H`, injective, with dense range and `‖j u‖ ≤ ‖u‖`.  The Dirichlet form is *defined* by
`𝔇(u, u') := ⟪u, u'⟫_V - ⟪j u, j u'⟫_H`, so that `‖u‖_V² = ‖j u‖² + 𝔇(u, u)` holds by definition.
Mathlib convention: inner products are conjugate-linear in the first and linear in the second
argument, so the "unknown" sits in the second slot and the test vector `u'` in the first.

* `T = j ∘ j†` (Riesz: `⟪j† f, u'⟫_V = ⟪f, j u'⟫_H`); bounded, self-adjoint, `0 ≤ T ≤ 1`, injective.
* `Res lam = T * (1 - (lam + 1) T)⁻¹` for `lam ∈ ℂ ∖ [0, ∞)`; `ResV lam f ∈ V` is the unique weak
  solution of `𝔇(u', u) - lam ⟪j u', j u⟫ = ⟪j u', f⟫` and `j (ResV lam f) = Res lam f`.
* `lam ↦ Res lam` is analytic (operator norm) on `ℂ ∖ [0, ∞)`.
-/

namespace ArtinKP.CAbs

open Filter Topology ComplexConjugate
open scoped InnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

/-- The abstract energy space: `V` (playing `H¹`) mapped into `H` (playing `L²`) by a contraction
`j` that is injective with dense range. -/
structure EnergySpace (V : Type*) (H : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- the inclusion `H¹ → L²` -/
  j : V →L[ℂ] H
  /-- `‖u‖_{L²} ≤ ‖u‖_{H¹}` -/
  norm_le : ∀ u : V, ‖j u‖ ≤ ‖u‖
  /-- the inclusion is injective -/
  injective : Function.Injective j
  /-- `H¹` is dense in `L²` -/
  denseRange : DenseRange j

/-- `ℂ ∖ [0, ∞)`. -/
def resolventDomain : Set ℂ := {lam | lam.re < 0 ∨ lam.im ≠ 0}

namespace EnergySpace

variable {V : Type*} {H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : EnergySpace V H)

/-- The Dirichlet form `𝔇(u, u') = ⟪u, u'⟫_V - ⟪j u, j u'⟫_H` (conjugate-linear in `u`). -/
def form (u u' : V) : ℂ := ⟪u, u'⟫_ℂ - ⟪E.j u, E.j u'⟫_ℂ

/-- The Riesz map `L² → H¹`: `⟪riesz f, u'⟫_V = ⟪f, j u'⟫_H`. -/
def riesz : H →L[ℂ] V := ContinuousLinearMap.adjoint E.j

/-- The form operator `T : L² → L²`, `T f = j (riesz f)`. -/
def T : H →L[ℂ] H := E.j ∘L E.riesz

/-- `(1 - (lam + 1) T)⁻¹` (junk `0` when not invertible). -/
def G (lam : ℂ) : H →L[ℂ] H := Ring.inverse (1 - (lam + 1) • E.T : H →L[ℂ] H)

/-- The resolvent `Res lam = T (1 - (lam + 1) T)⁻¹ : L² → L²`. -/
def Res (lam : ℂ) : H →L[ℂ] H := E.T * E.G lam

/-- The resolvent with values in the energy space, `ResV lam = riesz ∘ (1 - (lam + 1) T)⁻¹`. -/
def ResV (lam : ℂ) : H →L[ℂ] V := E.riesz ∘L E.G lam

/-- `u` is a weak solution of `(Δ_form - lam) u = f`:
`𝔇(u', u) - lam ⟪j u', j u⟫ = ⟪j u', f⟫` for all test vectors `u'`. -/
def IsWeakSol (lam : ℂ) (f : H) (u : V) : Prop :=
  ∀ u' : V, E.form u' u - lam * ⟪E.j u', E.j u⟫_ℂ = ⟪E.j u', f⟫_ℂ

/-- `u` is a weak `lam`-eigenvector: `𝔇(u', u) = lam ⟪j u', j u⟫` for all `u'`. -/
def IsWeakEigen (lam : ℂ) (u : V) : Prop :=
  ∀ u' : V, E.form u' u = lam * ⟪E.j u', E.j u⟫_ℂ

end EnergySpace

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.X_Friedrichs
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-! # WP-X, file 11: closability — the Friedrichs energy space of a symmetric nonnegative operator

Abstract form of "the Dirichlet form is closable".  Let `A` be a symmetric nonnegative operator
defined on a dense subspace `D` of a Hilbert space `H` (`SymmOp H`; think `D` = smooth
`Γ`-invariant functions with compact support modulo `Γ`, `A = Δ`, symmetry and positivity = Green's
identity).  Complete `D` for the energy inner product `⟪u,w⟫₁ = ⟪u,w⟫ + ⟪u, A w⟫`; the inclusion
`D → H` extends to a contraction `j : V → H` which is **injective** (this is closability:
`⟪x, w⟫₁ = ⟪j x, w + A w⟫` for `w ∈ D`, and `D` is dense in `V`) with dense range.  The result is an
`EnergySpace V H` in the sense of `CAbs_Form`, with `form u w = ⟪u, A w⟫` on the core.
-/

open scoped InnerProductSpace ComplexConjugate
open UniformSpace

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-- A densely defined symmetric nonnegative operator on a Hilbert space. -/
structure SymmOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- the domain -/
  D : Submodule ℂ H
  /-- the operator -/
  A : D →ₗ[ℂ] H
  /-- the domain is dense -/
  dense : Dense (D : Set H)
  /-- symmetry -/
  symm : ∀ u w : D, ⟪(u : H), A w⟫_ℂ = ⟪A u, (w : H)⟫_ℂ
  /-- nonnegativity -/
  nonneg : ∀ u : D, 0 ≤ (⟪(u : H), A u⟫_ℂ).re

namespace SymmOp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : SymmOp H)

/-- The domain, as a type carrying the energy inner product. -/
def Core : Type _ := S.D

instance instAddCommGroupCore : AddCommGroup S.Core := inferInstanceAs (AddCommGroup S.D)
instance instModuleComplexCore : Module ℂ S.Core := inferInstanceAs (Module ℂ S.D)

/-- The inclusion of the core in `H`, as a linear map. -/
def incl : S.Core →ₗ[ℂ] H := S.D.subtype

/-- The operator on the core. -/
def op : S.Core →ₗ[ℂ] H := S.A

lemma symm' (u w : S.Core) : ⟪S.incl u, S.op w⟫_ℂ = ⟪S.op u, S.incl w⟫_ℂ := S.symm u w

lemma nonneg' (u : S.Core) : 0 ≤ (⟪S.incl u, S.op u⟫_ℂ).re := S.nonneg u

/-- The energy inner product `⟪u, w⟫ + ⟪u, A w⟫`. -/
@[instance_reducible]
def preCore : PreInnerProductSpace.Core ℂ S.Core where
  inner u w := ⟪S.incl u, S.incl w⟫_ℂ + ⟪S.incl u, S.op w⟫_ℂ
  conj_inner_symm u w := by
    change conj (⟪S.incl w, S.incl u⟫_ℂ + ⟪S.incl w, S.op u⟫_ℂ) =
      ⟪S.incl u, S.incl w⟫_ℂ + ⟪S.incl u, S.op w⟫_ℂ
    rw [map_add, inner_conj_symm, inner_conj_symm, S.symm' u w]
  re_inner_nonneg u := by
    change 0 ≤ (⟪S.incl u, S.incl u⟫_ℂ + ⟪S.incl u, S.op u⟫_ℂ).re
    rw [Complex.add_re]
    exact add_nonneg (inner_self_nonneg (𝕜 := ℂ) (x := S.incl u)) (S.nonneg' u)
  add_left u v w := by
    change ⟪S.incl (u + v), S.incl w⟫_ℂ + ⟪S.incl (u + v), S.op w⟫_ℂ = _ + _ + (_ + _)
    rw [map_add, inner_add_left, inner_add_left]; ring
  smul_left u w r := by
    change ⟪S.incl (r • u), S.incl w⟫_ℂ + ⟪S.incl (r • u), S.op w⟫_ℂ = conj r * (_ + _)
    rw [map_smul, inner_smul_left, inner_smul_left]; ring

instance instSeminormedAddCommGroupCore : SeminormedAddCommGroup S.Core :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ _ _ _ _ S.preCore

instance instInnerProductSpaceComplexCore : InnerProductSpace ℂ S.Core := InnerProductSpace.ofCore S.preCore

lemma inner_core (u w : S.Core) :
    ⟪u, w⟫_ℂ = ⟪S.incl u, S.incl w⟫_ℂ + ⟪S.incl u, S.op w⟫_ℂ := rfl

lemma norm_incl_le (u : S.Core) : ‖S.incl u‖ ≤ ‖u‖ := by
  have h1 : ‖u‖ ^ 2 = ‖S.incl u‖ ^ 2 + (⟪S.incl u, S.op u⟫_ℂ).re := by
    rw [@norm_sq_eq_re_inner ℂ, S.inner_core, @norm_sq_eq_re_inner ℂ H]
    simp
  have h2 := S.nonneg' u
  exact le_of_sq_le_sq (by linarith) (norm_nonneg _)

/-- The energy space `V`: the completion of the core for the energy norm. -/
abbrev V : Type _ := Completion S.Core

/-- The canonical map of the core into `V`. -/
def kappa : S.Core →ₗ[ℂ] S.V := (Completion.toComplL (𝕜 := ℂ) (E := S.Core)).toLinearMap

lemma kappa_apply (u : S.Core) : S.kappa u = (u : Completion S.Core) := rfl

lemma denseRange_kappa : DenseRange S.kappa := Completion.denseRange_coe

lemma norm_incl_le_kappa (u : S.Core) : ‖S.incl u‖ ≤ 1 * ‖S.kappa u‖ := by
  rw [one_mul, kappa_apply, Completion.norm_coe]
  exact S.norm_incl_le u

variable [CompleteSpace H]

/-- The extension `j : V → H` of the inclusion of the core. -/
def j : S.V →L[ℂ] H := S.incl.extendOfNorm S.kappa

lemma j_kappa (u : S.Core) : S.j (S.kappa u) = S.incl u :=
  LinearMap.extendOfNorm_eq S.denseRange_kappa ⟨1, S.norm_incl_le_kappa⟩ u

lemma norm_j_le (x : S.V) : ‖S.j x‖ ≤ ‖x‖ := by
  have := LinearMap.norm_extendOfNorm_apply_le S.denseRange_kappa 1 S.norm_incl_le_kappa x
  rwa [one_mul] at this

/-- The identity behind closability: `⟪x, w⟫_V = ⟪j x, w + A w⟫_H` for `w` in the core. -/
lemma inner_kappa_right (x : S.V) (w : S.Core) :
    ⟪x, S.kappa w⟫_ℂ = ⟪S.j x, S.incl w + S.op w⟫_ℂ := by
  refine Completion.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) fun u => ?_
  rw [kappa_apply, Completion.inner_coe, ← kappa_apply, j_kappa, inner_add_right, S.inner_core]

/-- **Closability**: `j` is injective. -/
theorem j_injective : Function.Injective S.j := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : ∀ w : S.Core, ⟪x, S.kappa w⟫_ℂ = 0 := fun w => by
    rw [S.inner_kappa_right, hx, inner_zero_left]
  have h2 : ∀ y : S.V, ⟪x, y⟫_ℂ = 0 := fun y =>
    Completion.induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) fun w => h1 w
  exact inner_self_eq_zero.mp (h2 x)

lemma denseRange_j : DenseRange S.j := by
  refine S.dense.mono ?_
  intro h hh
  exact ⟨S.kappa (⟨h, hh⟩ : S.D), S.j_kappa _⟩

/-- **The Friedrichs energy space** of a symmetric nonnegative operator. -/
def energySpace : ArtinKP.CAbs.EnergySpace S.V H where
  j := S.j
  norm_le := S.norm_j_le
  injective := S.j_injective
  denseRange := S.denseRange_j

@[simp] lemma energySpace_j : S.energySpace.j = S.j := rfl

end SymmOp

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
/-! # WP-X2, file 5: the geometric core and the energy space `H¹(Γ \ X)`

* `X.toL2 Γ f h : L²(Γ\X)` — the class of a measurable `Γ`-invariant function that is square
  integrable modulo `Γ` (`X.L2Rep Γ f`), with `X.inner_toL2`, `X.norm_sq_toL2`;
* `X.core Γ` — the functions `∑_{γ ∈ Γ} φ ∘ γ`, `φ ∈ C_c^∞(X)` (equivalently: smooth,
  `Γ`-invariant, support compact modulo `Γ`; see `X.mem_core_of_tsupport` in `X2_Weak`);
* `X.symmOp Γ : SymmOp (L²(Γ\X))` — the Laplacian on the core: dense domain, symmetric,
  nonnegative, with `⟪w, Δw⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w w|²` (`X.inner_coreL2_coreLap_self`);
* `X.H1 Γ`, `X.energy Γ : CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

/-! ### Classes of invariant functions -/

variable {Γ}

variable (Γ)

variable {Γ}

lemma X.L2Rep.sub {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) :
    X.L2Rep Γ fun P => f P - g P :=
  ⟨hf.meas.sub hg.meas, fun γ P => by rw [hf.inv γ P, hg.inv γ P], hf.memLp.sub hg.memLp⟩

variable (Γ)

variable {Γ}

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

lemma X.grad2_nonneg (u : X F → ℂ) (P : X F) : 0 ≤ X.grad2 u P :=
  Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (acoef_pos k _).le (sq_nonneg _)

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

variable (Γ)

/-- **The Laplacian on the geometric core as a symmetric nonnegative operator on `L²(Γ\X)`.** -/
def X.symmOp : SymmOp (X.L2 Γ) where
  D := LinearMap.range (X.coreL2 Γ)
  A := (X.coreL2 Γ ∘ₗ X.coreLap Γ) ∘ₗ
    (LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective).symm.toLinearMap
  dense := X.dense_range_coreL2
  symm := by
    intro u w
    obtain ⟨a, ha⟩ : ∃ a, LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective a = u :=
      ⟨_, LinearEquiv.apply_symm_apply _ u⟩
    obtain ⟨b, hb⟩ : ∃ b, LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective b = w :=
      ⟨_, LinearEquiv.apply_symm_apply _ w⟩
    subst ha hb
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.ofInjective_apply]
    rw [X.inner_coreL2_coreLap, X.inner_coreLap_coreL2]
  nonneg := by
    intro u
    obtain ⟨a, ha⟩ : ∃ a, LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective a = u :=
      ⟨_, LinearEquiv.apply_symm_apply _ u⟩
    subst ha
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.ofInjective_apply]
    rw [X.inner_coreL2_coreLap_self, Complex.ofReal_re]
    exact integral_nonneg fun P => mul_nonneg ENNReal.toReal_nonneg (X.grad2_nonneg _ P)

/-- The energy space `H¹(Γ\X)`: the completion of the core for `‖w‖² + ⟪w, Δw⟫`. -/
abbrev X.H1 : Type _ := (X.symmOp Γ).V

/-- `H¹(Γ\X) → L²(Γ\X)` as an abstract energy space. -/
def X.energy : ArtinKP.CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ) := (X.symmOp Γ).energySpace

/-- A core function as an element of the domain of `X.symmOp`. -/
def X.coreD (a : X.core Γ) : (X.symmOp Γ).Core :=
  LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective a

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RC_Cusp
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-RC, file 1: reduction at a general cusp (stub R1 of WP-B1)

For an arbitrary `τ ∈ SL₂(F)` the group `τ SL₂(𝓞_F) τ⁻¹` contains the translations by `m𝓞_F` and
the diagonal matrices of the units `≡ 1 mod m`, where `m ∈ 𝓞_F ∖ 0` clears the denominators of the
products `τ_ij τ_kl`.  Hence (Dirichlet's unit theorem applied to `v^{1/k}`, `k = |(𝓞/m)^×|`) every
point of `X` has a translate under an upper triangular element of `τ SL₂(𝓞_F) τ⁻¹` with bounded `x`
and balanced `v`.

* `conjSub τ`: the subgroup `{γ' ∈ SL₂(𝓞) : τ⁻¹ γ' τ ∈ SL₂(𝓞)}`.
* `exists_reduced_conj`: the reduction statement.
* `reduction_cusp` (= **R1**), `reduction_cusp_siegelSet` (the same without an upper bound for the
  height; `siegelSet` is the unbounded Siegel set).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The elements `γ'` of `SL₂(𝓞_F)` with `τ⁻¹ γ' τ ∈ SL₂(𝓞_F)`. -/
def conjSub (τ : SL(2, F)) : Subgroup (SL(2, 𝓞 F)) :=
  ((intSL F).range.comap (MulAut.conj τ⁻¹).toMonoidHom).comap (intSL F)

variable [IsTotallyComplex F]

/-- The unbounded Siegel set `{P : |x_w| ≤ B, m ≤ v_w ∀ w}`. -/
def siegelSet (F : Type*) [Field F] [NumberField F] (m B : ℝ) : Set (X F) :=
  {P | ∀ w, ‖P.x w‖ ≤ B ∧ m ≤ P.v w}

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.X2_Prod
/-! # WP-X2, file 9: product coordinates `(x, v)` on `X` (stub S3 of WP-X)

`X.measurePreserving_xv`: the map `P ↦ (P.x, P.v) : X F → (ι → ℂ) × (ι → ℝ)` carries `X.vol F`
to `volume.prod (X.nuV F)`, `X.nuV F = ∏_w dv_w / v_w³` on `(0,∞)^ι`.  Hence integrals over `X`
and over strips `{x ∈ D}` are iterated integrals (`X.lintegral_xv`, `X.setLIntegral_strip`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-- `dv / v³` on `(0, ∞)`. -/
def nu1 : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun v => ENNReal.ofReal ((v ^ 3)⁻¹)

instance instSigmaFiniteRealNu1 : SigmaFinite nu1 := by unfold nu1; infer_instance

variable (F : Type*) [Field F] [NumberField F]

/-- The measure `∏_w dv_w / v_w³` on `(0,∞)^ι`. -/
def X.nuV : Measure (InfinitePlace F → ℝ) := Measure.pi fun _ => nu1

instance instSigmaFiniteForallInfinitePlaceRealNuV : SigmaFinite (X.nuV F) := by unfold X.nuV; infer_instance

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RC_Compact
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-RC, file 2: compactness modulo `Γ` of bounded-height sets (MATH2 1.4(d)) and finite volume (V1)

* `spread Γ B = ⋃_{q ∈ SL₂(𝓞)/Γ} q.out⁻¹ • B`: passage from `SL₂(𝓞_F)` to a subgroup of finite index.
* `exists_compact_top_le`, `exists_compact_top_le_subgroup`: **MATH2 1.4(d)**,
  `{P : ht_p(P) ≤ T ∀ p} ⊆ Γ · K`, `K` compact.
* `exists_cover_finite_vol`: `X = SL₂(𝓞_F) · B` with `vol B < ∞` (finite union of translated Siegel sets).
* `lintegral_mul_pou_le_of_cover` (covering lemma), `quotVol_univ_le`.
* `quotVol_univ_lt_top`: **V1**, `μ(Γ\X) < ∞` for `Γ` of finite index.
* `lintegral_G_pow_lt_top`: `G ∈ L^k(Γ\X)` with no volume hypothesis.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Pointwise
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### Subgroups of finite index -/

/-- The union of the translates of `B` by inverse coset representatives of `SL₂(𝓞_F)/Γ`. -/
def spread (Γ : Subgroup (SL(2, 𝓞 F))) (B : Set (X F)) : Set (X F) :=
  ⋃ q : SL(2, 𝓞 F) ⧸ Γ, (fun P : X F => q.out⁻¹ • P) '' B

/-! ### MATH2 1.4(d) -/

/-! ### Finite volume -/

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.X2_Weak
/-! # WP-X2, file 6: cut-offs; classical solutions are weak solutions in `H¹`

* `X.isClosed_saturation`: `Γ · K` is closed for compact `K`;
* `X.mem_core_of_support`: a smooth `Γ`-invariant function whose support lies in `Γ · K`,
  `K` compact, belongs to the core (it is `∑_γ φ ∘ γ` with `φ = ψ w / ∑_γ ψ ∘ γ`);
* `X.integrable_pou_mul`: `η · h` is integrable for `h` continuous, invariant, supported in
  `Γ · K`;
* `X.exists_weakSol`: **the height cut-off lemma** (MATH2 §1.6).  A smooth `Γ`-invariant `u`
  with `u ∈ L²(Γ\X)` and `Δu = λu + f` pointwise, `f ∈ L²(Γ\X)`, lies in `H¹(Γ\X)` and satisfies
  the weak equation `𝔇(u', u) − λ⟪u', u⟫ = ⟪u', f⟫` against all `u' ∈ H¹`, provided there are
  cut-offs `χ_n` (smooth, invariant, `0 ≤ χ_n ≤ 1`, compact support modulo `Γ`, `χ_n → 1`
  pointwise, `∑_w v_w²|∇_w χ_n|² ≤ ε_n → 0`).  Finite energy of `u` is a conclusion, not a
  hypothesis (IMS localisation formula).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Saturations of compact sets -/

instance instContinuousConstSMulSubgroup (Γ : Subgroup (SL(2, 𝓞 F))) :
    ContinuousConstSMul Γ (X F) :=
  ⟨fun γ => continuous_const_smul (γ : SL(2, 𝓞 F))⟩

/-! ### A bump function positive on a compact set -/

/-! ### Invariant functions supported in `Γ · K` are averages -/

/-- The local representative `ψ h / ∑_γ ψ ∘ γ`. -/
def X.rep (Γ : Subgroup (SL(2, 𝓞 F))) (ψ h : X F → ℂ) (P : X F) : ℂ :=
  ψ P * h P / X.avg Γ ψ P

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RC_Cutoff
/-! # WP-RC, file 3: the height cut-offs `χ_n` of MATH2 §1.6

`chi S n P = 1 − ∑_{p ∈ PairClass S} ϑ(log ht_p(P) / (n+1))`, `ϑ = 0` on `(−∞,1]`, `ϑ = 1` on `[2,∞)`.
Near every point at most one fixed term is nonzero (`exists_single`: local finiteness from the
summable majorant, uniqueness from (H1)), so `χ_n` is smooth, `0 ≤ χ_n ≤ 1`, and
`∑_w v_w²|∇_w χ_n|² = r ϑ'(…)²/(n+1)² ≤ r C²/(n+1)²` by `X.grad2_comp_log_pairHt` ((H2) in exact form).
`χ_n` is `SL₂(𝓞_F)`-invariant, `χ_n → 1` pointwise (eventually `= 1`), and `χ_n ≠ 0` forces all
heights `≤ e^{2(n+1)}`, a set that is compact modulo `Γ` (MATH2 1.4(d)).

* `exists_cutoffs`: the sequence, in exactly the form of the hypotheses of `X.exists_weakSol`.
* `exists_weakSol`: `X.exists_weakSol` with the cut-off hypotheses discharged.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Module Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

/-! ### The profile `ϑ` -/

/-- A smooth step: `0` on `(−∞, 1]`, `1` on `[2, ∞)`. -/
def theta (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

/-- The one-variable function of `τ = log I_p`: `1 − ϑ((τ − ℓ)/(n+1))`. -/
def Gf (ℓ : ℝ) (n : ℕ) (τ : ℝ) : ℂ := ((1 - theta ((τ - ℓ) / ((n : ℝ) + 1)) : ℝ) : ℂ)

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Local finiteness -/

/-! ### The cut-offs -/

/-- `χ_n = 1 − ∑_p ϑ(log ht_p / (n+1))`. -/
def chi (S : Finset (FinitePlace F)) (n : ℕ) (P : X F) : ℝ :=
  1 - ∑' p : PairClass S, theta (Real.log (p.ht P) / ((n : ℝ) + 1))

/-! ### Smoothness and the gradient bound -/

/-! ### The cut-off sequence for `X.exists_weakSol` -/

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.C5_PE
/-! # WP-C5, file 1: pseudo-Eisenstein series with a profile vanishing below height 2

For weights `a : PairClass S → ℂ` and a profile `g : ℝ → ℂ` (a function of `τ = log ht`),
`pe S a g P = ∑_p a(p) · g(log ht_p(P))`.  If `g` vanishes for `τ < log 2` (`VanishLow g`) the sum
is **locally a single term**, uniformly in `a` and `g` (`pe_eventually`; (H1) of MATH2 §0.1):
no convergence question arises.  Hence, for smooth `g`:

* `smooth_pe`, `lap_pe : Δ (pe a g) = pe a (Lg g)`, `Lg g = r(−g'' + 2g')`;
* `pe_smul`: invariance under `γ` when `a(pγ) = a(p)`;
* `norm_pe_le`, linearity in `a` and in `g`;
* if moreover `g` vanishes for `τ > log 3` (`VanishHigh g`), the support of `pe a g` lies in
  `Γ · K`, `K` compact (`exists_compact_pe`), so `pe a g ∈ X.core Γ` (`pe_mem_core`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.C5

open ArtinKP.X ArtinKP.B1

noncomputable section

/-! ### Profiles -/

/-- The profile vanishes below height `2` (`τ = log h < log 2`). -/
def VanishLow (g : ℝ → ℂ) : Prop := ∀ τ : ℝ, τ < Real.log 2 → g τ = 0

/-- The profile vanishes above height `3`. -/
def VanishHigh (g : ℝ → ℂ) : Prop := ∀ τ : ℝ, Real.log 3 < τ → g τ = 0

/-- Translation of a profile: `shift g ℓ τ = g (τ − ℓ)` (passage from `log I_p` to `log ht_p`). -/
def shift (g : ℝ → ℂ) (ℓ : ℝ) (τ : ℝ) : ℂ := g (τ - ℓ)

variable {F : Type*} [Field F] [NumberField F]

/-- The radial part of the Laplacian in the variable `τ = log h`: `r(−g'' + 2g')`,
`r` the number of infinite places. -/
def Lg (F : Type*) [Field F] [NumberField F] (g : ℝ → ℂ) (τ : ℝ) : ℂ :=
  (Fintype.card (InfinitePlace F) : ℂ) * (-deriv (deriv g) τ + 2 * deriv g τ)

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Locally a single term -/

/-- The pseudo-Eisenstein series with weights `a` and profile `g` (in `τ = log ht`). -/
def pe (S : Finset (FinitePlace F)) (a : PairClass S → ℂ) (g : ℝ → ℂ) (P : X F) : ℂ :=
  ∑' p : PairClass S, a p * g (Real.log (p.ht P))

/-! ### Algebra -/

/-! ### Smoothness and the Laplacian -/

/-! ### Support -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Profile
/-! # WP-C5, file 3: the profiles of MATH2 §1

* `rho`: smooth, `0` on `(−∞, 2]`, `1` on `[3, ∞)`; `rt τ = ρ(e^τ)` and its derivatives `rt1`, `rt2`.
* `gS s τ = ρ(e^τ) e^{sτ}`: the profile of the cut-off part `h_s` (`gS_log : gS s (log h) = ρ(h) h^s`).
* `lam F s = r · s(2 − s)`.
* `phiS F s τ = r e^{sτ} (−ρ̃''(τ) + (2 − 2s) ρ̃'(τ))`: the profile of the source `F_s`
  (`Lg_gS : (L − λ(s)) gS s = phiS F s`); smooth, supported in `[log 2, log 3]`, entire in `s`,
  bounded on `{‖s‖ ≤ M} × ℝ` (`exists_norm_phiS_le`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

noncomputable section

/-! ### The cut-off `ρ` -/

/-- A smooth step: `0` on `(−∞, 2]`, `1` on `[3, ∞)`. -/
def rho (h : ℝ) : ℝ := Real.smoothTransition (h - 2)

/-- `ρ` in the variable `τ = log h`, complex valued. -/
def rt (τ : ℝ) : ℂ := ((rho (Real.exp τ) : ℝ) : ℂ)

/-- `ρ̃'`. -/
def rt1 : ℝ → ℂ := deriv rt

/-- `ρ̃''`. -/
def rt2 : ℝ → ℂ := deriv rt1

/-! ### The profile of `h_s` -/

/-- `gS s τ = ρ(e^τ) e^{sτ}`. -/
def gS (s : ℂ) (τ : ℝ) : ℂ := rt τ * Complex.exp (s * (τ : ℂ))

variable {F : Type*} [Field F] [NumberField F]

/-! ### The eigenvalue and the profile of the source -/

/-- `λ(s) = r · s(2 − s)`, `r` the number of infinite places. -/
def lam (F : Type*) [Field F] [NumberField F] (s : ℂ) : ℂ :=
  (Fintype.card (InfinitePlace F) : ℂ) * (s * (2 - s))

/-- `φ_s = (L − λ(s))(ρ̃ e^{sτ}) = r e^{sτ}(−ρ̃'' + (2 − 2s)ρ̃')`. -/
def phiS (F : Type*) [Field F] [NumberField F] (s : ℂ) (τ : ℝ) : ℂ :=
  (Fintype.card (InfinitePlace F) : ℂ) *
    (Complex.exp (s * (τ : ℂ)) * (-rt2 τ + (2 - 2 * s) * rt1 τ))

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.RO_Orbits
/-! # WP-RO, file 4: finitely many `Γ`-orbits of pair classes (stub S-2 of WP-S)

* `finite_orbits_of_finiteIndex`: for a subgroup `Γ ≤ SL₂(𝓞)` of finite index, `𝒫/Γ` is finite
  (`𝒫 = B1.PairClass S`, any `S`).
* `princCong 𝔫`, the principal congruence subgroup of `SL₂(𝓞)`; it has finite index for `𝔫 ≠ ⊥`
  (`princCong_finiteIndex`), and `Gamma 𝔪 𝔫 = (princCong 𝔫).map (intMat 𝔪)` (`Gamma_eq_map`).
* `finite_orbits_row`: the same on `S.Row 𝔪` modulo `U_S`; **`finite_orbits`**: the statement of
  `S_Stubs.finite_orbits`, proved.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1 ArtinKP.X ArtinKP.S

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The principal congruence subgroup of level `𝔫` of `SL₂(𝓞_F)`. -/
def princCong (𝔫 : Ideal (𝓞 F)) : Subgroup (SL(2, 𝓞 F)) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk 𝔫)).ker

theorem princCong_finiteIndex {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) : (princCong 𝔫).FiniteIndex := by
  have := Ideal.finiteQuotientOfFreeOfNeBot 𝔫 h𝔫
  have : Finite (SL(2, 𝓞 F ⧸ 𝔫)) := inferInstance
  exact Subgroup.finiteIndex_ker _

theorem intMat_mem_Gamma {𝔫 : Ideal (𝓞 F)} {γ : SL(2, 𝓞 F)} (h : γ ∈ princCong 𝔫) :
    intMat 𝔪 γ ∈ Gamma 𝔪 𝔫 := Subgroup.mem_map_of_mem _ h

/-! ### WP-B1's conditional statements, unconditionally for a good modulus -/

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.C5_Series
/-! # WP-C5, file 4: the cut-off part `h_s`, the source `F_s` and `u_s = E_Ψ − h_s`

For a twisted section `Ψ : TSection ι 𝔪` (weights `B.tildeC Ψ s` on `B.RowClass 𝔪`):

* `hpart Ψ s Q = ∑_q Ψ̃_s(q) ρ(ht_q(Q)) ht_q(Q)^s`, `src Ψ s Q = ∑_q Ψ̃_s(q) φ_s(log ht_q(Q))`,
  `upart Ψ s = eis Ψ s − hpart Ψ s`.  All three are defined without hypotheses; `hpart` and `src`
  are locally single terms for every `s ∈ ℂ` (`hpart_eq_pe`, `src_eq_pe`: they are WP-C5's `pe`
  with the weights `wt h𝔪 Ψ s` on `B1.PairClass (SOf 𝔪)`).
* `Inv Γ Ψ`: `Ψ` is fixed by (the image in `SL₂(R)` of) `Γ ≤ SL₂(𝓞_F)`.
* `norm_upart_le`: `|u_s| ≤ B · G` (WP-B1's `G`), `Re s > 2`; `l2Rep_upart`.
* `lap_hpart : Δ h_s = λ(s) h_s + F_s`; with the named hypothesis `EisEigen Ψ s` (WP-RF, D1:
  `E_Ψ(·, s)` is smooth and `Δ E = λ(s) E`): `lap_upart : Δ u_s = λ(s) u_s + (−F_s)`.
* `src`: smooth, invariant, in the core (`src_mem_core`), bounded (`exists_norm_src_le`), entire in
  `s` pointwise (`differentiable_src`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Definitions (no hypotheses) -/

/-- The cut-off part `h_s = ∑_q Ψ̃_s(q) ρ(ht_q) ht_q^s` (profile `gS s` in `τ = log ht_q`). -/
def hpart (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) : ℂ :=
  ∑' q : B.RowClass 𝔪, tildeC Ψ s q * gS s (Real.log (q.ht Q))

/-- The source `F_s = ∑_q Ψ̃_s(q) φ_s(log ht_q)`, `φ_s = (L − λ(s))(ρ h^s)`. -/
def src (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) : ℂ :=
  ∑' q : B.RowClass 𝔪, tildeC Ψ s q * phiS F s (Real.log (q.ht Q))

/-- `u_s = E_Ψ(·, s) − h_s`. -/
def upart (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) : ℂ := eis Ψ s Q - hpart Ψ s Q

/-- `Ψ` is invariant under `Γ ≤ SL₂(𝓞_F)`. -/
def Inv (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) : Prop :=
  ∀ γ ∈ Γ, RO.intMat 𝔪 γ ∈ Ψ.stab

/-- **Named hypothesis (WP-RF, stub D1 of WP-B1)**: the Eisenstein series is smooth in `Q` and
is an eigenfunction, `Δ E_Ψ(·, s) = r s(2 − s) E_Ψ(·, s)` (termwise differentiation). -/
def EisEigen (Ψ : TSection ι 𝔪) (s : ℂ) : Prop :=
  X.Smooth (fun Q : X F => eis Ψ s Q) ∧
    ∀ Q : X F, X.lap (fun Q : X F => eis Ψ s Q) Q = lam F s * eis Ψ s Q

/-- The weights on WP-B1's pair classes. -/
def wt (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (p : PairClass (RO.SOf 𝔪)) : ℂ :=
  tildeC Ψ s ((RO.rowClassEquiv h𝔪).symm p)

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

/-! ### The source -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Level
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
/-! # WP-C5, file 7: every twisted section is invariant under a subgroup of finite index

`exists_finiteIndex_inv`: for `Ψ : TSection ι 𝔪` there is `Γ ≤ SL₂(𝓞_F)` of finite index with
`Inv Γ Ψ` (the kernel of the Kubota character `κ` on a deep principal congruence subgroup inside
the level of `Ψ`).  So the hypotheses `[Γ.FiniteIndex]`, `Inv Γ Ψ` of WP-C5 can always be met.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-- **Existence of the invariance group.** -/
theorem exists_finiteIndex_inv (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (Ψ : TSection ι 𝔪) :
    ∃ Γ : Subgroup (SL(2, 𝓞 F)), Γ.FiniteIndex ∧ Inv Γ Ψ := by
  obtain ⟨𝔫₀, h𝔫₀, hstab⟩ := Ψ.exists_level_le_stab
  obtain ⟨N, hN1, hN⟩ := Pk.exists_isDeepLevel hG.ne_bot
  set 𝔫 : Ideal (𝓞 F) := 𝔫₀ * 𝔪 ^ N with h𝔫def
  have h𝔫 : 𝔫 ≠ ⊥ := by
    rw [h𝔫def, ← Ideal.zero_eq_bot]
    have h1 : 𝔫₀ ≠ 0 := by rwa [Ideal.zero_eq_bot]
    have h2 : 𝔪 ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hG.ne_bot
    exact mul_ne_zero h1 (pow_ne_zero N h2)
  have hle0 : 𝔫 ≤ 𝔫₀ := Ideal.mul_le_left (I := 𝔫₀) (J := 𝔪 ^ N)
  have hleN : 𝔫 ≤ 𝔪 ^ N := Ideal.mul_le_right (I := 𝔫₀) (J := 𝔪 ^ N)
  have hfin : (RO.princCong 𝔫).FiniteIndex := RO.princCong_finiteIndex h𝔫
  let j : RO.princCong 𝔫 →* Gamma 𝔪 𝔫 :=
    MonoidHom.codRestrict ((RO.intMat 𝔪).comp (RO.princCong 𝔫).subtype) (Gamma 𝔪 𝔫)
      (fun γ => RO.intMat_mem_Gamma γ.2)
  let χ : RO.princCong 𝔫 →* ℂˣ := ((kappaHom ι Pk hG hz6 hN1 hN hleN).comp j).toHomUnits
  have hχ : ∀ γ : RO.princCong 𝔫, ((χ γ : ℂˣ) : ℂ) = kappa ι 𝔪 (RO.intMat 𝔪 γ) := fun γ => rfl
  have hrange : (χ.range : Set ℂˣ) ⊆ (rootsOfUnity 3 ℂ : Set ℂˣ) := by
    rintro x ⟨γ, rfl⟩
    change χ γ ∈ rootsOfUnity 3 ℂ
    rw [mem_rootsOfUnity]
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hχ]
    exact kappa_pow_three ι Pk hG hz6 _
  have hf3 : (rootsOfUnity 3 ℂ : Set ℂˣ).Finite := by
    have : Finite (rootsOfUnity 3 ℂ) := inferInstance
    exact Set.toFinite _
  have hfr : Finite χ.range := hf3.subset hrange
  have hker : χ.ker.FiniteIndex := Subgroup.finiteIndex_ker χ
  refine ⟨χ.ker.map (RO.princCong 𝔫).subtype, ⟨?_⟩, ?_⟩
  · rw [Subgroup.index_map_subtype]
    exact mul_ne_zero hker.index_ne_zero hfin.index_ne_zero
  · rintro γ ⟨k, hk, rfl⟩
    have h1 : kappa ι 𝔪 (RO.intMat 𝔪 k) = 1 := by
      rw [← hχ, MonoidHom.mem_ker.mp hk]
      rfl
    exact hstab _ (Gamma_mono hle0 (RO.intMat_mem_Gamma k.2)) h1

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.CAbs_Limit
/-!
# WP-C-abs, parts 3 and 4: the soft resolvent limit and its consequences

With `E : EnergySpace V H`, `Res lam = T (1 - (lam + 1) T)⁻¹` and `proj lam₀` the orthogonal
projection of `H` onto the weak `lam₀`-eigenspace (`= ker (T - (lam₀ + 1)⁻¹)`):

* `(lam - lam₀) • Res lam f → - proj lam₀ f` as `lam → lam₀` (real, `≠ -1`) inside a cone
  `‖lam - lam₀‖ ≤ C |Im lam|`;
* for `lamf` differentiable at `s₀` with `lamf s₀ = lam₀`, `lamf' s₀ ≠ 0`:
  `(s - s₀) • Res (lamf s) f_s → c₀ • proj lam₀ f`, with **`c₀ = - 1 / lamf' s₀`**;
* along a ray `s₀ + t d`, `t ↓ 0`, the cone condition is automatic as soon as
  `Im (lamf' s₀ * d) ≠ 0`;
* consequences: the limit is a weak eigenvector in `V`, the norm formula, functionals.
-/

namespace ArtinKP.CAbs

open Filter Topology ComplexConjugate
open scoped InnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace EnergySpace

variable {V : Type*} {H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : EnergySpace V H)

/-- The orthogonal projection of `H` onto the weak `lam`-eigenspace
`{j u | 𝔇(·, u) = lam ⟪j ·, j u⟫}` `= ker (T - (lam + 1)⁻¹)`. -/
def proj (lam : ℂ) : H →L[ℂ] H := eigenProj E.T (lam + 1)⁻¹

/-! ### Consequences (MATH (C6)–(C8)) -/

end EnergySpace

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.E_Model
/-! # E_Model: the intended residue functional satisfies the interface `ResFun`

`HasResOn Ω s₀ γ f r`: there is a function `Fc`, analytic on `Ω`, equal to `f` on `Re s > 2`, with
`(γ t − s₀) · Fc (γ t) → r` as `t ↓ 0`.  If `Ω` is preconnected and contains `Re s > 2`, and the path
`γ` tends to `s₀` inside `Ω`, this is a `ResFun s₀` (`ResFun.ofContinuation`): congruence is
trivial, additivity and multiplication by entire functions are limit laws, uniqueness is the
identity theorem.

`resFunSlit`: the concrete instance of MATH §3.3 — `Ω = {Re s > 1} ∖ (1, 2]`, `s₀ = 4/3`, the ray
`s₀ + t(1 + i)` (the ray of direction `e^{iπ/4}`).
-/

open Filter Topology

namespace ArtinKP.E

/-- "`f` (given on `Re s > 2`) continues analytically to `Ω` and `(s − s₀)·f(s) → r` along `γ`". -/
def HasResOn (Ω : Set ℂ) (s₀ : ℂ) (γ : ℝ → ℂ) (f : ℂ → ℂ) (r : ℂ) : Prop :=
  ∃ Fc : ℂ → ℂ, AnalyticOnNhd ℂ Fc Ω ∧ (∀ s : ℂ, 2 < s.re → Fc s = f s) ∧
    Tendsto (fun t : ℝ => (γ t - s₀) * Fc (γ t)) (𝓝[>] 0) (𝓝 r)

/-- The slit half-plane `{Re s > 1} ∖ (1, 2]` of MATH §3.3 (C5). -/
def slit : Set ℂ := {s : ℂ | 1 < s.re ∧ (s.im = 0 → 2 < s.re)}

lemma starConvex_slit : StarConvex ℝ (3 : ℂ) slit := by
  intro z hz a b ha hb hab
  have hre : (a • (3 : ℂ) + b • z).re = a * 3 + b * z.re := by simp
  have him : (a • (3 : ℂ) + b • z).im = b * z.im := by simp
  refine ⟨?_, fun h0 => ?_⟩
  · rw [hre]
    have : b * 1 ≤ b * z.re := mul_le_mul_of_nonneg_left hz.1.le hb
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      linarith [hz.1]
    · linarith
  · rw [hre]
    rw [him] at h0
    rcases mul_eq_zero.1 h0 with hb0 | hz0
    · have : a = 1 := by linarith
      rw [hb0, this]; norm_num
    · have h2 := hz.2 hz0
      have : b * 2 ≤ b * z.re := mul_le_mul_of_nonneg_left h2.le hb
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · have hb1 : b = 1 := by linarith
        rw [← ha0, hb1]
        linarith
      · linarith

lemma isPreconnected_slit : IsPreconnected slit :=
  (starConvex_slit.isPathConnected
    (show (1 : ℝ) < (3 : ℂ).re ∧ ((3 : ℂ).im = 0 → (2 : ℝ) < (3 : ℂ).re) from
      ⟨by norm_num, fun _ => by norm_num⟩)).isConnected.isPreconnected

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.C5_Main
/-! # WP-C5, file 5: (C5), the continuation and the limit (C7)

`Γ ≤ SL₂(𝓞_F)` of finite index, `Ψ` a twisted section with `Inv Γ Ψ`, `hG : Good 𝔪`.

* `srcL2 Γ Ψ s = [F_s]`, `uL2 Γ Ψ s = [u_s]` in `X.L2 Γ` (total functions: `0` when the
  representative is not square integrable); `differentiable_srcL2`: `s ↦ [F_s]` is **entire**.
* `Omega = {s | λ(s) ∉ [0, ∞)} = {Re s ≠ 1} ∖ [0, 2]` (`lam_mem_resolventDomain_iff`),
  `slit_subset_Omega`.
* `resPart Γ Ψ s = −Res(λ(s)) [F_s]`; **(C5)** `uL2_eq_resPart : [u_s] = −Res(λ(s))[F_s]` for
  `Re s > 2` (given D1 = `EisEigen Ψ s`); `differentiableOn_resPart`: holomorphic on `Omega`.
* `Eext Γ Ψ s = h_s + lift (resPart Γ Ψ s)`: the continued series; `Eext_ae_eq`.
* **(C7)** `theta Γ Ψ = −c₀ • P_{λ₀}[F_{4/3}]`, `c₀ = 3/(2r)`, `λ₀ = 8r/9`;
  `tendsto_ray_resPart`: `(s_t − s₀) • resPart(s_t) → θ` along `s_t = 4/3 + t(1 + i)`;
  `exists_isWeakEigen_theta`, `inner_coreLap_theta`, `proj_theta`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### The eigenvalue function -/

/-- The region where `λ(s) = r s(2 − s) ∉ [0, ∞)`: off the line `Re s = 1` and off `[0, 2]`. -/
def Omega : Set ℂ := {s : ℂ | s.re ≠ 1 ∧ (s.im = 0 → s.re < 0 ∨ 2 < s.re)}

/-- `c₀ = 3/(2r)`. -/
def c0 (F : Type*) [Field F] [NumberField F] : ℂ := 3 / (2 * (Fintype.card (InfinitePlace F) : ℂ))

/-- `λ₀ = λ(4/3) = 8r/9`. -/
def lam0 (F : Type*) [Field F] [NumberField F] : ℝ := 8 * (Fintype.card (InfinitePlace F) : ℝ) / 9

/-! ### The classes in `L²(Γ\X)` -/

open Classical in
/-- `[F_s] ∈ L²(Γ\X)`. -/
def srcL2 (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (s : ℂ) : X.L2 Γ :=
  if h : X.L2Rep Γ (src Ψ s) then X.toL2 Γ (src Ψ s) h else 0

open Classical in
/-- `[u_s] ∈ L²(Γ\X)` (meaningful for `Re s > 2`). -/
def uL2 (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (s : ℂ) : X.L2 Γ :=
  if h : X.L2Rep Γ (upart Ψ s) then X.toL2 Γ (upart Ψ s) h else 0

/-- The `L²` part of the continued Eisenstein series: `−Res(λ(s)) [F_s]`. -/
def resPart (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (s : ℂ) : X.L2 Γ :=
  -(X.energy Γ).Res (lam F s) (srcL2 Γ Ψ s)

/-- **`θ_Ψ = −c₀ P_{λ₀} [F_{s₀}]`**, `s₀ = 4/3`. -/
def theta (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) : X.L2 Γ :=
  -(c0 F • (X.energy Γ).proj ((lam0 F : ℝ) : ℂ) (srcL2 Γ Ψ (4 / 3)))

/-! ### (C5) -/

/-! ### Continuation -/

/-! ### The limit (C7) -/

/-! ### `θ` is a weak eigenfunction -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.N_Orbit
/-! # WP-N, file 1: the `x`-integral of the tail of `E_Ψ` over a cell of the translations of `Γ`

For `Γ ≤ SL₂(𝓞_F)` fixing the twisted section `Ψ`, `Λ_Γ = {β : n(β) ∈ Γ}` (`lamN Γ`, embedded in
`ℂ^r` as `latN Γ`) and `D` a fundamental domain of `latN Γ`:

* `tail Ψ s Q = E_Ψ(Q, s) − Ψ_s(0,1)·ht(Q)^s` (no hypotheses in the definition);
* `exists_integral_tail`: for `Re s > 2` there is a constant `C` with
  `∫_D tail Ψ s (x, v) dx = C · ∏_w v_w^{2−s}` for **all** `v`
  (the classes `≠ ∞` are unfolded along the free action of `Λ_Γ`, `orbN`; each full-space integral
  is a Jacquet integral at frequency `0`, WP-B's `integral_hKer` and WP-K's `jacquet_zero`);
* `integrableOn_tail`: the tail is integrable over `D`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### The translation lattice of `Γ` -/

/-- `Λ_Γ = {β ∈ 𝓞_F : n(β) ∈ Γ}`. -/
def lamN (Γ : Subgroup (SL(2, 𝓞 F))) : AddSubgroup (𝓞 F) where
  carrier := {β | nInt β ∈ Γ}
  zero_mem' := by
    rw [mem_ofPred_eq, nInt_zero]
    exact Γ.one_mem
  add_mem' := fun {a b} ha hb => by
    rw [mem_ofPred_eq, nInt_add]
    exact Γ.mul_mem ha hb
  neg_mem' := fun {a} ha => by
    have h : nInt (-a) = (nInt a)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← nInt_add, neg_add_cancel, nInt_zero]
    rw [mem_ofPred_eq, h]
    exact Γ.inv_mem ha

/-- `𝓞_F → ℂ^r`. -/
def embO : 𝓞 F →+ (InfinitePlace F → ℂ) :=
  (emb (F := F)).comp (algebraMap (𝓞 F) F).toAddMonoidHom

lemma embO_apply (β : 𝓞 F) : embO β = emb (β : F) := rfl

lemma embO_injective : Function.Injective (embO : 𝓞 F → InfinitePlace F → ℂ) := by
  intro a b h
  have h1 : emb ((a : F) - (b : F)) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact h
  have h2 := emb_eq_zero h1
  exact RingOfIntegers.coe_injective (sub_eq_zero.mp h2)

/-- The translation lattice of `Γ` in `ℂ^r`. -/
def latN (Γ : Subgroup (SL(2, 𝓞 F))) : AddSubgroup (InfinitePlace F → ℂ) := (lamN Γ).map embO

/-! ### Orbits of `Λ_Γ` on the classes `≠ ∞` -/

/-! ### The terms as shifted kernels -/

/-! ### The tail -/

/-! ### Finiteness of the unfolded `L¹` norm -/

/-! ### The integral over a cell -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.RC_CuspVol
/-! # WP-RC, file 5: the cusp volume (MATH2 §0.1, "cusp coordinates"; stub S3 of WP-X in final form)

For `Γ` of finite index in `SL₂(𝓞_F)` and `Γ_∞ = GammaInf Γ`:

`exists_cuspVol`: there is `V ∈ (0, ∞)` such that for every partition of unity `η` of `Γ_∞` and
every measurable `g ≥ 0`
`∫_{Γ_∞\X} g(ht) dμ = ∫ g(ht P) η(P) dμ(P) = V · ∫_0^∞ g(h) h⁻³ dh`.

Proof without fundamental domains.  The scalings `T_a : (x, v) ↦ (x, e^a v)` commute with every
upper triangular element of `SL₂(𝓞_F)`, so `η ∘ T_a` is again a partition of unity of `Γ_∞`; the
integral of the invariant function `g(ht)` does not depend on the partition of unity, and
`T_a` is a translation in the logarithmic chart.  Hence the image of `η μ` under `log ht` is
`e^{-2s}` times a translation-invariant measure, and `lintegral_average` identifies it.
`V < ∞` by the covering lemma and reduction theory in `Γ_∞`; `V > 0` since `∫ η dμ > 0`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### Powers in a subgroup of finite index -/

lemma pow_factorial_index_mem (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (a : SL(2, 𝓞 F)) :
    a ^ (Γ.index).factorial ∈ Γ := by
  obtain ⟨n, hn0, hn, hmem⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Γ)) a
  obtain ⟨d, hd⟩ := Nat.dvd_factorial hn0 hn
  rw [hd, pow_mul]
  exact Γ.pow_mem hmem d

lemma nInt_pow (β : 𝓞 F) (n : ℕ) : nInt β ^ n = nInt ((n : 𝓞 F) * β) := by
  induction n with
  | zero => simp [nInt_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← nInt_add]
    congr 1
    push_cast
    ring

/-! ### The logarithmic chart and the scalings of `v` -/

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-!
# WP-RF, part 3: Fourier uniqueness on a strip of `X` (core of stub S1 (b))

Product coordinates `P ↦ (x, v) : X F → XV F = (ι → ℂ) × (ι → ℝ)` carry `X.vol` to Lebesgue
measure with density `dens v = ∏_w v_w⁻³` on `v > 0` (`map_xv`).  For a basis `bV` of `ι → ℂ`
(the lattice basis of the translations) and `n : ℕ`, the box
`{x ∈ cell bV} × [1/(n+1), n+1]^ι` lies in the cell of the basis `bE bV n = bV ⊕ (n+2)·e_w` of
`XV F`, whose characters are `chi bV m x · phiK n k v`.  Hence (`RF_Torus.ae_eq_zero_of_coeff`):

`measure_ne_zero_null`: a function on `X`, square integrable on that box, all of whose
coefficients against `chi bV m (x) · phiK n k (v)` over the box vanish, is `0` a.e. on the box.
No Fubini and no slicing: the `v`-directions are treated as further circle directions.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The space of product coordinates `(x, v)`. -/
abbrev XV (F : Type*) [Field F] [NumberField F] : Type _ :=
  (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ)

/-! ### The density of `X.vol` in product coordinates -/

variable (F) in
/-- `(0, ∞)^ι`. -/
def posSet : Set (InfinitePlace F → ℝ) := Set.univ.pi fun _ => Ioi (0 : ℝ)

/-- The density `∏_w v_w⁻³` on `(0,∞)^ι`, zero elsewhere. -/
def dens (v : InfinitePlace F → ℝ) : ℝ≥0∞ :=
  (posSet F).indicator (fun v => ∏ w, ENNReal.ofReal ((v w ^ 3)⁻¹)) v

/-- Product coordinates. -/
def toXV (P : X F) : XV F := (P.x, P.v)

/-- The inverse of `toXV` on `v > 0`. -/
def ofXV (p : XV F) : X F := chart F fun w => (p.1 w, Real.log (p.2 w))

/-! ### Boxes in `v` -/

variable (F) in
/-- `[1/(n+1), n+1]^ι`. -/
def vBox (n : ℕ) : Set (InfinitePlace F → ℝ) :=
  {v | ∀ w, 1 / ((n : ℝ) + 1) ≤ v w ∧ v w ≤ (n : ℝ) + 1}

/-! ### The basis of `XV F` adapted to a box -/

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.X_Cusp
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-X, file 12: the translation subgroup of the cusp and unfolding to a strip

`GammaN Γ ≤ Γ` is the group of translations `[[1, β], [0, 1]]` in `Γ`; it acts on `X` by
`x ↦ x + β` (through the embeddings) and fixes `v`.  If `D ⊂ ℂ^r` is a strict fundamental set for
the translation lattice, `P ↦ 1_D(x(P))` is a partition of unity for `GammaN Γ`, and the
unfolding theorem reads
`∫_{Γ\X} (Σ_{γ ∈ N\Γ} f(γP)) u(P) = ∫_{x ∈ D} f u dμ` (`X.lintegral_unfold_N`).
Fourier analysis along `x` (frequencies in the dual lattice) takes place on the strip `{x ∈ D}`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The translations in `Γ`: matrices `[[1, β], [0, 1]]`. -/
def GammaN (Γ : Subgroup (SL(2, 𝓞 F))) : Subgroup Γ where
  carrier := {γ | (γ : SL(2, 𝓞 F)) 1 0 = 0 ∧ (γ : SL(2, 𝓞 F)) 0 0 = 1}
  one_mem' := by simp
  mul_mem' := by
    rintro γ γ' ⟨h1, h2⟩ ⟨h1', h2'⟩
    simp only [mem_setOf_eq] at h1 h2 h1' h2' ⊢
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two, h1, h1', h2, h2']
    simp
  inv_mem' := by
    rintro γ ⟨h1, h2⟩
    simp only [mem_setOf_eq] at h1 h2 ⊢
    have hdet := (γ : SL(2, 𝓞 F)).det_coe
    rw [Matrix.det_fin_two, h1, h2, mul_zero, sub_zero, one_mul] at hdet
    rw [Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [h1, hdet]

/-- The translation vector `β ∈ ℂ^r` of an element of `GammaN Γ`. -/
def GammaN.shift {Γ : Subgroup (SL(2, 𝓞 F))} (γ : GammaN Γ) (w : InfinitePlace F) : ℂ :=
  w.embedding (((γ : Γ) : SL(2, 𝓞 F)) 0 1 : 𝓞 F)

lemma X.measurable_x : Measurable (X.x : X F → InfinitePlace F → ℂ) :=
  measurable_pi_iff.mpr fun w => (X.continuous_x w).measurable

lemma X.measurable_v : Measurable (X.v : X F → InfinitePlace F → ℝ) :=
  measurable_pi_iff.mpr fun w => (X.continuous_v w).measurable

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Lattice
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice
/-! # WP-X2, file 10: the translation lattice (stub S2 of WP-X)

For `F` totally complex and `Γ ≤ SL(2,𝓞_F)` containing the translations `n(β)`, `β ∈ 𝔫`, for a
nonzero ideal `𝔫`, the shifts of `GammaN Γ` form a lattice in `ℂ^r` and there is a bounded
measurable strict fundamental set (`exists_fundamental_translations`): the hypothesis `hfund` of
`isPOU_strip` and `X.lintegral_unfold_N`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal nonZeroDivisors
open MeasureTheory Set NumberField NumberField.InfinitePlace

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

lemma GammaN.coe_one_one (γ : GammaN Γ) : ((γ : Γ) : SL(2, 𝓞 F)) 1 1 = 1 := by
  have hdet := ((γ : Γ) : SL(2, 𝓞 F)).det_coe
  rw [Matrix.det_fin_two, γ.2.1, γ.2.2, mul_zero, sub_zero, one_mul] at hdet
  exact hdet

lemma GammaN.mul_zero_one (γ γ' : GammaN Γ) :
    (((γ * γ' : GammaN Γ) : Γ) : SL(2, 𝓞 F)) 0 1 =
      ((γ : Γ) : SL(2, 𝓞 F)) 0 1 + ((γ' : Γ) : SL(2, 𝓞 F)) 0 1 := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, γ.2.2, GammaN.coe_one_one γ']
  ring

lemma GammaN.ext_of_zero_one {γ γ' : GammaN Γ}
    (h : ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = ((γ' : Γ) : SL(2, 𝓞 F)) 0 1) : γ = γ' := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact γ.2.2.trans γ'.2.2.symm
  · exact h
  · exact γ.2.1.trans γ'.2.1.symm
  · exact (GammaN.coe_one_one γ).trans (GammaN.coe_one_one γ').symm

variable (Γ) in
/-- The translation vector of an element of `GammaN Γ`, in the mixed space. -/
def GammaN.mixed : Additive (GammaN Γ) →+ mixedEmbedding.mixedSpace F where
  toFun γ := mixedEmbedding F
    (algebraMap (𝓞 F) F ((((Additive.toMul γ : GammaN Γ) : Γ) : SL(2, 𝓞 F)) 0 1))
  map_zero' := by simp
  map_add' γ γ' := by
    simp only [toMul_add, GammaN.mul_zero_one, map_add]

lemma GammaN.mixed_injective : Function.Injective (GammaN.mixed Γ) := by
  intro γ γ' h
  have h1 := IsFractionRing.injective (𝓞 F) F (mixedEmbedding_injective F h)
  exact congrArg Additive.ofMul (GammaN.ext_of_zero_one h1)

variable (Γ) in
/-- The lattice of translation vectors of `Γ`. -/
def GammaN.lattice : Submodule ℤ (mixedEmbedding.mixedSpace F) :=
  AddSubgroup.toIntSubmodule (AddMonoidHom.range (GammaN.mixed Γ))

lemma GammaN.mem_lattice {x : mixedEmbedding.mixedSpace F} :
    x ∈ GammaN.lattice Γ ↔ ∃ γ : Additive (GammaN Γ), GammaN.mixed Γ γ = x := Iff.rfl

instance instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice : DiscreteTopology (GammaN.lattice Γ) :=
  DiscreteTopology.of_subset (s := (mixedEmbedding.integerLattice F : Set _))
    (inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F))) (by
      rintro _ ⟨γ, rfl⟩
      exact ⟨_, rfl⟩)

theorem GammaN.isZLattice
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β) :
    IsZLattice ℝ (E := mixedEmbedding.mixedSpace F) (GammaN.lattice Γ) := by
  obtain ⟨𝔫, h0, h⟩ := h𝔫
  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
    Units.mk0 (𝔫 : FractionalIdeal (𝓞 F)⁰ F) (FractionalIdeal.coeIdeal_ne_zero.2 h0)
  refine ⟨top_unique ?_⟩
  rw [← IsZLattice.span_top (K := ℝ) (L := mixedEmbedding.idealLattice F I)]
  refine Submodule.span_mono ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mixedEmbedding.mem_idealLattice F I).1 hx
  have hy' : y ∈ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) := hy
  obtain ⟨β, hβ, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 F)⁰).1 hy'
  obtain ⟨γ, hγ⟩ := h β hβ
  exact ⟨Additive.ofMul γ, by simp [GammaN.mixed, hγ]⟩

variable (F) in
/-- For a totally complex field the mixed space is `ℂ^r`. -/
def toMixed [IsTotallyComplex F] : (InfinitePlace F → ℂ) ≃ₗ[ℝ] mixedEmbedding.mixedSpace F where
  toFun x := (fun _ => 0, fun w => x w.1)
  invFun p := fun w => p.2 ⟨w, IsTotallyComplex.isComplex w⟩
  map_add' x y := by
    apply Prod.ext
    · funext w; simp
    · funext w; simp
  map_smul' c x := by
    apply Prod.ext
    · funext w; simp
    · funext w; simp
  left_inv x := rfl
  right_inv p := by
    apply Prod.ext
    · funext w
      exact absurd w.2 (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1))
    · rfl

lemma toMixed_add_shift [IsTotallyComplex F] (x : InfinitePlace F → ℂ) (γ : GammaN Γ) :
    toMixed F (fun w => x w + GammaN.shift γ w) =
      GammaN.mixed Γ (Additive.ofMul γ) + toMixed F x := by
  apply Prod.ext
  · funext w
    exact absurd w.2 (not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1))
  · funext w
    simp [toMixed, GammaN.mixed, GammaN.shift, add_comm]

/-- **A bounded measurable strict fundamental set for the translation lattice of `Γ`.** -/
theorem exists_fundamental_translations [IsTotallyComplex F] (Γ : Subgroup (SL(2, 𝓞 F)))
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β) :
    ∃ D : Set (InfinitePlace F → ℂ), MeasurableSet D ∧ Bornology.IsBounded D ∧
      ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D := by
  have := GammaN.isZLattice h𝔫
  have : Module.Free ℤ (GammaN.lattice Γ) := ZLattice.module_free ℝ (GammaN.lattice Γ)
  have : Module.Finite ℤ (GammaN.lattice Γ) := ZLattice.module_finite ℝ (GammaN.lattice Γ)
  let b0 := Module.Free.chooseBasis ℤ (GammaN.lattice Γ)
  let b := b0.ofZLatticeBasis ℝ (GammaN.lattice Γ)
  have hspan : Submodule.span ℤ (Set.range b) = GammaN.lattice Γ := b0.ofZLatticeBasis_span ℝ
  let e := (toMixed F).toContinuousLinearEquiv
  have he : ∀ x, e x = toMixed F x := fun x => rfl
  refine ⟨e ⁻¹' ZSpan.fundamentalDomain b,
    (ZSpan.fundamentalDomain_measurableSet b).preimage e.continuous.measurable, ?_, ?_⟩
  · refine (e.symm.lipschitz.isBounded_image (ZSpan.fundamentalDomain_isBounded b)).subset ?_
    intro x hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · intro x
    obtain ⟨v, hv, hvu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (e x)
    have hvL : (v : mixedEmbedding.mixedSpace F) ∈ GammaN.lattice Γ :=
      (SetLike.ext_iff.1 hspan _).1 v.2
    obtain ⟨γa, hγ⟩ := GammaN.mem_lattice.1 hvL
    refine ⟨Additive.toMul γa, ?_, ?_⟩
    · show e (fun w => x w + GammaN.shift (Additive.toMul γa) w) ∈ ZSpan.fundamentalDomain b
      rw [he, toMixed_add_shift, ofMul_toMul, hγ]
      exact hv
    · intro γ' hγ'
      have hmem : GammaN.mixed Γ (Additive.ofMul γ') ∈ Submodule.span ℤ (Set.range b) :=
        (SetLike.ext_iff.1 hspan _).2 (GammaN.mem_lattice.2 ⟨_, rfl⟩)
      have h1 : (⟨GammaN.mixed Γ (Additive.ofMul γ'), hmem⟩ :
          Submodule.span ℤ (Set.range b)) +ᵥ e x ∈ ZSpan.fundamentalDomain b := by
        have h2 : e (fun w => x w + GammaN.shift γ' w) ∈ ZSpan.fundamentalDomain b := hγ'
        rw [he, toMixed_add_shift] at h2
        exact h2
      have h3 := congrArg Subtype.val (hvu _ h1)
      have h4 : GammaN.mixed Γ (Additive.ofMul γ') = GammaN.mixed Γ γa := h3.trans hγ.symm
      have h5 := GammaN.mixed_injective h4
      rw [← h5]
      rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-!
# WP-RF, part 4: Fourier series along `x` on `Γ\X` (stub S1 of WP-X)

Setting of WP-X "Remaining stubs": `F` totally complex, `Γ ≤ SL(2,𝓞_F)` containing the
translations `n(β)`, `β ∈ 𝔫`; `Λ = {GammaN.shift γ}` the translation lattice in `ι → ℂ`;

* `pair ν x = Σ_w Re(ν_w x_w)`, `eChar ν x = exp(2πi · pair ν x)`,
  `dualLat Γ = {ν | pair ν λ ∈ ℤ for all λ ∈ Λ}`;
* `stripFn D ν φ P = 1_D(P.x) · e_ν(P.x) · φ(P.v)`, the function `ψ` of
  `X.coeffFunctional Γ n ψ …` for the `(ν, φ)`-Fourier coefficient;
* `exists_latBasis`: a basis of `ι → ℂ` whose `ℤ`-span is `Λ`; the characters `chi bV m` of
  `RF_Torus` are the `eChar ν`, `ν ∈ dualLat Γ` (`exists_dual_of_chi`);
* **`eq_zero_of_coeff`** (S1 (b)): `u : X.L2 Γ` with all coefficient functionals zero is zero;
* `ae_eq_zero_of_strip`: the same for any measurable `GammaN Γ`-invariant function which is
  square integrable on boxes.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The pairing and the characters -/

/-- The real pairing `Σ_w Re(ν_w x_w)` on `ι → ℂ`. -/
def pair (ν x : InfinitePlace F → ℂ) : ℝ := ∑ w, (ν w * x w).re

/-- `e_ν(x) = exp(2πi Σ_w Re(ν_w x_w))`. -/
def eChar (ν x : InfinitePlace F → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (pair ν x : ℂ))

lemma norm_eChar (ν x : InfinitePlace F → ℂ) : ‖eChar ν x‖ = 1 := by
  have e : 2 * Real.pi * Complex.I * (pair ν x : ℂ)
      = ((2 * Real.pi * pair ν x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [eChar, e, Complex.norm_exp_ofReal_mul_I]

lemma measurable_pair (ν : InfinitePlace F → ℂ) : Measurable (pair ν) := by
  unfold pair
  exact Finset.measurable_sum _ fun w _ =>
    Complex.measurable_re.comp (measurable_const.mul (measurable_pi_apply w))

lemma measurable_eChar (ν : InfinitePlace F → ℂ) : Measurable (eChar ν) := by
  unfold eChar
  exact Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_pair ν)))

/-- `ψ(P) = 1_D(x) · e_ν(x) · φ(v)`: `X.coeffFunctional Γ n (stripFn D ν φ) …` is the
`(ν, φ)`-Fourier coefficient functional along the strip `{x ∈ D}`. -/
def stripFn (D : Set (InfinitePlace F → ℂ)) (ν : InfinitePlace F → ℂ)
    (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) : ℂ :=
  D.indicator (fun _ => (1 : ℂ)) P.x * (eChar ν P.x * φ P.v)

lemma measurable_stripFn {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (ν : InfinitePlace F → ℂ) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) :
    Measurable (stripFn D ν φ) := by
  unfold stripFn
  exact ((measurable_const.indicator hD).comp X.measurable_x).mul
    (((measurable_eChar ν).comp X.measurable_x).mul (hφ.comp X.measurable_v))

lemma norm_stripFn_le (D : Set (InfinitePlace F → ℂ)) (ν : InfinitePlace F → ℂ)
    {φ : (InfinitePlace F → ℝ) → ℂ} {C : ℝ} (hφ : ∀ v, ‖φ v‖ ≤ C) (P : X F) :
    ‖stripFn D ν φ P‖ ≤ C := by
  unfold stripFn
  rw [norm_mul, norm_mul, norm_eChar, one_mul]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hφ P.v)
  by_cases h : P.x ∈ D
  · rw [indicator_of_mem h, norm_one, one_mul]; exact hφ _
  · rw [indicator_of_notMem h, norm_zero, zero_mul]; exact hC

/-! ### A basis of the translation lattice -/

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.N_Shape
/-! # WP-N, file 2: the shape of the constant term of `E_Ψ` at `∞` for `Re s > 2` (MATH2 §2.1(b))

* `Cell Γ D n₀`: `D` is a measurable fundamental domain of the translation lattice of `Γ`, contained
  in `{‖x_w‖ ≤ n₀}`.  `Cell.of_hfund` converts from the form used by WP-X/WP-RF (`hfund`);
  `exists_cell` gives one for every `Γ` of finite index.
* `cf D n φ f = ∫_{box n} conj (1_D(x) φ(v)) f`: the constant-term functional (it is
  `X.coeffFunctional Γ n (RF.stripFn D 0 φ) …` on `L²(Γ\X)`, `coeffFunctional_eq_cf`).
* `mD D Ψ s = vol(D)⁻¹ ∫_D tail Ψ s (x, 1) dx`: the coefficient of `ht^{2−s}`.
* **`cf_eis`**: for `Re s > 2`, `n ≥ n₀`,
  `cf D n φ (E_Ψ(·,s)) = Ψ_s(0,1) · cf D n φ (ht^s) + mD D Ψ s · cf D n φ (ht^{2−s})`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Cells -/

lemma nInt_eq_of_GammaN (γ : GammaN Γ) :
    nInt (((γ : Γ) : SL(2, 𝓞 F)) 0 1) = ((γ : Γ) : SL(2, 𝓞 F)) := by
  have h1 : ((γ : Γ) : SL(2, 𝓞 F)) 1 0 = 0 := γ.2.1
  have h2 : ((γ : Γ) : SL(2, 𝓞 F)) 0 0 = 1 := γ.2.2
  have h3 := GammaN.coe_one_one γ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nInt_coe, h1, h2, h3]

lemma shift_mem_latN (γ : GammaN Γ) : (GammaN.shift γ : InfinitePlace F → ℂ) ∈ latN Γ := by
  refine ⟨((γ : Γ) : SL(2, 𝓞 F)) 0 1, ?_, rfl⟩
  change nInt (((γ : Γ) : SL(2, 𝓞 F)) 0 1) ∈ Γ
  rw [nInt_eq_of_GammaN]
  exact (γ : Γ).2

/-- The element of `GammaN Γ` with a given translation `β ∈ Λ_Γ`. -/
def ofLam (β : lamN Γ) : GammaN Γ :=
  ⟨⟨nInt (β : 𝓞 F), β.2⟩, ⟨nInt_upper _, by simp [nInt_coe]⟩⟩

lemma shift_ofLam (β : lamN Γ) : GammaN.shift (ofLam β) = embO (β : 𝓞 F) := by
  funext w
  simp [GammaN.shift, ofLam, nInt_coe, embO_apply, emb_apply]

/-- A finite-index subgroup contains the translations by a nonzero ideal. -/
lemma exists_ideal_translations (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β := by
  set k : ℕ := (Γ.index).factorial with hk
  have hk0 : ((k : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine ⟨Ideal.span {((k : ℕ) : 𝓞 F)}, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hk0, fun β hβ => ?_⟩
  obtain ⟨β', rfl⟩ := Ideal.mem_span_singleton'.mp hβ
  have hmem : nInt (β' * ((k : ℕ) : 𝓞 F)) ∈ Γ := by
    rw [mul_comm, ← RC.nInt_pow]
    exact RC.pow_factorial_index_mem Γ _
  refine ⟨ofLam ⟨_, hmem⟩, ?_⟩
  simp [ofLam, nInt_coe]

/-! ### The constant-term functional -/

/-- `∫_{box n} conj(1_D(x) φ(v)) f(x, v)`: the constant-term functional (frequency `0`). -/
def cf (D : Set (InfinitePlace F → ℂ)) (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ)
    (f : X F → ℂ) : ℂ :=
  ∫ P in X.box n, conj (stripFn D 0 φ P) * f P ∂X.vol F

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
/-! # WP-N, file 3: coefficients of `θ_Ψ` from continuations (MATH2 §2.1(c),(d); item 5)

* `differentiableAt_setIntegral`: a bounded holomorphic family integrates to a holomorphic function
  over a set of finite measure.
* `hInt Ψ n ψ s = ∫_{box n} conj ψ · h_s` is entire (`differentiable_hInt`).
* **`coeff_theta_of_continuation`** (all frequencies): if `a` is holomorphic on `E.slit`, equals
  `∫_{box n} conj ψ · E_Ψ(·, s)` for `Re s > 2`, and `(s_t − s₀) a(s_t) → r` along C5's ray, then
  `∫_{box n} conj ψ · θ_Ψ = r`.
* **`cf_theta_of_continuation`** (frequency `0`, MATH2 §2.1(d)): if `m'` is holomorphic on `E.slit`,
  equals `mD D Ψ` for `Re s > 2` and `(s_t − s₀) m'(s_t) → z`, then
  `cf D n φ (θ_Ψ) = z · cf D n φ (ht^{2/3})` for all `(n, φ)`.

`EisEigen Ψ s` (owner WP-RF) enters as the hypothesis `hE : ∀ s, 2 < s.re → EisEigen Ψ s`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

/-! ### Holomorphic dependence of integrals on a parameter -/

/-! ### The ray and the slit -/

/-- C5's ray `s_t = 4/3 + t(1 + i)`. -/
def ray (t : ℝ) : ℂ := (4 / 3 : ℂ) + t * (1 + Complex.I)

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The cut-off part against a bounded test function -/

/-- `∫_{box n} conj ψ · h_s`. -/
def hInt (Ψ : TSection ι 𝔪) (n : ℕ) (ψ : X F → ℂ) (s : ℂ) : ℂ :=
  ∫ P in X.box n, conj (ψ P) * hpart Ψ s P ∂X.vol F

/-! ### Coefficients of `θ_Ψ` from a continuation (all test functions) -/

/-! ### Frequency `0`: the residue of the `ht^{2−s}`-coefficient -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.RF_Deriv1
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-!
# WP-RF, part 5: derivative bounds of all orders for one factor of `ht_p^s` (stub D1, local part)

One factor of a pair height in the logarithmic chart `E1 = ℂ × ℝ ∋ (x, t)`, `v = e^t`:
`phi s c d (x, t) = (e^t / (|c x + d|² + |c|² e^{2t}))^s`.

**Method** (no Faà di Bruno, no explicit higher derivatives).  The vector
`Z = (u₁, u₂, q, r, U)`, `u = x̄/ρ`, `q = e^{2t}/ρ`, `r = 1/ρ`, `ρ = |x|² + e^{2t}`,
`U = κ·(e^t/ρ)^s`, satisfies a *polynomial autonomous system* `DZ = P(Z)` (`hasFDerivAt_Zfun`).
For such a system every iterated derivative is a smooth function of `Z` itself, the same for all
solutions (`exists_iter_poly`).  On `t ≥ -T` the vector `(u, q, r)` stays in a compact set, and
normalizing `U = 1` at the point gives

`place_bound`: `‖D^n (phi s c d)(y)‖ ≤ M · |phi s c d y|` for all `(c, d) ≠ 0` and all `y` with
`y.2 ≥ -T`, `M = M(s, n, T)`.  (For `n = 1, 2` this is (H2) of MATH2 §0.1.)
-/

set_option autoImplicit false

open scoped ComplexConjugate

noncomputable section

namespace ArtinKP.RF

/-! ### Polynomial autonomous systems -/

/-! ### The system of one factor -/

/-- The chart of one factor: `(x, t)`. -/
abbrev E1' : Type := ℂ × ℝ

/-- The state space `(u₁, u₂, q, r, U)`. -/
abbrev V5 : Type := ℝ × ℝ × ℝ × ℝ × ℂ

/-- `ρ'/ρ` as a function of the state and the direction. -/
def mfun (z : V5) (k : E1') : ℝ := 2 * z.1 * k.1.re + 2 * z.2.1 * k.1.im + 2 * z.2.2.1 * k.2

/-- The right-hand side of the system, in direction `k`. -/
def pfun (s : ℂ) (z : V5) (k : E1') : V5 :=
  (z.2.2.2.1 * k.1.re - z.1 * mfun z k, z.2.2.2.1 * k.1.im - z.2.1 * mfun z k,
    2 * z.2.2.1 * k.2 - z.2.2.1 * mfun z k, -(z.2.2.2.1 * mfun z k),
    s * z.2.2.2.2 * ((k.2 - mfun z k : ℝ) : ℂ))

/-- The right-hand side of the system as a continuous linear map. -/
def Psys (s : ℂ) (z : V5) : E1' →L[ℝ] V5 :=
  LinearMap.toContinuousLinearMap
    { toFun := pfun s z
      map_add' := fun k k' => by
        simp only [pfun, mfun, Prod.fst_add, Prod.snd_add, Complex.add_re, Complex.add_im,
          Prod.mk_add_mk, Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring, by ring, ?_⟩
        push_cast; ring
      map_smul' := fun a k => by
        simp only [pfun, mfun, Prod.smul_fst, Prod.smul_snd, Complex.real_smul, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul, RingHom.id_apply,
          Prod.smul_mk, Prod.mk.injEq, zero_mul, sub_zero, add_zero]
        refine ⟨by ring, by ring, by ring, by ring, ?_⟩
        push_cast; ring }

/-- `ρ = |x|² + e^{2t}`. -/
def rho0 (y : E1') : ℝ := y.1.re ^ 2 + y.1.im ^ 2 + Real.exp (2 * y.2)

/-- The solution `(Re x/ρ, Im x/ρ, e^{2t}/ρ, 1/ρ, κ (e^t/ρ)^s)`. -/
def Zfun (s κ : ℂ) (y : E1') : V5 :=
  (y.1.re * (rho0 y)⁻¹, y.1.im * (rho0 y)⁻¹, Real.exp (2 * y.2) * (rho0 y)⁻¹, (rho0 y)⁻¹,
    κ * Complex.exp (s * ((y.2 - Real.log (rho0 y) : ℝ) : ℂ)))

/-- The solution for the degenerate factor `e^{st}`. -/
def Zfun' (s κ : ℂ) (y : E1') : V5 := (0, 0, 0, 0, κ * Complex.exp (s * (y.2 : ℂ)))

/-- The projection to the last coordinate. -/
def pi5 : V5 →L[ℝ] ℂ :=
  (ContinuousLinearMap.snd ℝ ℝ ℂ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)).comp
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℂ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ × ℂ))))

/-! ### One factor of a pair height -/

/-- `|c x + d|² + |c|² e^{2t}` (`= H3.rowDen c d` in the chart). -/
def rho (c d : ℂ) (y : E1') : ℝ :=
  Complex.normSq (c * y.1 + d) + Complex.normSq c * Real.exp (2 * y.2)

/-- One factor of `I_{(c,d)}^s` in the chart: `(e^t/ρ)^s`. -/
def phi (s : ℂ) (c d : ℂ) (y : E1') : ℂ :=
  Complex.exp (s * ((y.2 - Real.log (rho c d y) : ℝ) : ℂ))

/-- `phi` for `(c, d) = (1, 0)`. -/
def phi0 (s : ℂ) (y : E1') : ℂ := Complex.exp (s * ((y.2 - Real.log (rho0 y) : ℝ) : ℂ))

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.RF_Deriv2
/-!
# WP-RF, part 7: derivative bounds for `I_{(c,d)}^s` and differentiation of the series (stub D1)

In the logarithmic chart `Coord F ∋ y = (x_w, t_w)_w`:

* `Uc s c d y = ∏_w phi s (σ_w c) (σ_w d) (y w) = I_{(c,d)}(chart y)^s` (`Uc_eq`);
* `Uc_bound`: `‖D^n (I_{(c,d)}^s ∘ chart)(y)‖ ≤ M · I_{(c,d)}(chart y)^{Re s}` for all pairs
  `(c, d) ≠ 0` of `F` and all `y` with `t_w ≥ -T`; `M = M(s, n, T)`.  All orders `n`, uniform in
  the pair and in `x`.  (`n = 1, 2`: the scaled first and second derivatives of D1.)
* `hasSum_lapE`: the chart Laplacian of a series which may be differentiated termwise twice.
* **`smooth_tsum_pairHt_cpow`, `lap_tsum_pairHt_cpow`**: for any family of pairs `(c_i, d_i)` and
  coefficients `a_i` with a locally uniform summable majorant of `|a_i| I_i^{Re s}`,
  `E(P) = ∑' i, a_i I_i(P)^s` is `X.Smooth` and `X.lap E = r s (2 - s) E`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The coordinate projection of the chart. -/
def projC (w : InfinitePlace F) : Coord F →L[ℝ] E1 := ContinuousLinearMap.proj w

/-- `I_{(c,d)}^s` in the chart, as a product over the places. -/
def Uc (s : ℂ) (c d : F) (y : Coord F) : ℂ :=
  ∏ w : InfinitePlace F, phi s (w.embedding c) (w.embedding d) (y w)

/-! ### Termwise Laplacian -/

/-! ### The series `∑ a_i I_i^s` -/

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.RF_Eis
/-!
# WP-RF, part 8: the series over pair classes (stub D1 of WP-B1, in B1's indexing)

For `Re s > 2` and bounded coefficients `a : PairClass S → ℂ`,
`E(P) = ∑' p, a p · ht_p(P)^s` is `X.Smooth` and `X.lap E = r s (2 - s) E`
(`smooth_tsum_ht_cpow`, `lap_tsum_ht_cpow`).  This is `RF_Deriv2` with B1's majorant
`PairClass.exists_summable_majorant_cpow`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  (S : Finset (FinitePlace F))

/-- The coefficient absorbing the `S`-norm: `ht_p^s = sNorm^{-s} · I_p^s`. -/
def coefS (a : PairClass S → ℂ) (s : ℂ) (p : PairClass S) : ℂ :=
  a p * Complex.exp (-(s * (Real.log (X.sNorm S p.out.c p.out.d) : ℂ)))

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.T_Arch
/-! # WP-T, file 2: the archimedean Whittaker function as a function on `X`

`WX s ν P = Winf s ν P.v = ∏_w jacquet s (−σ_w ν) v_w`.  For `Re s > 1`:

* `continuous_WX`, `differentiableOn_WX` (in `s`, `ν ≠ 0`), `exists_norm_WX_le` (bounded on
  `ball × box`);
* **`exists_WX_ne_zero`**: for every `s₁` (complex!) there is `δ > 0` with `WX s₁ ν P ≠ 0` whenever
  all `v_w < δ`.  (The Jacquet integral is `v^{2−s}·ĝ_s(νv)` with `ĝ_s` continuous and
  `ĝ_s(0) = π/(s−1) ≠ 0`; no information on zeros of `K_μ` of complex order is needed.)
* `phaseW s₁ ν`, a measurable test function of `v` of modulus `≤ 1` with
  `conj (phaseW s₁ ν P.v) * WX s₁ ν P = ‖WX s₁ ν P‖`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### One place -/

/-! ### The function on `X` -/

variable {F : Type*} [Field F] [NumberField F]

/-- `W_s(ν; ·)` as a function on `X`. -/
def WX (s : ℂ) (ν : F) (P : X F) : ℂ := Winf s ν P.v

/-! ### The phase test function -/

variable [IsTotallyComplex F]

/-- `z / ‖z‖`. -/
def unitPhase (z : ℂ) : ℂ := z / ((‖z‖ : ℝ) : ℂ)

/-- The unit phase of `W_{s₁}(ν; v)`, as a function of `v`. -/
def phaseW (s₁ : ℂ) (ν : F) (v : InfinitePlace F → ℝ) : ℂ :=
  unitPhase (WX s₁ ν (ofXV ((0 : InfinitePlace F → ℂ), v)))

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Mean
/-! # WP-T, file 1: strict cells of commensurable lattices (Mathlib only)

`PCell L D`: `D` is a measurable *strict* fundamental set of the subgroup `L` of `E` (every point
has exactly one translate in `D`) — the `hfund` form of WP-X2/WP-RF.

* `PCell.union`: if `L ≤ L₁` and `rep : κ → L₁` is a finite system of representatives of `L₁/L`,
  then `⋃_k (rep k + D)` is a strict cell of `L`.
* `exists_reps`: representatives from `L.relIndex L₁ ≠ 0`.
* **`mean_eq`**: let `D₁`, `D₂` be strict cells of `L₁`, `L₂`, `L ≤ L₁ ⊓ L₂` of finite index in
  both, `f` an `L₁`-periodic function, and suppose `∫_{t + D₂} f = I` for the representatives `t`
  of `L₂/L`.  Then `vol(D₂)·∫_{D₁} f = vol(D₁)·I`.
-/

open MeasureTheory Set

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableNeg E]

/-- A measurable strict fundamental set of the subgroup `L`. -/
structure PCell (L : AddSubgroup E) (D : Set E) : Prop where
  meas : MeasurableSet D
  fund : ∀ x : E, ∃! g : L, (g : E) + x ∈ D

/-- `t + D`. -/
def shiftSet (t : E) (D : Set E) : Set E := {x | x - t ∈ D}

lemma measurableSet_shiftSet (t : E) {D : Set E} (hD : MeasurableSet D) :
    MeasurableSet (shiftSet t D) :=
  (measurable_id.sub_const t) hD

/-- `⋃_k (rep k + D)`. -/
def unionSet {κ : Type*} (rep : κ → E) (D : Set E) : Set E := {x | ∃ k, x - rep k ∈ D}

lemma unionSet_eq {κ : Type*} (rep : κ → E) (D : Set E) :
    unionSet rep D = ⋃ k, shiftSet (rep k) D := by
  ext x; simp [unionSet, shiftSet]

variable {L L₁ L₂ : AddSubgroup E} {D D₁ D₂ : Set E}

/-- Representatives: `rep k ∈ L₁`, and every `g ∈ L₁` is congruent mod `L` to exactly one. -/
structure IsReps (L L₁ : AddSubgroup E) {κ : Type*} (rep : κ → E) : Prop where
  mem : ∀ k, rep k ∈ L₁
  uniq : ∀ g ∈ L₁, ∃! k, g - rep k ∈ L

/-- Representatives exist when the relative index is finite. -/
theorem exists_reps (hL : L.relIndex L₁ ≠ 0) :
    ∃ (κ : Type u) (_ : Fintype κ) (rep : κ → E), IsReps L L₁ rep := by
  have : (L.addSubgroupOf L₁).FiniteIndex := ⟨hL⟩
  have hfin : Finite (L₁ ⧸ L.addSubgroupOf L₁) := AddSubgroup.finite_quotient_of_finiteIndex
  refine ⟨L₁ ⧸ L.addSubgroupOf L₁, Fintype.ofFinite _, fun q => ((Quotient.out q : L₁) : E),
    fun q => (Quotient.out q : L₁).2, fun g hg => ?_⟩
  have key : ∀ q : L₁ ⧸ L.addSubgroupOf L₁,
      g - ((Quotient.out q : L₁) : E) ∈ L ↔ q = QuotientAddGroup.mk ⟨g, hg⟩ := by
    intro q
    have h1 : (QuotientAddGroup.mk (Quotient.out q) : L₁ ⧸ L.addSubgroupOf L₁) = q :=
      Quotient.out_eq q
    constructor
    · intro h
      rw [← h1, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      simpa [sub_eq_neg_add] using h
    · intro h
      have h2 : (QuotientAddGroup.mk (Quotient.out q) : L₁ ⧸ L.addSubgroupOf L₁)
          = QuotientAddGroup.mk ⟨g, hg⟩ := by rw [h1, h]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h2
      simpa [sub_eq_neg_add] using h2
  exact ⟨QuotientAddGroup.mk ⟨g, hg⟩, (key _).mpr rfl, fun q hq => (key q).mp hq⟩

section union

variable {κ : Type*} [Fintype κ] {rep : κ → E}

/-- **Union of translates**: a strict cell of the sublattice. -/
theorem PCell.union (hL : L ≤ L₁) (hrep : IsReps L L₁ rep) (h : PCell L₁ D) :
    PCell L (unionSet rep D) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [unionSet_eq]
    exact MeasurableSet.iUnion fun k => measurableSet_shiftSet _ h.meas
  obtain ⟨g₁, hg₁, hu⟩ := h.fund x
  obtain ⟨k, hk, hku⟩ := hrep.uniq (-(g₁ : E)) (L₁.neg_mem g₁.2)
  have hl : (g₁ : E) + rep k ∈ L := by
    have := L.neg_mem hk
    rwa [neg_sub, sub_neg_eq_add, add_comm] at this
  refine ⟨⟨_, hl⟩, ⟨k, ?_⟩, ?_⟩
  · change (g₁ : E) + rep k + x - rep k ∈ D
    have e : (g₁ : E) + rep k + x - rep k = (g₁ : E) + x := by abel
    rw [e]; exact hg₁
  · rintro ⟨l', hl'⟩ ⟨k', hk'⟩
    have hk'' : l' + x - rep k' ∈ D := hk'
    have hg' : l' - rep k' ∈ L₁ := L₁.sub_mem (hL hl') (hrep.mem k')
    have h1 := hu ⟨_, hg'⟩ (by
      change l' - rep k' + x ∈ D
      have e : l' - rep k' + x = l' + x - rep k' := by abel
      rw [e]; exact hk'')
    have h2 : l' - rep k' = (g₁ : E) := congrArg Subtype.val h1
    have h3 : -(g₁ : E) - rep k' ∈ L := by
      have e : -(g₁ : E) - rep k' = -l' := by rw [← h2]; abel
      rw [e]; exact L.neg_mem hl'
    have h4 : k' = k := hku k' h3
    subst h4
    refine Subtype.ext ?_
    change l' = (g₁ : E) + rep k'
    rw [← h2]; abel

end union

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Lat
/-! # WP-T, file 3: the lattices `Λ_Γ` (translations of `Γ`) and `Λ_M` (`B.transLat 𝔪 M`)

Both sit in `latO F = emb(𝓞_F)` (for `M ≥ 0`) and contain the image of a nonzero ideal, hence are
commensurable: `relIndex_inf_left/right`.

* `pcell_of_hfund`: WP-X2/WP-RF's `hfund` is a strict cell `T.PCell (N.latN Γ) D`;
  `exists_pcell_latN`.
* `exists_pcell_transLat`: a bounded strict cell of `Λ_M` (`M ≥ 0`), as a union of translates of a
  cell of `emb(𝓞_F)`;  `cellM 𝔪 M` (a chosen one, bounded by `cellN 𝔪 M`).
* `kap 𝔪 M = (vol(cellM 𝔪 M) · vol(𝔩_M))⁻¹` — the constant of all coefficient formulas
  (`= covol(𝓞_F)⁻¹` by WP-B's stub B-2; independent of the chosen cell: `volume_eq_cellM`).
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

/-! ### Ideal lattices -/

/-- `emb(𝓞_F)`. -/
def latO (F : Type*) [Field F] [NumberField F] : AddSubgroup (InfinitePlace F → ℂ) :=
  (⊤ : AddSubgroup (𝓞 F)).map embO

/-- `emb(I)`. -/
def idealLat (I : Ideal (𝓞 F)) : AddSubgroup (InfinitePlace F → ℂ) :=
  I.toAddSubgroup.map embO

lemma latN_top : latN (⊤ : Subgroup (SL(2, 𝓞 F))) = latO F := by
  have h : lamN (⊤ : Subgroup (SL(2, 𝓞 F))) = ⊤ := by
    ext β; exact ⟨fun _ => trivial, fun _ =>
      (Subgroup.mem_top (nInt β) : nInt β ∈ (⊤ : Subgroup (SL(2, 𝓞 F))))⟩
  unfold latN latO
  rw [h]

theorem relIndex_idealLat {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (idealLat I).relIndex (latO F) ≠ 0 := by
  unfold idealLat latO
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ embO_injective, AddSubgroup.relIndex_top_right]
  have h1 : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have h2 : Finite (𝓞 F ⧸ I.toAddSubgroup) := h1
  exact AddSubgroup.index_ne_zero_of_finite

theorem relIndex_of_idealLat_le {A : AddSubgroup (InfinitePlace F → ℂ)} {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hIA : idealLat I ≤ A) : A.relIndex (latO F) ≠ 0 := fun h =>
  relIndex_idealLat hI (AddSubgroup.relIndex_eq_zero_of_le_left hIA h)

/-! ### The two families of lattices -/

theorem transLat_le_latO {M : ℤ} (hM : 0 ≤ M) : transLat 𝔪 M ≤ latO F := by
  rintro x ⟨b, hb, rfl⟩
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (b : F) ≤ 1 := by
    intro v
    by_cases hv : 𝔪 ≤ v.asIdeal
    · refine (hb v hv).trans ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · exact Set.integer_valuation_le_one (S := placesOf 𝔪) (K := F) b hv
  obtain ⟨β, hβ⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (b : F) hval
  refine ⟨β, trivial, ?_⟩
  rw [embR_apply, embO_apply, ← hβ]

theorem exists_idealLat_le_transLat (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ idealLat 𝔫 ≤ transLat 𝔪 M := by
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  refine ⟨Ideal.span {b ^ M.toNat}, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hb0, ?_⟩
  rintro x ⟨β, hβ, rfl⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hβ
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) (c * b ^ M.toNat), ?_, rfl⟩
  have h1 : Small 𝔪 0 ((c : 𝓞 F) : F) := fun v _ => by
    simpa using v.valuation_le_one c
  have h2 := h1.mul (small_pow_of_mem hb M.toNat)
  have h3 : Small 𝔪 M (((c : 𝓞 F) : F) * ((b : 𝓞 F) : F) ^ M.toNat) :=
    h2.mono (by rw [zero_add]; exact Int.self_le_toNat M)
  change Small 𝔪 M (((algebraMap (𝓞 F) (SInt 𝔪) (c * b ^ M.toNat) : SInt 𝔪) : F))
  have e : ((algebraMap (𝓞 F) (SInt 𝔪) (c * b ^ M.toNat) : SInt 𝔪) : F)
      = ((c : 𝓞 F) : F) * ((b : 𝓞 F) : F) ^ M.toNat := by
    change (((c * b ^ M.toNat : 𝓞 F)) : F) = _
    push_cast; rfl
  rw [e]
  exact h3

/-! ### Cells -/

/-- The `hfund` form of WP-X2/WP-RF is a strict cell of `Λ_Γ`. -/
theorem pcell_of_hfund {Γ : Subgroup (SL(2, 𝓞 F))} {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ,
      ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D) :
    PCell (latN Γ) D := by
  refine ⟨hD, fun x => ?_⟩
  obtain ⟨γ, hγ, huniq⟩ := hfund x
  have key : ∀ γ' : GammaN Γ, (fun w => x w + GammaN.shift γ' w)
      = (GammaN.shift γ' : InfinitePlace F → ℂ) + x := fun γ' => by
    funext w; simp [add_comm]
  refine ⟨⟨GammaN.shift γ, shift_mem_latN γ⟩, ?_, fun g hg => ?_⟩
  · change (GammaN.shift γ : InfinitePlace F → ℂ) + x ∈ D
    rw [← key]; exact hγ
  · obtain ⟨β, hβ, hgβ⟩ := g.2
    have h1 : (fun w => x w + GammaN.shift (ofLam ⟨β, hβ⟩) w) ∈ D := by
      rw [key, shift_ofLam, hgβ]; exact hg
    have h2 := huniq _ h1
    refine Subtype.ext ?_
    change (g : InfinitePlace F → ℂ) = GammaN.shift γ
    rw [← h2, shift_ofLam, hgβ]

theorem exists_pcell_latN (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    ∃ (D : Set (InfinitePlace F → ℂ)) (n₀ : ℕ), PCell (latN Γ) D ∧
      ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀ := by
  obtain ⟨D, hD, hb, hfund⟩ := exists_fundamental_translations Γ (exists_ideal_translations Γ)
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨D, N, pcell_of_hfund hD hfund, fun x hx w =>
    (norm_le_pi_norm x w).trans ((hR x hx).trans hN)⟩

/-- **A bounded strict cell of `Λ_M`**, `M ≥ 0`. -/
theorem exists_pcell_transLat (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    ∃ (D : Set (InfinitePlace F → ℂ)) (n₀ : ℕ), PCell (transLat 𝔪 M) D ∧
      ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀ := by
  obtain ⟨D₀, n₀, h₀, hb₀⟩ := exists_pcell_latN (⊤ : Subgroup (SL(2, 𝓞 F)))
  rw [latN_top] at h₀
  obtain ⟨𝔫, h𝔫, hle⟩ := exists_idealLat_le_transLat h𝔪 M
  obtain ⟨κ, _, rep, hrep⟩ := exists_reps (relIndex_of_idealLat_le h𝔫 hle)
  obtain ⟨N, hN⟩ := exists_nat_ge (∑ k, ‖rep k‖)
  refine ⟨unionSet rep D₀, n₀ + N, h₀.union (transLat_le_latO hM) hrep, ?_⟩
  rintro x ⟨k, hk⟩ w
  have h1 := hb₀ _ hk w
  have h2 : ‖rep k w‖ ≤ N :=
    ((norm_le_pi_norm (rep k) w).trans
      (Finset.single_le_sum (f := fun k => ‖rep k‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ k))).trans hN
  have e : x w = (x - rep k) w + rep k w := by simp
  rw [e]
  push_cast
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

open Classical in
/-- A chosen bounded strict cell of `Λ_M` (`∅` unless `𝔪 ≠ ⊥`, `M ≥ 0`). -/
def cellM (𝔪 : Ideal (𝓞 F)) (M : ℤ) : Set (InfinitePlace F → ℂ) :=
  if h : 𝔪 ≠ ⊥ ∧ 0 ≤ M then (exists_pcell_transLat h.1 h.2).choose else ∅

open Classical in
/-- A bound for `cellM`. -/
def cellN (𝔪 : Ideal (𝓞 F)) (M : ℤ) : ℕ :=
  if h : 𝔪 ≠ ⊥ ∧ 0 ≤ M then (exists_pcell_transLat h.1 h.2).choose_spec.choose else 0


/-- The constant `(vol(Λ_M-cell)·vol(𝔩_M))⁻¹` (`= covol(𝓞_F)⁻¹`, WP-B stub B-2). -/
def kap (𝔪 : Ideal (𝓞 F)) (M : ℤ) : ℂ :=
  ((((volume (cellM 𝔪 M)).toReal * vol 𝔪 M : ℝ)) : ℂ)⁻¹

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Coef
/-! # WP-T, file 4: the `ν`-th coefficient of `E_Φ` over a cell, for `Re s > 2`

* `freq ν = (−2σ_w ν)_w`: `conj (RF.eChar (freq ν) x) = B.chiInf ν x`, so that
  `X.coeffFunctional Γ n (RF.stripFn D (freq ν) φ) …` is the `ν`-th coefficient against `conj φ`.
* `HasCoefT Ψ ν' a₀ D κ` (twisted section, any coefficient series `a₀`): for `Re s > 2` and all
  `v`, `∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`;
  `HasCoef hG hz6 Φ ν D κ` is the case `Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`.
  - `hasCoef_transLat`: a strict cell of `Λ_M` (`M ≥ 0` valid) has it with `κ = kap 𝔪 M` (WP-B);
  - **`hasCoef_latN`**: so has every bounded strict cell of the translation lattice of any `Γ`
    fixing `Φ.twist`, provided `conj e_∞(ν·)` is `Λ_Γ`-periodic (`T.mean_eq`).
* `Afun Γ Ψ n ψ s = ∫_{box n} conj ψ · lift (resPart Γ Ψ s) + ∫_{box n} conj ψ · h_s`: holomorphic
  on `E.slit`, `= ∫_{box n} conj ψ · E_Ψ` for `Re s > 2`, ray limit `∫ conj ψ · θ`.
* `Wc D n φ ν s = N.cf D n φ (WX s ν)`: holomorphic on `Re s > 1`; `exists_Wc_ne_zero`.
* **`Afun_eq_of_hasCoefT`**: `Afun … (stripFn D (freq ν') φ) s = κ·a₀(s)·Wc D n φ ν' s`, `Re s > 2`.
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

/-! ### The frequency of `ν` in WP-RF's parametrization -/

/-- `ν ↦ (−2σ_w ν)_w`. -/
def freq (ν : F) : InfinitePlace F → ℂ := fun w => -2 * w.embedding ν

/-! ### Cells that compute the coefficient -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

/-- `D` computes the `ν'`-th Fourier coefficient of `E_Ψ(·, s)`, `Re s > 2`, with coefficient
series `a₀` and constant `κ`:
`∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`. -/
def HasCoefT (Ψ : TSection ι 𝔪) (ν' : F) (a₀ : ℂ → ℂ) (D : Set (InfinitePlace F → ℂ))
    (κ : ℂ) : Prop :=
  ∀ s : ℂ, 2 < s.re → ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w),
    ∫ x in D, eis Ψ s (X.mk x v hv) * chiInf ν' x
      = (((volume D).toReal : ℝ) : ℂ) * κ * Winf s ν' v * a₀ s

/-- `HasCoefT` for a genuine section and its Kubota series `𝔞_Φ(ν, ·)`. -/
def HasCoef (D : Set (InfinitePlace F → ℂ)) (κ : ℂ) : Prop :=
  HasCoefT (Φ.twist hG hz6) (ν : F) ((kubota hG hz6).aSer Φ ν) D κ

variable {hG hz6 Φ ν}

/-! ### The coefficient function of the continuation -/

/-- `∫_{box n} conj ψ · (E^{ext}_Ψ(·, s))`, written as resolvent part plus cut-off part. -/
def Afun (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (n : ℕ) (ψ : X F → ℂ) (s : ℂ) : ℂ :=
  (∫ Q in X.box n, conj (ψ Q) * X.lift Γ (resPart Γ Ψ s) Q ∂X.vol F) + hInt Ψ n ψ s

/-! ### The archimedean factor -/

/-- `∫_{box n} conj(1_D(x) φ(v)) · W_s(ν; v)`. -/
def Wc (D : Set (InfinitePlace F → ℂ)) (n : ℕ) (φ : (InfinitePlace F → ℝ) → ℂ) (ν : F)
    (s : ℂ) : ℂ :=
  cf D n φ (WX s ν)

/-! ### The coefficient of the series over an admissible cell -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Cont
/-! # WP-T, file 5: the continuation of the coefficient series and its residue (generic form)

Function level (`E.slit`, the ray `N.ray t = 4/3 + t(1+i)`):
* `contSlit a₀` — the holomorphic function on `E.slit` agreeing with `a₀` on `Re s > 2`, if there
  is one (`contSlit_spec`, `contSlit_unique`);
* `resSlit a₀ = lim_{t↓0} (s_t − 4/3)·contSlit a₀ (s_t)`.

For a twisted section `Ψ`, a frequency `ν' ≠ 0` and a coefficient series `a₀` with one admissible
cell (`HasSeed Ψ ν' a₀`: some bounded measurable `D₀` of positive volume with
`HasCoefT Ψ ν' a₀ D₀ κ₀`, `κ₀ ≠ 0`):
* `differentiableOn_contSlit`, `contSlit_eq` — MATH2 (C6) for `ν' ≠ 0`;
* **`Afun_eq_contSlit`**: for every `Γ` fixing `Ψ`, every admissible cell `(D, κ)`, every box
  `n ⊇ D` and test function `φ`, on all of `E.slit`
  `∫_{box n} conj (stripFn D (freq ν') φ) · E^{ext} = κ · contSlit a₀ s · Wc D n φ ν' s`;
* `tendsto_resSlit` — MATH2 (C7); `hasResOn` (the `E.HasResOn` statement);
* **`integral_theta_of_hasCoefT`**:
  `∫_{box n} conj (stripFn D (freq ν') φ) · θ_Ψ = κ · resSlit a₀ · Wc D n φ ν' (4/3)`.

The genuine sections `Φ` (`Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`) are in `T_Theta`.
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
  {ι : F →+* ℂ}

/-! ### Function level -/

open Classical in
/-- The holomorphic continuation of `a₀` from `Re s > 2` to `E.slit` (`0` if there is none). -/
def contSlit (a₀ : ℂ → ℂ) : ℂ → ℂ :=
  if h : ∃ a : ℂ → ℂ, DifferentiableOn ℂ a E.slit ∧ ∀ s : ℂ, 2 < s.re → a s = a₀ s
  then h.choose else 0

/-- `lim_{t↓0} (s_t − 4/3)·contSlit a₀ (s_t)`, `s_t = 4/3 + t(1+i)` (junk if there is no limit). -/
def resSlit (a₀ : ℂ → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit a₀ (ray t)

/-! ### Twisted sections with a coefficient series -/

/-- One admissible cell with nonzero constant. -/
def HasSeed (Ψ : TSection ι 𝔪) (ν' : F) (a₀ : ℂ → ℂ) : Prop :=
  ∃ (D₀ : Set (InfinitePlace F → ℂ)) (κ₀ : ℂ) (n₀ : ℕ), HasCoefT Ψ ν' a₀ D₀ κ₀ ∧ κ₀ ≠ 0 ∧
    MeasurableSet D₀ ∧ volume D₀ ≠ 0 ∧ ∀ x ∈ D₀, ∀ w, ‖x w‖ ≤ n₀

/-! ### The residue -/

end

end ArtinKP.T
end

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

lemma coe_ne_zero {ν : SInt 𝔪} (hν : ν ≠ 0) : (ν : F) ≠ 0 := fun h => hν (Subtype.ext h)

/-- **`τ_Φ(ν) = lim_{t↓0} (s_t − 4/3)·𝔞_Φ(ν, s_t)`**, `s_t = 4/3 + t(1+i)`. -/
def tau : ℂ := resSlit ((kubota hG hz6).aSer Φ ν)

/-! ### The archimedean factor as an integral over `v` -/


/-! ### Fourier coefficients of `θ` for the cells of `Γ` -/

end

end ArtinKP.T
end


