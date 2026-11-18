-- Prove2me | Definitions.Def_ArtinKPB017
-- name    : ArtinKPB017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T10:00:48.177859+00:00
-- url     : https://prove2.me/theorems/fc0d39d2-c62e-4406-873a-7202ce808a6c
-- title:
--   Definitions bundle ArtinKPB017 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 401 declarations of that development: 255 definitions, 7 inductive types or structures, 25 instances and 114 theorems. The definitions and types are `ArtinKP.A.CubicPkg.transport`, `ArtinKP.A.ofSymbolPkg`, `ArtinKP.A.placeMap`, `ArtinKP.A.rootBack`, `ArtinKP.B.mCoeff`, `ArtinKP.B.sumBig`, `ArtinKP.B7.Cform`, `ArtinKP.B7.csum`, `ArtinKP.B7.gaussP`, `ArtinKP.B7.phi`, `ArtinKP.B7.tab`, `ArtinKP.BZ.constC`, `ArtinKP.C9.DualCover`, `ArtinKP.C9.TransLevel`, `ArtinKP.C9.lowInt`, `ArtinKP.C9.mModel`, `ArtinKP.C9.psiSum`, `ArtinKP.C9.stabGroup`, `ArtinKP.DD.DiffInS`, `ArtinKP.DD.cutD`, `ArtinKP.E.ClsP`, `ArtinKP.E.Kubota.LEq`, `ArtinKP.E.Kubota.Y`, `ArtinKP.E.Kubota.Yterm`, `ArtinKP.E.Kubota.wt`, `ArtinKP.E.PrimeDatum`, `ArtinKP.E.Theta.PER`, `ArtinKP.E.Theta.wloc`, `ArtinKP.E.UInv`, `ArtinKP.E.splitFun`, `ArtinKP.F.Adm`, `ArtinKP.F.IsU`, `ArtinKP.F.bR`, `ArtinKP.F.cq`, `ArtinKP.F.ratio`, `ArtinKP.F.rhs54`, `ArtinKP.F.scaleLat`, `ArtinKP.F.scaleSet`, `ArtinKP.FA.IsReps`, `ArtinKP.FA.OQ` and 222 more.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `C0.C0R_Tr`, `C0.C0YMain`, `C0.C0YPkg`, `C0.C0ZA`, `C0.C0ZF`, `C0.C0ZK`, `C0.C0ZS`, `C0.C0ZU`, `C0.C0ZV`, `KP.A_Exist`, `KP.A_Transport`, `KP.B1_Pairs`, `KP.B7_Gauss`, `KP.B7_System`, `KP.BZ_Main`, `KP.B_Const`, `KP.B_Kub`, `KP.C9_Const`, `KP.C9_Nonvanish`, `KP.C9_Tau`, `KP.DD_Cut`, `KP.E_Residue`, `KP.E_Series`, `KP.F_Alg_Main`, `KP.F_Alg_Sum`, `KP.F_Alg_Symbol`, `KP.F_Eis_Fourier`, `KP.F_Eis_Main`, `KP.F_Eis_Op`, `KP.F_Per_Const`, `KP.F_Per_Kernel`, `KP.F_Per_Main`, `KP.F_Per_Mean`, `KP.F_Per_U`, `KP.F_Per_Z`, `KP.G1_Delta`, `KP.G1_FI`, `KP.G2a_Bessel`, `KP.G2a_Block`, `KP.G2a_Def`, `KP.G2a_Dx`, `KP.G2a_Exp`, `KP.G2a_Fwd`, `KP.G2a_Major`, `KP.GK_J`, `KP.GR_Arch`, `KP.GR_Flip`, `KP.GR_Theta`, `KP.GW_Main`, `KP.GW_One`, `KP.H0_Cut`, `KP.H0_Main`, `KP.H0_Nu`, `KP.H0_Rot`, `KP.H0_Row`, `KP.HB_Aut`, `KP.HB_C`, `KP.HB_Dig`, `KP.HB_Sec`, `KP.H_Dig`, `KP.H_Grid`, `KP.H_Sum`, `KP.K_Bessel`, `KP.K_Kappa`, `KP.K_Weyl`, `KP.N2_Cor`, `KP.N2_Cusp`, `KP.N2_Lattice`, `KP.N2_Main`, `KP.N2_Unfold`, `KP.N_Level`, `KP.N_Main`, `KP.N_Orbit`, `KP.N_Res`, `KP.N_Shape`, `KP.RF_Fourier`, `KP.RF_Parseval`, `KP.RF_Strip`, `KP.RF_Torus`, `KP.S_BigCell`, `KP.S_Ops`, `KP.S_Twisted`, `KP.T_Lat`, `KP.T_Vanish`, `KP.X2_Chart`, `KP.X_Meas`, `KP.X_Quot`, `KP.X_QuotC`, `KP.X_Space`, `KP.Z_Phi`, `KP.Z_Series`, `T12.C3B_Norm`, `T12.C3B_Unit`, `T12.C3I_Add`, `T12.C3I_Cut`, `T12.C3I_Gauss`, `T12.C3P_Zeta`, `T12.L3J_Kappa`, `T12.L3P_Gen`, `T12.L3P_Sfin`, `T12.L3P_Val`, `T12.L3V_Base`, `T12.L3V_Defs`, `T12.L3V_Ideal`, `T12.L3V_Res`, `T12.L3V_VP`, `T12.L3X_Meas`, `T12.L3X_Pack`, `T12.L3X_Phi`, `T12.L3X_Rho`, `T12.T12B_Euler`.
--
--   **Imports.** It imports the published bundles `Def_ArtinHecke`, `Def_ArtinHeckeLocalCoeff`, `Def_ArtinHeckePoissonLocal`, `Def_ArtinHeckeProbe`, `Def_ArtinHeckeSModel`, `Def_ArtinHeckeTheta`, `Def_DedekindDomain_Completion_BaseChange`, `Def_ExtCitation_LocalLevelResidues`, `Def_IsDedekindDomain_FiniteUnitIdeles`, `Def_IsDedekindDomain_FiniteUnitIdelesOutside`, `Def_LanglandsTunnell_ArtinCoreCTM`, `Def_M4aHerbrand_GenuineDescent`, `Def_M4aHerbrand_IdeleClassVocab`, `Def_M4aHerbrand_SIdeleClassGroup`, `Def_NormIndex_AdmissibleExpOfDegree`, `Def_NumberField_ArchimedeanIdeleModule`, `Def_NumberField_PlaceDecompositionAction` and `Def_NumberField_TateGlobalZeta`; the bundles `ArtinKPB003` and `ArtinKPB016` of this split; the published statements `LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd`, `M4aHerbrand_restrictNormalHom_idelicArtinMap_eq`, `NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank`, `NumberField_isOpen_range_powMonoidHom_units_adicCompletion` and `ArtinKP.GK.exists_summable_majorant_norm_jdef`.
--
--   **Imported by** (directly, in this split): the statements `ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds`, `ArtinKP.C9.ae_eq_htC_of_coeff`, `ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero`, `ArtinKP.C9.theta_psiSum_ne_zero`, `ArtinKP.E.primeDatum_gen`, `ArtinKP.E.wloc_mul_sym_eq`, `ArtinKP.FA.prop54`, `ArtinKP.FB.U_eis_primeElt`, `ArtinKP.FB.sum_eInf_reps`, `ArtinKP.F.U_coeff`, `ArtinKP.F.const_adm`, `ArtinKP.F.hasCoefT_restrict`, `ArtinKP.F.hasCoef_adm`, `ArtinKP.F.integral_restrict_scale`, `ArtinKP.F.mD_restrict`, `ArtinKP.F.tendsto_mext_zPsi`, `ArtinKP.F.zPsi_add`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.F.zPsi_smul`, `ArtinKP.F.zPsi_sum`, `ArtinKP.F.zPsi_translate_nMat`, `ArtinKP.G2a.ThetaM_nT`, `ArtinKP.G2a.ThetaM_tau`, `ArtinKP.G2a.coeff_thetaS_freq`, `ArtinKP.G2a.coeff_thetaS_of_ne`, `ArtinKP.G2a.continuous_thetaS`, `ArtinKP.G2a.exists_major`, `ArtinKP.G2a.exists_major_prod`, `ArtinKP.G2a.hasFDerivAt_block`, `ArtinKP.G2a.integral_strip_term`, `ArtinKP.G2a.norm_tau_le`, `ArtinKP.G2a.thetaS_smul_gammaN`, `ArtinKP.G2a.thetaT_translate`, `ArtinKP.GK.exists_isDelta`, `ArtinKP.GK.hne`, `ArtinKP.GK.kw_theta_of_diffInS`, `ArtinKP.GK.tau_eq_rpow_mul_coefF_mul_kir`, `ArtinKP.GK.theta_per_gen_of_isExterior`, `ArtinKP.GK.xi_wSec_phiB_eq_jdef`, `ArtinKP.GR.ThetaM_flip`, `ArtinKP.GR.secCut_of_isCyclotomicExtension`, `ArtinKP.GR.thetaG_eq_tsum_forward`, `ArtinKP.GR.thetaG_eq_tsum_reflected`, `ArtinKP.GR.thmE`, `ArtinKP.GR.weylFlip_of_thmE`, `ArtinKP.H0.FmOf_clauses`, `ArtinKP.H0.goal_of_KPCut`, `ArtinKP.HB.autCut2_of_secCut`, `ArtinKP.HB.digCoefNu_eq`, `ArtinKP.HB.finsum_maskProd_mul_digCoefNu_eq_eprod`, `ArtinKP.HB.kpCutNu_of_autCut2`, `ArtinKP.HB.loc_weyl`, `ArtinKP.HB.local_D`, `ArtinKP.H.sum_maskProd_sAddChar`, `ArtinKP.H.summable_forward_coef`, `ArtinKP.H.summable_reflected_coef`, `ArtinKP.K.kappaB_iteratedDeriv_bound_shift`, `ArtinKP.N2.cusp_integral_eq_zero`, `ArtinKP.N2.integrable_orbit`, `ArtinKP.N2.mD_eq_of_le`, `ArtinKP.N2.orbit_integral_eq_zero`, `ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N2.zRes_eq_zPsi`, `ArtinKP.N.Acoef_cross`, `ArtinKP.N.Acoef_eq`, `ArtinKP.N.cf_eis`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.differentiableOn_Acoef`, `ArtinKP.N.differentiableOn_mext`, `ArtinKP.N.tendsto_ray_Acoef`, `ArtinKP.N.zRes_eq_of_continuation`, `ArtinKP.Z.tsum_G0` and `ArtinPrimitiveRoots.L3V.norm_gs`; the proofs of `ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds`, `ArtinKP.C9.ae_eq_htC_of_coeff`, `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero`, `ArtinKP.C9.theta_psiSum_ne_zero`, `ArtinKP.E.primeDatum_gen`, `ArtinKP.E.wloc_mul_sym_eq`, `ArtinKP.FA.prop54`, `ArtinKP.FB.U_eis_primeElt`, `ArtinKP.FB.sum_eInf_reps`, `ArtinKP.F.U_coeff`, `ArtinKP.F.const_adm`, `ArtinKP.F.hasCoefT_restrict`, `ArtinKP.F.hasCoef_adm`, `ArtinKP.F.integral_restrict_scale`, `ArtinKP.F.mD_restrict`, `ArtinKP.F.tendsto_mext_zPsi`, `ArtinKP.F.zPsi_add`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.F.zPsi_smul`, `ArtinKP.F.zPsi_sum`, `ArtinKP.F.zPsi_translate_nMat`, `ArtinKP.G2a.ThetaM_nT`, `ArtinKP.G2a.ThetaM_tau`, `ArtinKP.G2a.coeff_thetaS_freq`, `ArtinKP.G2a.coeff_thetaS_of_ne`, `ArtinKP.G2a.continuous_thetaS`, `ArtinKP.G2a.exists_major`, `ArtinKP.G2a.exists_major_prod`, `ArtinKP.G2a.hasFDerivAt_block`, `ArtinKP.G2a.integral_strip_term`, `ArtinKP.G2a.jac_bound`, `ArtinKP.G2a.norm_tau_le`, `ArtinKP.G2a.thetaS_smul_gammaN`, `ArtinKP.G2a.thetaT_translate`, `ArtinKP.GK.exists_isDelta`, `ArtinKP.GK.hne`, `ArtinKP.GK.kw_theta_of_diffInS`, `ArtinKP.GK.tau_eq_rpow_mul_coefF_mul_kir`, `ArtinKP.GK.tau_eq_zero_of_theta`, `ArtinKP.GK.theta_per_gen_of_isExterior`, `ArtinKP.GK.xi_wSec_phiB_eq_jdef`, `ArtinKP.GR.ThetaM_flip`, `ArtinKP.GR.secCut_of_isCyclotomicExtension`, `ArtinKP.GR.thetaG_eq_tsum_forward`, `ArtinKP.GR.thetaG_eq_tsum_reflected`, `ArtinKP.GR.thmE`, `ArtinKP.GR.weylFlip_of_thmE`, `ArtinKP.H0.FmOf_clauses`, `ArtinKP.H0.goal_of_KPCut`, `ArtinKP.HB.autCut2_of_secCut`, `ArtinKP.HB.digCoefNu_eq`, `ArtinKP.HB.finsum_maskProd_mul_digCoefNu_eq_eprod`, `ArtinKP.HB.kpCutNu_of_autCut2`, `ArtinKP.HB.loc_weyl`, `ArtinKP.HB.local_D`, `ArtinKP.H.sum_maskProd_sAddChar`, `ArtinKP.H.summable_forward_coef`, `ArtinKP.H.summable_reflected_coef`, `ArtinKP.K.kappaB_iteratedDeriv_bound_shift`, `ArtinKP.N2.cusp_integral_eq_zero`, `ArtinKP.N2.integrable_orbit`, `ArtinKP.N2.mD_eq_of_le`, `ArtinKP.N2.orbit_integral_eq_zero`, `ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N2.zRes_eq_zPsi`, `ArtinKP.N.Acoef_cross`, `ArtinKP.N.Acoef_eq`, `ArtinKP.N.cf_eis`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.differentiableOn_Acoef`, `ArtinKP.N.differentiableOn_mext`, `ArtinKP.N.lift_theta_translate`, `ArtinKP.N.tendsto_ray_Acoef`, `ArtinKP.N.zRes_eq_of_continuation`, `ArtinKP.T.coeffFunctional_theta_twist_eq`, `ArtinKP.Z.tsum_G0`, `ArtinPrimitiveRoots.L3V.norm_gs` and `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`.
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
import Definitions.Def_ArtinKPB003
import Definitions.Def_ArtinKPB016
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_NumberField_isOpen_range_powMonoidHom_units_adicCompletion
import Theorems.Thm_ArtinKP_GK_exists_summable_majorant_norm_jdef

section
-- module Solutions.Artin.C0.C0R_Tr
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

section Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mem_map_equiv (f : R ≃+* S) (I : Ideal R) (y : S) : y ∈ I.map f ↔ f.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, f.symm_apply_apply]; exact hx,
    fun h => ⟨_, h, f.apply_symm_apply y⟩⟩

end Ideals

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

theorem absNorm_map_equiv (e : F ≃+* F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

/-! ### The residue symbol transports -/

/-! ### `AllowedGen` transports -/

end C0R

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.C0.C0YPkg
/-! C0Y: the local-symbol package and the `S`-pairing built from it. -/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace C0Y

variable (F : Type) [Field F] [NumberField F]

/-- The embedding `Fˣ → F_vˣ`. -/
def emb (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* (v.adicCompletion F)ˣ :=
  Units.map (algebraMap F (v.adicCompletion F) : F →* v.adicCompletion F)

/-- The properties of the local `ℓ`-th Hilbert symbols used for C0-H. -/
structure SymbolPkg (ℓ : ℕ) where
  h : (v : HeightOneSpectrum (𝓞 F)) → Fˣ →* (v.adicCompletion F)ˣ →* rootsOfUnity ℓ F
  steinberg : ∀ v (a : Fˣ), h v a (emb F v (-a)) = 1
  prod_eq_one : ∀ (a b : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ v ∉ T, h v a (emb F v b) = 1) → ∏ v ∈ T, h v a (emb F v b) = 1
  nondeg : ∀ v (a : Fˣ), (∀ b, h v a b = 1) →
    emb F v a ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range
  unit_unit : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∉ v.asIdeal → ∀ a b : Fˣ,
    v.valuation F (a : F) = 1 → v.valuation F (b : F) = 1 → h v a (emb F v b) = 1
  tame : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∉ v.asIdeal → ∀ (a π : Fˣ) (ω : F),
    v.valuation F (a : F) = 1 → v.valuation F (π : F) = WithZero.exp (-1 : ℤ) → ω ^ ℓ = 1 →
    v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / ℓ) - ω) < 1 →
    (((h v a (emb F v π) : Fˣ)) : F) = ω

variable {F} {ℓ : ℕ} (P : SymbolPkg F ℓ)

/-- The symbol at `v` restricted to global elements, as a pairing on `Fˣ`. -/
def SymbolPkg.hv (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* Fˣ →* rootsOfUnity ℓ F where
  toFun a := (P.h v a).comp (emb F v)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem SymbolPkg.hv_apply (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    P.hv v a b = P.h v a (emb F v b) := rfl

theorem rootsOfUnity_pow_eq_one {M : Type*} [CommMonoid M] (z : rootsOfUnity ℓ M) : z ^ ℓ = 1 := by
  have := z.2
  rw [mem_rootsOfUnity] at this
  exact Subtype.ext (by simpa using this)

/-- The symbol vanishes on local `ℓ`-th powers in the second slot. -/
theorem SymbolPkg.h_pow (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (c : (v.adicCompletion F)ˣ) :
    P.h v a (c ^ ℓ) = 1 := by
  rw [map_pow]; exact rootsOfUnity_pow_eq_one _

theorem SymbolPkg.h_of_mem_range (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ)
    {b : (v.adicCompletion F)ˣ}
    (hb : b ∈ (powMonoidHom ℓ : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range) :
    P.h v a b = 1 := by
  obtain ⟨c, rfl⟩ := hb; exact P.h_pow v a c

end C0Y
end
end

section
-- module Solutions.Artin.C0.C0YMain
/-! C0Y: clause 5 (reciprocity) and the assembly of C0-H from local-symbol packages. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain ArtinPrimitiveRoots
open scoped nonZeroDivisors

noncomputable section

namespace C0Y

/-- The packages that C0-H needs: local `ℓ`-th Hilbert symbols for totally complex number
fields containing `μ_ℓ`. -/
def PkgHyp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ), ℓ.Prime → (∃ ζ : F, IsPrimitiveRoot ζ ℓ) →
    (∀ w : InfinitePlace F, w.IsComplex) → Nonempty (SymbolPkg F ℓ)

end C0Y
end
end

section
-- module Solutions.Artin.C0.C0ZA
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-! C0Z: the library's idelic Artin map for an abelian extension, and ideles at one place. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

/-! ### Generic part: any abelian extension `K/E` of `Type`-level number fields -/

section Generic

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  [IsGalois E K]

/-- Ramified primes divide a fixed nonzero ideal (to be proved from the different). -/
theorem exists_ramified_dvd :
    ∃ 𝔣 : Ideal (𝓞 E), 𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 E),
      (primeAbove E K v).inertia (K ≃ₐ[E] K) ≠ ⊥ → v.asIdeal ∣ 𝔣 := by
  classical
  have hD : differentIdeal (𝓞 E) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  refine ⟨(differentIdeal (𝓞 E) (𝓞 K)).comap (algebraMap (𝓞 E) (𝓞 K)), ?_, ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · intro v hv
    have hP : primeAbove E K v ∣ differentIdeal (𝓞 E) (𝓞 K) := by
      rw [dvd_differentIdeal_iff]
      intro hun
      apply hv
      have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[E] K) v.asIdeal (primeAbove E K v)
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove E K v) (K ≃ₐ[E] K),
        Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at h1
      exact Subgroup.eq_bot_of_card_eq _ h1
    rw [Ideal.dvd_iff_le] at hP ⊢
    calc (differentIdeal (𝓞 E) (𝓞 K)).comap (algebraMap (𝓞 E) (𝓞 K))
        ≤ (primeAbove E K v).comap (algebraMap (𝓞 E) (𝓞 K)) := Ideal.comap_mono hP
      _ = v.asIdeal := under_primeAbove E K v

theorem exists_admissible :
    ∃ 𝔣 : Ideal (𝓞 E), NumberField.NormIndex.IsAdmissibleModulusOfDegree E K
      (Module.finrank E K) 𝔣 := by
  obtain ⟨𝔣, h0, hram⟩ := exists_ramified_dvd E K
  obtain ⟨𝔣', -, -, h⟩ :=
    exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E K 𝔣 h0 hram (Module.finrank E K)
  exact ⟨𝔣', h⟩

/-- The four defining properties of the idelic Artin map, as the library states them. -/
def IsIdelicArtin [IsMulCommutative (K ≃ₐ[E] K)] (𝔣 : Ideal (𝓞 E))
    (r : (AdeleRing (𝓞 E) E)ˣ →* (K ≃ₐ[E] K)) : Prop :=
  principalIdeles (𝓞 E) E ≤ r.ker ∧
  r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E K).idelicNorm.range ∧
  Function.Surjective r ∧
  ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
    r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E K v ^ placeOrd E (projFin E u) v

theorem exists_idelicArtin [IsMulCommutative (K ≃ₐ[E] K)] :
    ∃ 𝔣 r, NumberField.NormIndex.IsAdmissibleModulusOfDegree E K (Module.finrank E K) 𝔣 ∧
      IsIdelicArtin E K 𝔣 r := by
  obtain ⟨𝔣, h𝔣⟩ := exists_admissible E K
  obtain ⟨r, h1, h2, h3, h4⟩ :=
    exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      E K 𝔣 h𝔣
  exact ⟨𝔣, r, h𝔣, h1, h2, h3, h4⟩

/-- Chosen modulus and Artin map. -/
def artinMod [IsMulCommutative (K ≃ₐ[E] K)] : Ideal (𝓞 E) := (exists_idelicArtin E K).choose
def artinMap [IsMulCommutative (K ≃ₐ[E] K)] : (AdeleRing (𝓞 E) E)ˣ →* (K ≃ₐ[E] K) :=
  (exists_idelicArtin E K).choose_spec.choose
theorem artinMap_spec [IsMulCommutative (K ≃ₐ[E] K)] :
    NumberField.NormIndex.IsAdmissibleModulusOfDegree E K (Module.finrank E K) (artinMod E K) ∧
      IsIdelicArtin E K (artinMod E K) (artinMap E K) :=
  (exists_idelicArtin E K).choose_spec.choose_spec

end Generic

/-! ### The idele supported at one finite place -/

section Single

variable (E : Type) [Field E] [NumberField E]

open scoped Classical

/-- The finite adele equal to `x` at `v` and `1` elsewhere. -/
def fsingle (v : HeightOneSpectrum (𝓞 E)) (x : v.adicCompletion E) : FiniteAdeleRing (𝓞 E) E :=
  RestrictedProduct.mulSingle _ v x

theorem fsingle_apply (v w : HeightOneSpectrum (𝓞 E)) (x : v.adicCompletion E) :
    (fsingle E v x) w = Pi.mulSingle (M := fun w => w.adicCompletion E) v x w := rfl

theorem fsingle_mul (v : HeightOneSpectrum (𝓞 E)) (x y : v.adicCompletion E) :
    fsingle E v x * fsingle E v y = fsingle E v (x * y) := by
  apply RestrictedProduct.ext
  intro w
  show (fsingle E v x) w * (fsingle E v y) w = (fsingle E v (x * y)) w
  rw [fsingle_apply, fsingle_apply, fsingle_apply, Pi.mulSingle_mul]
  rfl

theorem fsingle_one (v : HeightOneSpectrum (𝓞 E)) : fsingle E v 1 = 1 := by
  apply RestrictedProduct.ext
  intro w
  show (fsingle E v 1) w = 1
  rw [fsingle_apply, Pi.mulSingle_one]; rfl

/-- `single v z`: the idele equal to `z` at `v` and `1` at every other place. -/
def single (v : HeightOneSpectrum (𝓞 E)) : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ where
  toFun z :=
    { val := (1, fsingle E v (z : v.adicCompletion E))
      inv := (1, fsingle E v ((z⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E))
      val_inv := by
        refine Prod.ext (mul_one _) ?_
        show fsingle E v _ * fsingle E v _ = 1
        rw [fsingle_mul, Units.mul_inv, fsingle_one]
      inv_val := by
        refine Prod.ext (mul_one _) ?_
        show fsingle E v _ * fsingle E v _ = 1
        rw [fsingle_mul, Units.inv_mul, fsingle_one] }
  map_one' := by
    apply Units.ext
    refine Prod.ext rfl ?_
    show fsingle E v 1 = 1
    exact fsingle_one E v
  map_mul' z z' := by
    apply Units.ext
    refine Prod.ext (mul_one _).symm ?_
    show fsingle E v ((z * z' : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      fsingle E v (z : v.adicCompletion E) * fsingle E v (z' : v.adicCompletion E)
    rw [fsingle_mul, Units.val_mul]

end Single

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZK
/-! C0Z: Kummer characters `σ ↦ σβ/β ∈ μ_ℓ(F)` for any Galois extension `M/F` and any
`β ∈ Mˣ` with `β^ℓ ∈ F`, when `μ_ℓ ⊂ F`; Kummer fields. -/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace C0Z

variable {F : Type} [Field F] {ℓ : ℕ} [NeZero ℓ]

/-- Every `ℓ`-th root of unity of an `F`-field comes from `F`. -/
theorem exists_of_pow_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
    (x : M) (hx : x ^ ℓ = 1) : ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = x := by
  have hζM := hζ.map_of_injective (FaithfulSMul.algebraMap_injective F M)
  obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], by rw [map_pow, hi]⟩

variable {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
include hζ

/-- A Kummer generator: a nonzero `β` with `β^ℓ ∈ F`. -/
structure KGen (M : Type*) [Field M] [Algebra F M] (ℓ : ℕ) where
  β : M
  ne_zero : β ≠ 0
  pow_mem : ∃ a : F, β ^ ℓ = algebraMap F M a

variable {M}

theorem ratio_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : (σ g.β / g.β) ^ ℓ = 1 := by
  obtain ⟨a, ha⟩ := g.pow_mem
  rw [div_pow, ← map_pow, ha, AlgEquiv.commutes, ← ha, div_self (pow_ne_zero _ g.ne_zero)]

theorem ratio_mem (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = σ g.β / g.β :=
  exists_of_pow_eq_one hζ M _ (ratio_pow hζ g σ)

/-- The value of the Kummer character in `F`. -/
def kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : F := (ratio_mem hζ g σ).choose

theorem kval_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : kval hζ g σ ^ ℓ = 1 :=
  (ratio_mem hζ g σ).choose_spec.1

theorem algebraMap_kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M (kval hζ g σ) = σ g.β / g.β :=
  (ratio_mem hζ g σ).choose_spec.2

theorem fix_ratio (g : KGen (F := F) M ℓ) (σ τ : M ≃ₐ[F] M) :
    σ (τ g.β / g.β) = τ g.β / g.β := by
  rw [← algebraMap_kval hζ g τ, AlgEquiv.commutes]

/-- The Kummer character `σ ↦ σβ/β`, valued in `μ_ℓ(F)`. -/
def kch (g : KGen (F := F) M ℓ) : (M ≃ₐ[F] M) →* rootsOfUnity ℓ F where
  toFun σ := rootsOfUnity.mkOfPowEq (kval hζ g σ) (kval_pow hζ g σ)
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, OneMemClass.coe_one, Units.val_one]
    apply FaithfulSMul.algebraMap_injective F M
    rw [algebraMap_kval hζ, map_one, AlgEquiv.one_apply, div_self g.ne_zero]
  map_mul' σ τ := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul]
    apply FaithfulSMul.algebraMap_injective F M
    rw [map_mul, algebraMap_kval hζ, algebraMap_kval hζ, algebraMap_kval hζ, AlgEquiv.mul_apply]
    have h1 : τ g.β = (τ g.β / g.β) * g.β := by field_simp [g.ne_zero]
    conv_lhs => rw [h1, map_mul, fix_ratio hζ g σ τ]
    field_simp [g.ne_zero]

theorem algebraMap_kch (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M ((kch hζ g σ : Fˣ) : F) = σ g.β / g.β := by
  simp only [kch, MonoidHom.coe_mk, OneHom.coe_mk, rootsOfUnity.coe_mkOfPowEq]
  exact algebraMap_kval hζ g σ

theorem kch_eq_iff (g g' : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    kch hζ g σ = kch hζ g' σ ↔ σ g.β / g.β = σ g'.β / g'.β := by
  rw [← algebraMap_kch hζ, ← algebraMap_kch hζ]
  constructor
  · intro h; rw [h]
  · intro h
    apply Subtype.ext; apply Units.ext
    exact FaithfulSMul.algebraMap_injective F M h

/-- Product of generators. -/
def KGen.mul (g g' : KGen (F := F) M ℓ) : KGen (F := F) M ℓ where
  β := g.β * g'.β
  ne_zero := mul_ne_zero g.ne_zero g'.ne_zero
  pow_mem := by
    obtain ⟨a, ha⟩ := g.pow_mem
    obtain ⟨a', ha'⟩ := g'.pow_mem
    exact ⟨a * a', by rw [mul_pow, ha, ha', map_mul]⟩

theorem kch_mul (g g' : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    kch hζ (g.mul g') σ = kch hζ g σ * kch hζ g' σ := by
  apply Subtype.ext; apply Units.ext
  apply FaithfulSMul.algebraMap_injective F M
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul, algebraMap_kch hζ]
  simp only [KGen.mul, map_mul]
  field_simp [g.ne_zero, g'.ne_zero]

/-- The character depends only on `β^ℓ`. -/
theorem kch_eq_of_pow_eq (g g' : KGen (F := F) M ℓ) (h : g.β ^ ℓ = g'.β ^ ℓ) :
    kch hζ g = kch hζ g' := by
  ext σ
  have := (kch_eq_iff hζ g g' σ).mpr
  rw [this]
  have hr : (g'.β / g.β) ^ ℓ = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ g'.ne_zero)]
  obtain ⟨y, -, hy⟩ := exists_of_pow_eq_one hζ M _ hr
  have hg' : g'.β = algebraMap F M y * g.β := by rw [hy]; field_simp [g.ne_zero]
  rw [hg', map_mul, AlgEquiv.commutes]
  have hy0 : algebraMap F M y ≠ 0 := by
    rw [hy]; exact div_ne_zero g'.ne_zero g.ne_zero
  field_simp [g.ne_zero, hy0]

/-- Restriction to a normal subextension. -/
theorem kch_restrict (L : Type*) [Field L] [Algebra F L] [Algebra L M] [IsScalarTower F L M]
    [Normal F L] (g : KGen (F := F) L ℓ) (σ : M ≃ₐ[F] M) :
    kch hζ g (AlgEquiv.restrictNormalHom L σ) =
      kch hζ (M := M) ⟨algebraMap L M g.β, by simpa using g.ne_zero, by
        obtain ⟨a, ha⟩ := g.pow_mem
        exact ⟨a, by rw [← map_pow, ha, ← IsScalarTower.algebraMap_apply]⟩⟩ σ := by
  apply Subtype.ext; apply Units.ext
  apply FaithfulSMul.algebraMap_injective F M
  rw [IsScalarTower.algebraMap_apply F L M, algebraMap_kch hζ, algebraMap_kch hζ, map_div₀]
  congr 1
  exact AlgEquiv.restrictNormal_commutes σ L g.β

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZF
/-! C0Z: the Kummer fields `F(a^{1/ℓ})` and `F(a^{1/ℓ}, a'^{1/ℓ})` as splitting fields. -/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace C0Z

variable (F : Type) [Field F] (ℓ : ℕ)

/-- `F(a^{1/ℓ})`. -/
def KF (a : Fˣ) : Type := (X ^ ℓ - C (a : F)).SplittingField

/-- `F(a^{1/ℓ}, a'^{1/ℓ})`. -/
def KF2 (a a' : Fˣ) : Type := ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))).SplittingField

variable (a a' : Fˣ)

instance instFieldKF : Field (KF F ℓ a) := inferInstanceAs (Field (SplittingField _))
instance instAlgebraKF : Algebra F (KF F ℓ a) := inferInstanceAs (Algebra F (SplittingField _))
instance instFieldKF2 : Field (KF2 F ℓ a a') := inferInstanceAs (Field (SplittingField _))
instance instAlgebraKF2 : Algebra F (KF2 F ℓ a a') := inferInstanceAs (Algebra F (SplittingField _))
instance instIsSplittingFieldKFHSubPolynomialHPowNatXCoeRingHomCVal : IsSplittingField F (KF F ℓ a) (X ^ ℓ - C (a : F)) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance instIsSplittingFieldKF2HMulPolynomialHSubHPowNatXCoeRingHomCVal : IsSplittingField F (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance instFiniteDimensionalKF : FiniteDimensional F (KF F ℓ a) := IsSplittingField.finiteDimensional _ (X ^ ℓ - C (a : F))
instance instFiniteDimensionalKF2 : FiniteDimensional F (KF2 F ℓ a a') :=
  IsSplittingField.finiteDimensional _ ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
instance instNormalKF : Normal F (KF F ℓ a) := Normal.of_isSplittingField (X ^ ℓ - C (a : F))
instance instNormalKF2 : Normal F (KF2 F ℓ a a') :=
  Normal.of_isSplittingField ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))

section CharZero

variable [CharZero F]

instance instIsGaloisKF : IsGalois F (KF F ℓ a) := { }
instance instIsGaloisKF2 : IsGalois F (KF2 F ℓ a a') := { }

end CharZero

instance instNumberFieldKF [NumberField F] : NumberField (KF F ℓ a) := NumberField.of_module_finite F _
instance instNumberFieldKF2 [NumberField F] : NumberField (KF2 F ℓ a a') := NumberField.of_module_finite F _

variable {F ℓ}

theorem exists_root_of_splits {M : Type*} [Field M] [Algebra F M] (hℓ : ℓ ≠ 0)
    (hs : Splits ((X ^ ℓ - C (a : F)).map (algebraMap F M))) : ∃ β : M, β ^ ℓ = algebraMap F M a := by
  have hdeg : ((X ^ ℓ - C (a : F)).map (algebraMap F M)).degree ≠ 0 := by
    rw [degree_map]
    exact degree_ne_of_natDegree_ne (by rw [natDegree_X_pow_sub_C]; exact hℓ)
  obtain ⟨β, hβ⟩ := hs.exists_eval_eq_zero hdeg
  refine ⟨β, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C] at hβ
  exact sub_eq_zero.mp hβ

/-- A Kummer generator from a root of `X^ℓ - a`. -/
def kgenOf {M : Type*} [Field M] [Algebra F M] {β : M} (hβ : β ^ ℓ = algebraMap F M a)
    (hℓ : ℓ ≠ 0) : KGen (F := F) M ℓ where
  β := β
  ne_zero := by
    rintro rfl
    rw [zero_pow hℓ, eq_comm, map_eq_zero] at hβ
    exact a.ne_zero hβ
  pow_mem := ⟨a, hβ⟩

theorem splits_KF (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a : F)).map (algebraMap F (KF F ℓ a))) :=
  IsSplittingField.splits (KF F ℓ a) (X ^ ℓ - C (a : F))

theorem ne_zero_X_pow_sub_C (hℓ : ℓ ≠ 0) : (X ^ ℓ - C (a : F)) ≠ 0 :=
  X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hℓ) _

theorem splits_KF2_left (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a : F)).map (algebraMap F (KF2 F ℓ a a'))) := by
  have h := IsSplittingField.splits (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
  refine h.of_dvd ?_ (Polynomial.map_dvd _ (dvd_mul_right _ _))
  rw [Polynomial.map_ne_zero_iff (algebraMap F _).injective]
  exact mul_ne_zero (ne_zero_X_pow_sub_C a hℓ) (ne_zero_X_pow_sub_C a' hℓ)

theorem splits_KF2_right (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a' : F)).map (algebraMap F (KF2 F ℓ a a'))) := by
  have h := IsSplittingField.splits (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
  refine h.of_dvd ?_ (Polynomial.map_dvd _ (dvd_mul_left _ _))
  rw [Polynomial.map_ne_zero_iff (algebraMap F _).injective]
  exact mul_ne_zero (ne_zero_X_pow_sub_C a hℓ) (ne_zero_X_pow_sub_C a' hℓ)

theorem root_pow_of_mem_rootSet {M : Type*} [Field M] [Algebra F M] {b : F} {r : M}
    (hr : aeval r (X ^ ℓ - C b) = 0) : r ^ ℓ = algebraMap F M b := by
  simpa [sub_eq_zero] using hr

section Comm

variable [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

/-- A root of `X^ℓ - a` is a multiple of a fixed generator by an element of `F`. -/
theorem eq_smul_of_pow_eq {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ) {r : M}
    (hr : r ^ ℓ = g.β ^ ℓ) : ∃ c : F, r = algebraMap F M c * g.β := by
  have h1 : (r / g.β) ^ ℓ = 1 := by rw [div_pow, hr, div_self (pow_ne_zero _ g.ne_zero)]
  obtain ⟨c, -, hc⟩ := exists_of_pow_eq_one hζ M _ h1
  exact ⟨c, by rw [hc]; field_simp [g.ne_zero]⟩

theorem fixes_of_kch_eq_one {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : kch hζ g σ = 1) : σ g.β = g.β := by
  have := algebraMap_kch hζ g σ
  rw [h, OneMemClass.coe_one, Units.val_one, map_one, eq_comm, div_eq_one_iff_eq g.ne_zero] at this
  exact this

theorem fixes_root {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : σ g.β = g.β) {r : M} (hr : r ^ ℓ = g.β ^ ℓ) : σ r = r := by
  obtain ⟨c, rfl⟩ := eq_smul_of_pow_eq hζ g hr
  rw [map_mul, AlgEquiv.commutes, h]

/-- The Galois group of `F(a^{1/ℓ}, a'^{1/ℓ})/F` is abelian. -/
theorem isMulCommutative_KF2 : IsMulCommutative (KF2 F ℓ a a' ≃ₐ[F] KF2 F ℓ a a') := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨β, hβ⟩ := exists_root_of_splits a hℓ (splits_KF2_left a a' hℓ)
  obtain ⟨β', hβ'⟩ := exists_root_of_splits a' hℓ (splits_KF2_right a a' hℓ)
  let g := kgenOf a hβ hℓ
  let g' := kgenOf a' hβ' hℓ
  have hinj : ∀ σ : KF2 F ℓ a a' ≃ₐ[F] KF2 F ℓ a a', kch hζ g σ = 1 → kch hζ g' σ = 1 → σ = 1 := by
    intro σ h1 h2
    have f1 := fixes_of_kch_eq_one hζ g σ h1
    have f2 := fixes_of_kch_eq_one hζ g' σ h2
    apply AlgEquiv.coe_toAlgHom_injective
    refine AlgHom.ext_of_adjoin_eq_top
      (IsSplittingField.adjoin_rootSet (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))))
      fun r hr => ?_
    rw [mem_rootSet] at hr
    show σ r = r
    rw [map_mul, mul_eq_zero] at hr
    rcases hr.2 with h | h
    · exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet h]; exact hβ.symm)
    · exact fixes_root hζ g' σ f2 (by rw [root_pow_of_mem_rootSet h]; exact hβ'.symm)
  refine ⟨⟨fun σ τ => ?_⟩⟩
  have : σ * τ * (τ * σ)⁻¹ = 1 := hinj _
    (by rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, mul_comm])
    (by rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, mul_comm])
  exact mul_inv_eq_one.mp this

/-- The Galois group of `F(a^{1/ℓ})/F` is abelian. -/
theorem isMulCommutative_KF : IsMulCommutative (KF F ℓ a ≃ₐ[F] KF F ℓ a) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨β, hβ⟩ := exists_root_of_splits a hℓ (splits_KF a hℓ)
  let g := kgenOf a hβ hℓ
  have hinj : ∀ σ : KF F ℓ a ≃ₐ[F] KF F ℓ a, kch hζ g σ = 1 → σ = 1 := by
    intro σ h1
    have f1 := fixes_of_kch_eq_one hζ g σ h1
    apply AlgEquiv.coe_toAlgHom_injective
    refine AlgHom.ext_of_adjoin_eq_top
      (IsSplittingField.adjoin_rootSet (KF F ℓ a) (X ^ ℓ - C (a : F))) fun r hr => ?_
    rw [mem_rootSet] at hr
    show σ r = r
    exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet hr.2]; exact hβ.symm)
  refine ⟨⟨fun σ τ => ?_⟩⟩
  have : σ * τ * (τ * σ)⁻¹ = 1 := hinj _
    (by rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul, mul_comm])
  exact mul_inv_eq_one.mp this

end Comm

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZS
/-! C0Z: the local Kummer symbol `(a, b)_v ∈ μ_ℓ(F)` from the idelic Artin map, and its
multiplicativity in `a`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- The chosen root of `X^ℓ - a` in `F(a^{1/ℓ})`. -/
def rootKF (a : Fˣ) : KGen (F := F) (KF F ℓ a) ℓ :=
  kgenOf a (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
    (NeZero.ne ℓ)

/-- The local symbol `(a, ·)_v : F_vˣ → μ_ℓ(F)`. -/
def sym (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) : (v.adicCompletion F)ˣ →* rootsOfUnity ℓ F :=
  haveI := isMulCommutative_KF a hζ
  (kch hζ (rootKF F a)).comp ((artinMap F (KF F ℓ a)).comp (single F v))

/-- The symbol can be computed in any abelian extension `M ⊇ F(a^{1/ℓ})`, with any root of
`X^ℓ - a` in `M`. -/
theorem sym_eq_of_le (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (M : Type) [Field M] [NumberField M]
    [Algebra F M] [IsGalois F M] [IsMulCommutative (M ≃ₐ[F] M)] (ι : KF F ℓ a →ₐ[F] M)
    (g : KGen (F := F) M ℓ) (hg : g.β ^ ℓ = algebraMap F M a) (b : (v.adicCompletion F)ˣ) :
    sym F hζ v a b = kch hζ g (artinMap F M (single F v b)) := by
  haveI := isMulCommutative_KF a hζ
  letI : Algebra (KF F ℓ a) M := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F (KF F ℓ a) M := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  obtain ⟨h𝔣, h1, h2, h3, h4⟩ := artinMap_spec F M
  obtain ⟨h𝔣L, hL1, hL2, hL3, hL4⟩ := artinMap_spec F (KF F ℓ a)
  have hres := restrictNormalHom_idelicArtinMap_eq F M (KF F ℓ a) _ h𝔣 _ h1 h2 h3 h4 _ h𝔣L _
    hL1 hL2 hL3 hL4 (single F v b)
  simp only [sym, MonoidHom.coe_comp, Function.comp_apply]
  rw [← hres, kch_restrict hζ (KF F ℓ a) (rootKF F a)]
  rw [kch_eq_of_pow_eq hζ _ g ?_]
  show (algebraMap (KF F ℓ a) M (rootKF F a).β) ^ ℓ = g.β ^ ℓ
  have : (rootKF F a).β ^ ℓ = algebraMap F (KF F ℓ a) a :=
    (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
  rw [← map_pow, this, ← IsScalarTower.algebraMap_apply, hg]

theorem sym_mul (v : HeightOneSpectrum (𝓞 F)) (a a' : Fˣ) (b : (v.adicCompletion F)ˣ) :
    sym F hζ v (a * a') b = sym F hζ v a b * sym F hζ v a' b := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  haveI := isMulCommutative_KF2 a a' hζ
  obtain ⟨β, hβ⟩ := exists_root_of_splits a hℓ (splits_KF2_left a a' hℓ)
  obtain ⟨β', hβ'⟩ := exists_root_of_splits a' hℓ (splits_KF2_right a a' hℓ)
  let g := kgenOf a hβ hℓ
  let g' := kgenOf a' hβ' hℓ
  have hgg : (g.mul g').β ^ ℓ = algebraMap F (KF2 F ℓ a a') ((a * a' : Fˣ) : F) := by
    show (β * β') ^ ℓ = _
    rw [mul_pow, hβ, hβ', Units.val_mul, map_mul]
  have hs3 : Splits ((X ^ ℓ - C ((a * a' : Fˣ) : F)).map (algebraMap F (KF2 F ℓ a a'))) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (FaithfulSMul.algebraMap_injective F (KF2 F ℓ a a'))) hgg
  let ι1 := IsSplittingField.lift (KF F ℓ a) (X ^ ℓ - C (a : F)) (splits_KF2_left a a' hℓ)
  let ι2 := IsSplittingField.lift (KF F ℓ a') (X ^ ℓ - C (a' : F)) (splits_KF2_right a a' hℓ)
  let ι3 := IsSplittingField.lift (KF F ℓ (a * a')) (X ^ ℓ - C ((a * a' : Fˣ) : F)) hs3
  rw [sym_eq_of_le F hζ v (a * a') (KF2 F ℓ a a') ι3 (g.mul g') hgg,
    sym_eq_of_le F hζ v a (KF2 F ℓ a a') ι1 g hβ, sym_eq_of_le F hζ v a' (KF2 F ℓ a a') ι2 g' hβ',
    kch_mul]

/-- The local symbol as a pairing `Fˣ × F_vˣ → μ_ℓ(F)`. -/
def symHom (v : HeightOneSpectrum (𝓞 F)) : Fˣ →* (v.adicCompletion F)ˣ →* rootsOfUnity ℓ F where
  toFun a := sym F hζ v a
  map_one' := by
    ext b
    have h := sym_mul F hζ v 1 1 b
    rw [one_mul] at h
    have : sym F hζ v 1 b = 1 := by
      have h' : sym F hζ v 1 b * sym F hζ v 1 b = sym F hζ v 1 b * 1 := by rw [mul_one, ← h]
      exact mul_left_cancel h'
    rw [this]; rfl
  map_mul' a a' := by ext b; simp only [MonoidHom.mul_apply]; rw [sym_mul]

@[simp] theorem symHom_apply (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (b : (v.adicCompletion F)ˣ) :
    symHom F hζ v a b = sym F hζ v a b := rfl

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZU
/-! C0Z: Kummer extensions are unramified at `v ∤ ℓ a`; the unit–unit symbol. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- A root of unity of `F` as an algebraic integer. -/
def rootO (μ : rootsOfUnity ℓ F) : 𝓞 F :=
  ⟨((μ : Fˣ) : F), IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by
    have := μ.2; rw [mem_rootsOfUnity] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]; exact isIntegral_one)⟩

end C0Z
end
end

section
-- module Solutions.Artin.C0.C0ZV
/-! C0Z: the tame formula `(a, π)_v ≡ a^{(Nv - 1)/ℓ} (mod v)` at `v ∤ ℓ`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter
  LanglandsTunnell.P2.Artin Polynomial
open scoped IsMulCommutative NumberField.PlaceDecomp

noncomputable section

namespace C0Z

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- An algebraic integer from an element of `F` that is a root of unity. -/
def toO (x : F) (hx : x ^ ℓ = 1) : 𝓞 F :=
  ⟨x, IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by rw [hx]; exact isIntegral_one)⟩

end C0Z
end
end

section
-- module Solutions.Artin.KP.A_Exist
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S.brk_neg_left _root_.ArtinKP.S.brk_neg_right _root_.ArtinKP.S.brk_one_left _root_.ArtinKP.S.brk_one_right _root_.ArtinKP.S.brk_pow_three_left _root_.ArtinKP.S.brk_pow_three_right _root_.ArtinKP.S.brk_self _root_.ArtinKP.S.brk_zero_left _root_.ArtinKP.S.brk_zero_right _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-A: existence of the cubic package for `F : Type`

`CubicPkg F` is obtained from `C0Y.SymbolPkg F 3` (`C0Z.pkgHyp`, built on the library's idelic
Artin map, which lives in universe `0`).  The field `deep` comes from the openness of the cubes
in `(F_v)ˣ` (library statement `NumberField.isOpen_range_powMonoidHom_units_adicCompletion`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace ArtinKP.A

variable {F : Type} [Field F] [NumberField F]

/-- Elements of `F` close to `1` at `v` are local cubes. -/
theorem exists_depth (v : HeightOneSpectrum (𝓞 F)) :
    ∃ N : ℕ, ∀ b : Fˣ, v.valuation F ((b : F) - 1) ≤ WithZero.exp (-(N : ℤ)) →
      C0Y.emb F v b ∈ (powMonoidHom 3 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range := by
  have hR : IsOpen (((powMonoidHom 3 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range :
      Set (v.adicCompletion F)ˣ)) :=
    NumberField.isOpen_range_powMonoidHom_units_adicCompletion v (by norm_num)
  have hV := (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).isOpenMap _ hR
  have h1 : (1 : v.adicCompletion F) ∈ Units.val ''
      ((powMonoidHom 3 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range :
        Set (v.adicCompletion F)ˣ) := ⟨1, one_mem _, rfl⟩
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp (hV.mem_nhds h1)
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding
    (γ : MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))))) with hg
  have hg0 : g ≠ 0 := (map_ne_zero _).mpr γ.ne_zero
  refine ⟨(1 - WithZero.log g).toNat, fun b hb => ?_⟩
  have hlt : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).restrict
      (algebraMap F (v.adicCompletion F) (b : F) - 1) < γ := by
    rw [Valuation.restrict_lt_iff_lt_embedding]
    have e : algebraMap F (v.adicCompletion F) (b : F) - 1
        = (((b : F) - 1 : F) : v.adicCompletion F) := by
      rw [← map_one (algebraMap F (v.adicCompletion F)), ← map_sub]; rfl
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    refine lt_of_le_of_lt hb ?_
    rw [← hg]
    calc WithZero.exp (-(((1 - WithZero.log g).toNat : ℕ) : ℤ))
        < WithZero.exp (WithZero.log g) := by rw [WithZero.exp_lt_exp]; omega
      _ = g := WithZero.exp_log hg0
  obtain ⟨u, hu, hub⟩ := hγ hlt
  have : u = C0Y.emb F v b := Units.ext hub
  rw [← this]
  exact hu

/-- The global package from the local-symbol package of C0Y. -/
def ofSymbolPkg (P₀ : C0Y.SymbolPkg F 3) : CubicPkg F where
  hv := P₀.hv
  steinberg v a := P₀.steinberg v a
  prod_eq_one a b T h := P₀.prod_eq_one a b T h
  unit_unit v h3 a b ha hb := P₀.unit_unit v (by simpa using h3) a b ha hb
  tame v h3 a π ω ha hπ hω hc := P₀.tame v (by simpa using h3) a π ω ha hπ hω hc
  deep v := by
    obtain ⟨N, hN⟩ := exists_depth v
    exact ⟨N, fun a b hb => P₀.h_of_mem_range v a (hN b hb)⟩

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.A_Transport
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S.brk_neg_left _root_.ArtinKP.S.brk_neg_right _root_.ArtinKP.S.brk_one_left _root_.ArtinKP.S.brk_one_right _root_.ArtinKP.S.brk_pow_three_left _root_.ArtinKP.S.brk_pow_three_right _root_.ArtinKP.S.brk_self _root_.ArtinKP.S.brk_zero_left _root_.ArtinKP.S.brk_zero_right _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-A: transport of the cubic package along a field isomorphism; existence in every universe

`CubicPkg.transport e P'` moves a package along `e : F ≃+* F'`.  With
`F ≃+* CyclotomicField n ℚ` this gives `nonempty_cubicPkg_cyclotomic` for `F : Type*`
(the library's Artin map, hence `C0Z.pkgHyp`, only exists for `F : Type`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

/-- The place of `F'` corresponding to `v` under `e`. -/
def placeMap (e : F ≃+* F') : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F') :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)

theorem placeMap_asIdeal (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) :
    (placeMap e v).asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv e) :=
  Ideal.comap_symm (RingOfIntegers.mapRingEquiv e)

theorem mem_placeMap_iff (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (n : ℕ) :
    RingOfIntegers.mapRingEquiv e a ∈ (placeMap e v).asIdeal ^ n ↔ a ∈ v.asIdeal ^ n := by
  rw [placeMap_asIdeal, ← Ideal.map_pow, C0R.mem_map_equiv, RingEquiv.symm_apply_apply]

theorem intValuation_placeMap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    (placeMap e v).intValuation (RingOfIntegers.mapRingEquiv e a) = v.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  have ha' : RingOfIntegers.mapRingEquiv e a ≠ 0 := by
    simpa using ha
  have key : ∀ n : ℕ, (placeMap e v).intValuation (RingOfIntegers.mapRingEquiv e a)
      ≤ WithZero.exp (-(n : ℤ)) ↔ v.intValuation a ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      mem_placeMap_iff]
  have h1 := (placeMap e v).intValuation_if_neg ha'
  have h2 := v.intValuation_if_neg ha
  set k := (Associates.mk (placeMap e v).asIdeal).count
    (Associates.mk (Ideal.span {RingOfIntegers.mapRingEquiv e a})).factors
  set m := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors
  have k1 := (key k).mp (by rw [h1])
  have k2 := (key m).mpr (by rw [h2])
  rw [h2, WithZero.exp_le_exp] at k1
  rw [h1, WithZero.exp_le_exp] at k2
  rw [h1, h2]
  congr 1
  omega

theorem valuation_placeMap (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    (placeMap e v).valuation F' (e x) = v.valuation F x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have ea : e (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F') F' (RingOfIntegers.mapRingEquiv e a) :=
    rfl
  have eb : e (algebraMap (𝓞 F) F b) = algebraMap (𝓞 F') F' (RingOfIntegers.mapRingEquiv e b) :=
    rfl
  rw [map_div₀, ea, eb, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_placeMap, intValuation_placeMap]

theorem three_mem_placeMap_iff (e : F ≃+* F') (v : HeightOneSpectrum (𝓞 F)) :
    (3 : 𝓞 F') ∈ (placeMap e v).asIdeal ↔ (3 : 𝓞 F) ∈ v.asIdeal := by
  have := mem_placeMap_iff e v 3 1
  rw [map_ofNat, pow_one, pow_one] at this
  exact this

/-- Cube roots of unity of `F'` pulled back to `F`. -/
def rootBack (e : F ≃+* F') : rootsOfUnity 3 F' →* rootsOfUnity 3 F :=
  restrictRootsOfUnity (e.symm : F' →* F) 3

theorem rootBack_coe (e : F ≃+* F') (z : rootsOfUnity 3 F') :
    ((rootBack e z : Fˣ) : F) = e.symm ((z : F'ˣ) : F') := rfl

theorem rootBack_eq_one_iff (e : F ≃+* F') (z : rootsOfUnity 3 F') : rootBack e z = 1 ↔ z = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun w : rootsOfUnity 3 F => ((w : Fˣ) : F)) h
    simp only [rootBack_coe, OneMemClass.coe_one, Units.val_one] at h'
    apply Subtype.ext
    apply Units.ext
    have := congrArg e h'
    simpa using this
  · rintro rfl
    exact map_one _

/-- Transport of a cubic package along a field isomorphism. -/
def CubicPkg.transport (e : F ≃+* F') (P' : CubicPkg F') : CubicPkg F where
  hv v :=
    { toFun := fun a => (rootBack e).comp
        ((P'.hv (placeMap e v) (Units.map (e : F →* F') a)).comp (Units.map (e : F →* F')))
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  steinberg v a := by
    have h : Units.map (e : F →* F') (-a) = -Units.map (e : F →* F') a := by
      ext; simp
    simp [h, P'.steinberg]
  prod_eq_one a b T hT := by
    classical
    have h1 : ∏ v ∈ T, (rootBack e) (P'.hv (placeMap e v) (Units.map (e : F →* F') a)
        (Units.map (e : F →* F') b)) = 1 := by
      rw [← map_prod, rootBack_eq_one_iff]
      have h2 := P'.prod_eq_one (Units.map (e : F →* F') a) (Units.map (e : F →* F') b)
        (T.map (placeMap e).toEmbedding) (by
          intro v' hv'
          obtain ⟨v, rfl⟩ := (placeMap e).surjective v'
          have hv : v ∉ T := by
            intro h
            exact hv' (Finset.mem_map_of_mem _ h)
          have := hT v hv
          exact (rootBack_eq_one_iff e _).mp this)
      rwa [Finset.prod_map] at h2
    exact h1
  unit_unit v h3 a b ha hb := by
    have h3' : (3 : 𝓞 F') ∉ (placeMap e v).asIdeal := fun h => h3 ((three_mem_placeMap_iff e v).mp h)
    have := P'.unit_unit (placeMap e v) h3' (Units.map (e : F →* F') a)
      (Units.map (e : F →* F') b) (by simpa [valuation_placeMap] using ha)
      (by simpa [valuation_placeMap] using hb)
    simp [this]
  tame v h3 a π ω ha hπ hω hc := by
    have h3' : (3 : 𝓞 F') ∉ (placeMap e v).asIdeal := fun h => h3 ((three_mem_placeMap_iff e v).mp h)
    have hN : Ideal.absNorm (placeMap e v).asIdeal = Ideal.absNorm v.asIdeal := by
      rw [placeMap_asIdeal]; exact C0R.absNorm_map_equiv e v.asIdeal
    have := P'.tame (placeMap e v) h3' (Units.map (e : F →* F') a) (Units.map (e : F →* F') π)
      (e ω) (by simpa [valuation_placeMap] using ha) (by simpa [valuation_placeMap] using hπ)
      (by rw [← map_pow, hω, map_one]) (by
        rw [hN]
        have h' : ((Units.map (e : F →* F') a : F'ˣ) : F') ^ ((Ideal.absNorm v.asIdeal - 1) / 3)
            - e ω = e ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 3) - ω) := by simp
        rw [h', valuation_placeMap]
        exact hc)
    show ((rootBack e _ : Fˣ) : F) = ω
    rw [rootBack_coe, MonoidHom.comp_apply, this, RingEquiv.symm_apply_apply]
  deep v := by
    obtain ⟨N, hN⟩ := P'.deep (placeMap e v)
    refine ⟨N, fun a b hb => ?_⟩
    have := hN (Units.map (e : F →* F') a) (Units.map (e : F →* F') b) (by
      have h' : ((Units.map (e : F →* F') b : F'ˣ) : F') - 1 = e ((b : F) - 1) := by simp
      rw [h', valuation_placeMap]
      exact hb)
    simp [this]

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.X_Quot
/-! # WP-X, file 5: quotient measures and unfolding without fundamental domains

Abstract setting: a countable group `G` acting measurably on `(α, μ)` and preserving `μ`.
A *partition of unity* for the action is a measurable `η : α → ℝ≥0∞` with
`∑_g η (g • a) = 1` for all `a` (the indicator of a strict fundamental domain is one; in a
properly discontinuous situation an everywhere positive one always exists, `exists_isPOU`).
The quotient measure on `G \ α` is the push-forward of `η μ`; it does not depend on `η`
(`quotMeasure_eq`).  Everything is Tonelli:

* `lintegral_tsum_swap` : `∫ φ · Σ_g ψ∘g = ∫ ψ · Σ_g φ∘g`;
* `lintegral_mul_pou_eq` : independence of `η`;
* `lintegral_autom_mul_eq` : unfolding `∫_{G\α} (Σ_{H\G} f∘γ) u = ∫_{H\α} f u`;
* `setLIntegral_le_mul_lintegral_pou` : a set meeting each orbit at most `m` times has
  `∫_B f ≤ m ∫_{G\α} f`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

/-! ### The quotient measure -/

/-! ### Unfolding -/

/-- `(q, h) ↦ q.out * h` is a bijection `(G ⧸ H) × H ≃ G`. -/
def quotProdEquiv (H : Subgroup G) : (G ⧸ H) × H ≃ G :=
  Equiv.ofBijective (fun p => p.1.out * (p.2 : G)) (by
    constructor
    · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
      simp only at heq
      have hq : q = q' := by
        have := congrArg (QuotientGroup.mk (s := H)) heq
        rwa [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.mk_mul_of_mem _ h'.2,
          QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      subst hq
      have : (h : G) = h' := mul_left_cancel heq
      rw [Subtype.ext this]
    · intro g
      have hmem : (QuotientGroup.mk (s := H) g).out⁻¹ * g ∈ H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      exact ⟨(QuotientGroup.mk g, ⟨_, hmem⟩), by simp⟩)

/-- The sum of `f` over `H \ G`: `Σ_{γ ∈ H\G} f (γ • a)`, with the representatives
`γ = q.out⁻¹`, `q ∈ G ⧸ H`. For `H`-invariant `f` any representatives give the same value
(`autom_term_eq`). -/
def autom (H : Subgroup G) (f : α → ℝ≥0∞) (a : α) : ℝ≥0∞ :=
  ∑' q : G ⧸ H, f (q.out⁻¹ • a)

/-- The restriction of a partition of unity for `G` to a subgroup `H`. -/
def pouRestrict (H : Subgroup G) (η : α → ℝ≥0∞) (a : α) : ℝ≥0∞ :=
  ∑' q : G ⧸ H, η (q.out • a)

/-! ### Multiplicity and existence of partitions of unity -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Meas
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteXVol
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

/-! ### Generators -/

instance instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatComplexH3Vol : SMulInvariantMeasure (SL(2, ℂ)) H3 H3.vol :=
  ⟨fun g s hs => by
    have h := vol_map_smul g
    conv_rhs => rw [← h]
    rw [Measure.map_apply (measurable_const_smul g) hs]⟩

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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

/-! ### Topology and measure -/

instance instSMulInvariantMeasureGinfXVol : SMulInvariantMeasure (Ginf F) (X F) (X.vol F) :=
  ⟨fun g s hs => (measurePreserving_Ginf_smul g).measure_preimage hs.nullMeasurableSet⟩

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Pairs
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

/-! ### The raw right action of `SL₂(𝓞_F)` on pairs -/

/-! ### Primitive pairs and pair classes -/

namespace PairClass

instance instNonempty : Nonempty (PairClass S) := ⟨inf S⟩

end PairClass

/-! ### (B1) for families of `S`-integer pairs -/

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B7_Gauss
/-! # B7_Gauss: the cubic Gauss sum `g(ν, c)` over a ring of `S`-integers, abstractly

`R` is a domain with fraction-type field `K` (in the application `R = SInt 𝔪`, `K = F`).

* `CubicSymbol R` is the interface to WP-A: the cubic exterior symbol `(d/c)`, with exactly the
  properties used here.
* `AddData R K` is an additive character of `K` trivial on `R` (in the application `sAddChar 𝔪`,
  see `B7_Link`).
* `gauss S A ν c = ∑_{d mod c} (d/c)⁻¹ e(ν d / c)` (terms with `(d, c) ≠ 1` vanish since
  `(d/c) = 0` there and `0⁻¹ = 0`).

Main results (MATH.md (B7)): `gauss_mul` (twisted multiplicativity), `gauss_mul_left`
(`g(μν, c) = (μ/c) g(ν, c)`), the prime-power table `gauss_prime_pow_le`,
`gauss_prime_pow_succ`, `gauss_prime_pow_eq_zero`, and the constant-term sums `csum_eq_phi`,
`csum_eq_zero`, `csum_of_cube`, `csum_eq_zero_of_val`, `csum_prime_pow`, `phi_prime_pow`.
-/

set_option linter.unusedSectionVars false

namespace ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### The additive character on fractions -/

/-! ### Elementary facts about the symbol -/

/-! ### The Gauss sum -/

variable (S : CubicSymbol R) (A : AddData R K)

/-- The constant-term sum `∑_{d mod c} (d/c)⁻¹`. -/
noncomputable def csum (c : R) : ℂ :=
  rsum c (fun d => (S.sym d c)⁻¹)

open Classical in
/-- `φ_R(c)`: the number of residues modulo `c` prime to `c`. -/
noncomputable def phi (c : R) : ℂ :=
  rsum c (fun d => if IsCoprime d c then 1 else 0)

/-! ### Constant-term sums -/

/-! ### Prime powers -/

section prime

variable {π : R} (hπ : π ≠ 0) (hmax : (Ideal.span {π}).IsMaximal)
  (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

/-- The normalized prime Gauss sums `g_j(π) = ∑_{d mod π} (d/π)^{-j} e(d/π)`. -/
noncomputable def gaussP (π : R) (j : ℕ) : ℂ :=
  rsum π (fun d => (S.sym d π)⁻¹ ^ j * A.ψ d π)

end prime

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B7_System
/-! # B7_System: the formal three-term linear system of MATH.md §4.1 and its solution (§4.3)

Everything here is polynomial algebra in formal quantities `q`, `G`, `G'`, `x`, `Ψ 0`, `Ψ 1`, `Ψ 2`.

* `tab q G G' k j` is the prime-power table of the Gauss sum `g(ν₀ π^k, π^j)` (`B7_Gauss`:
  `gauss_prime_pow_le`, `csum_prime_pow`, `phi_prime_pow`, `gauss_prime_pow_succ`,
  `gaussP_of_three_dvd`, `gauss_prime_pow_eq_zero`), with `G = g(ν₀, π) = (ν₀/π) g₁(π)` and
  `G' = (ν₀/π)² g₂(π)`.
* `Cform q G G' x Ψ k = ∑_{j ≤ k+1} tab k j · x^j · Ψ_{(k+j) mod 3}` is (4.1).
* `Cform_zero` … `Cform_five` are the closed forms listed in MATH §4.1 (all correct as printed).
* `Cform_add_three`: the general recursion `C_{k+3} = q³x³ C_k + (1 - q²x³) Ψ_{k mod 3}`.
* `solve`: at a point with `q⁴x³ = 1` (the theta point `x₀ = q^{-4/3}`), `C₃ = C₀` and `C₅ = C₂`
  force `Ψ₂ = 0`, `q·G·x·Ψ₁ = Ψ₀`, `q·C₀ = (q+1)Ψ₀` and `C₁ = q²x²·G'·C₀`.
* `periodic_of_solution`: conversely these relations give `q·C_k = (q+1)Ψ_{k mod 3}` and
  `C_{k+3} = C_k` for all `k` (so `C₄ = C₁` is automatic).
* `ratio_rpow`: over `ℂ` with `x₀ = q^{-4/3}`: `C₁ = q^{-2/3} · G' · C₀`.
-/

namespace ArtinKP.B7

section table

variable {A : Type*} [CommRing A]

/-- The prime-power table `g(ν₀ π^k, π^j)` as a formal expression. -/
def tab (q G G' : A) (k j : ℕ) : A :=
  if j ≤ k then (if 3 ∣ j then (if j = 0 then 1 else q ^ j - q ^ (j - 1)) else 0)
  else if j = k + 1 then q ^ k * (if j % 3 = 1 then G else if j % 3 = 2 then G' else -1)
  else 0

/-- The formal coefficient `C_k = ∑_{j=0}^{k+1} g(ν₀π^k, π^j) x^j Ψ_{k+j}` of (4.1). -/
def Cform (q G G' x : A) (Ψ : ℕ → A) (k : ℕ) : A :=
  ∑ j ∈ Finset.range (k + 2), tab q G G' k j * x ^ j * Ψ ((k + j) % 3)

end table

end ArtinKP.B7
end

section
-- module Solutions.Artin.T12.C3B_Norm
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

lemma sAddChar_congr {𝔪 : Ideal (𝓞 F)} (x x' : F)
    (H : ∀ y : F, (x - y ∈ (placesOf 𝔪).integer F) ↔ (x' - y ∈ (placesOf 𝔪).integer F)) :
    sAddChar 𝔪 x = sAddChar 𝔪 x' := by
  classical
  let G : (F → Prop) → ℂ := fun p => if h : ∃ y, p y then
    Complex.exp (-(2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F h.choose : ℚ) : ℂ)) else 0
  have e1 : sAddChar 𝔪 x = G (fun y => x - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  have e2 : sAddChar 𝔪 x' = G (fun y => x' - y ∈ (placesOf 𝔪).integer F ∧
      ∀ v ∈ placesOf 𝔪, v.valuation F y ≤ 1) := by
    unfold sAddChar; rfl
  rw [e1, e2]
  congr 1
  funext y
  exact propext (and_congr_left' (H y))

/-- `e` is invariant under translation by `R`. -/
lemma sAddChar_add_mem {𝔪 : Ideal (𝓞 F)} (x r : F) (hr : r ∈ (placesOf 𝔪).integer F) :
    sAddChar 𝔪 (x + r) = sAddChar 𝔪 x := by
  have key : ∀ y : F, (x + r - y ∈ (placesOf 𝔪).integer F) ↔ (x - y ∈ (placesOf 𝔪).integer F) := by
    intro y
    constructor
    · intro h
      have := sub_mem h hr
      rwa [show x + r - y - r = x - y by ring] at this
    · intro h
      have := add_mem h hr
      rwa [show x - y + r = x + r - y by ring] at this
  exact sAddChar_congr _ _ key

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3B_Unit
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- The primes at which the sextic symbol behaves: exterior primes with `6 ∣ N P − 1`. -/
def GoodP (𝔪 P : Ideal (𝓞 F)) : Prop :=
  P.IsPrime ∧ P ≠ ⊥ ∧ ¬ 𝔪 ≤ P ∧ 6 ∣ Ideal.absNorm P - 1

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

lemma mem_map_iff (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪) :
    x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪)) ↔ ∃ r : SInt 𝔪, x = g.gen I * r := by
  rw [← g.span_gen I hI, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [← hr, mul_comm]⟩
  · rintro ⟨r, hr⟩; exact ⟨r, by rw [hr, mul_comm]⟩

lemma div_gen_mem (g : AllowedGen ι 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) (x : SInt 𝔪)
    (hx : x ∈ I.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    (x : F) / (g.gen I : F) ∈ (placesOf 𝔪).integer F := by
  obtain ⟨r, rfl⟩ := (mem_map_iff g I hI x).mp hx
  have h0 := gen_ne_zero g I hI
  rw [Subalgebra.coe_mul, mul_div_cancel_left₀ _ h0]
  exact r.2

end gen

end C3B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Add
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-- `a / gen 𝔞` has a witness. -/
lemma hasWit_div_gen (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a : SInt 𝔪) : HasWit 𝔪 ((a : F) / (g.gen 𝔞 : F)) := by
  apply hasWit_of_mul_mem _ 𝔞 h𝔞.2
  intro i hi
  have hm : algebraMap (𝓞 F) (SInt 𝔪) i ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    Ideal.mem_map_of_mem _ hi
  have := C3B.div_gen_mem g 𝔞 h𝔞 _ hm
  rw [coe_alg] at this
  rw [show (a : F) / (g.gen 𝔞 : F) * algebraMap (𝓞 F) F i =
    (a : F) * (algebraMap (𝓞 F) F i / (g.gen 𝔞 : F)) by ring]
  exact mul_mem a.2 this

/-- `e(a/c + b/c) = e(a/c) e(b/c)` for `c` an allowed generator. -/
lemma sAddChar_div_gen_add (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    (a b : SInt 𝔪) :
    sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F) + (b : F) / (g.gen 𝔞 : F)) =
      sAddChar 𝔪 ((a : F) / (g.gen 𝔞 : F)) * sAddChar 𝔪 ((b : F) / (g.gen 𝔞 : F)) :=
  sAddChar_add (hasWit_div_gen g 𝔞 h𝔞 a) (hasWit_div_gen g 𝔞 h𝔞 b)

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Gauss
/-! # C3I_Gauss: the additive character, Gauss sums and Davenport–Hasse on `L = R / P R`

* `psi g h : AddChar L ℂ`, `psi_mk : psi (mk x) = e(x / gen P)`, `psi_isPrimitive`.
* `card_sqrt`: `#{u | u² = w} = 1 + χ³(w)`; `jacobi_dh`: `χ(4) J(χ, χ) = J(χ³, χ)`.
* Gauss sums `g_j = gaussSum (χ^j) ψ`: `gs_mul_gs_inv`, `gs_three_sq`, `star_gs`, `dh`:
  `χ(4) g₁ g₃ = g₂²`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

/-- `e(x / gen 𝔞)` depends only on `x mod 𝔞 R`. -/
lemma sAddChar_div_congr (g : AllowedGen ι 𝔪) (𝔞 : Ideal (𝓞 F)) (h𝔞 : IsExterior 𝔪 𝔞)
    {x x' : SInt 𝔪} (hx : x - x' ∈ 𝔞.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    sAddChar 𝔪 ((x : F) / (g.gen 𝔞 : F)) = sAddChar 𝔪 ((x' : F) / (g.gen 𝔞 : F)) := by
  have : (x : F) / (g.gen 𝔞 : F) =
      (x' : F) / (g.gen 𝔞 : F) + ((x - x' : SInt 𝔪) : F) / (g.gen 𝔞 : F) := by
    rw [Subalgebra.coe_sub]; ring
  rw [this, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g 𝔞 h𝔞 _ hx)]

/-- The additive character `y ↦ e(y / gen P)` of `L`. -/
noncomputable def psi (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) :
    AddChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun y := sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F))
  map_zero_eq_one' := by
    have h0 : quotLift (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mk_quotLift]
    exact C3B.sAddChar_of_mem _ (C3B.div_gen_mem g _ h.ext _ h0)
  map_add_eq_mul' := by
    intro a b
    have hab : quotLift (a + b) - (quotLift a + quotLift b) ∈
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
      rw [← Ideal.Quotient.eq, map_add, mk_quotLift, mk_quotLift, mk_quotLift]
    rw [sAddChar_div_congr g _ h.ext hab, Subalgebra.coe_add, add_div,
      sAddChar_div_gen_add g _ h.ext]

/-! ### Characters on the finite field `L` -/

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Defs
/-! # L3V_Defs: local symbols at an exterior prime, on elements of `F`

Internal definitions; the cut `L3V_CutKP` inlines them as `let`s (no new bundle):
* `localSymbol ι 𝔪 P t`: `χ_P(t)` for a `P`-unit `t ∈ F` (as `χ_P(y) conj χ_P(z)` for any
  `t = y / z` with `y, z ∈ R` prime to `P`), and `0` if `t` is not a `P`-unit;
* `localAddChar g P w`: `ψ_P(w / p)` for a `P`-integral `w ∈ F`, `p = gen P`, i.e. `e(−y / p)` for
  any `y ∈ R` with `y ≡ w (mod P)`.
-/

namespace ArtinPrimitiveRoots

namespace L3V

open NumberField

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The sextic residue symbol `χ_P(t)` of a `P`-unit `t ∈ F`: `χ_P(y) · conj χ_P(z)` for a
representation `z t = y` with `y, z ∈ R` and `z ∉ P R` (a choice; the value does not depend on it);
`0` if there is none, and `0` (through `χ_P(y) = 0`) when `t ∈ P`. -/
noncomputable def localSymbol (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F)) (t : F) : ℂ :=
  if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      (yz.2 : F) * t = (yz.1 : F) then
    sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
  else 0

open Classical in
/-- The local additive character `ψ_P(w / p)` of the standard character at the exterior prime `P`,
for `P`-integral `w ∈ F`, with `p` the allowed generator of `P`: `e(−y / p)` for some `y ∈ R` with
`z (w − y) ∈ P R` for some `z ∈ R ∖ P R` (a choice; `0` if there is none). By the product formula
`ψ_P(y / p) = conj e(y / p) = e(−y / p)` for `y ∈ R`. -/
noncomputable def localAddChar {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪)
    (P : Ideal (𝓞 F)) (w : F) : ℂ :=
  if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
      (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
    sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
  else 0

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Base
/-! # L3V_Base: the local data of `L3V_CutKP` as top-level definitions, and the cut's data

* `Wv`, `Wsph`, `tau`, `mask`, `Wweyl`, `Eloc`: the `let`s of `L3V_CutKP`; `Rsum`: the nonzero-digit
  part of `Eloc`.
* `Data χ g`: the objects the cut provides for one `(𝔪, χ, g)`; `data_of_cut`.
-/

namespace ArtinPrimitiveRoots

namespace L3V

open NumberField UniqueFactorizationMonoid

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- `W_P(a(p^e))` of (5.4). -/
noncomputable def Wv (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e : ℕ) : ℂ :=
  if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
  else if e % 3 = 1 then
    (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
  else 0

/-- `W_P(a(p^{e₀} t))`. -/
noncomputable def Wsph (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e₀ : ℤ) (t : F) : ℂ :=
  if e₀ < 0 then 0 else localSymbol ι 𝔪 P t ^ (2 * e₀.toNat) * Wv g P e₀.toNat

/-- `τ_{P,j}`. -/
noncomputable def tau (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ) : ℂ :=
  ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
    starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
      sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))

open Classical in
/-- The mask `α_{P,j}` of (6.4). -/
noncomputable def mask (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ)
    (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ :=
  if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
  else (tau g P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j

/-- The per-digit Weyl value `W_P(a(p^{e−2} t) w n(v/p))`, `e = e₀ + 2`. -/
noncomputable def Wweyl (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (e₀ : ℤ) (t : F)
    (v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ :=
  if e₀ + 2 < 0 then 0 else
    Wv g P (e₀ + 2).toNat * localSymbol ι 𝔪 P t ^ (4 + 2 * (e₀ + 2).toNat) *
      sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
      localAddChar g P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))

open Classical in
/-- The exterior local factor `E_P`. -/
noncomputable def Eloc (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (k : ℕ) (e₀ : ℤ) (t : F) : ℂ :=
  if k = 0 then Wsph g P e₀ t else
    ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
      mask g P (k % 6) v * (if v = 0 then Wsph g P e₀ t else Wweyl g P e₀ t v)

open Classical in
/-- The nonzero-digit part of `E_P`. -/
noncomputable def Rsum (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (j : ℕ) (e₀ : ℤ) (t : F) : ℂ :=
  ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
    mask g P j v * (if v = 0 then 0 else Wweyl g P e₀ t v)

/-- The monomial exponent `b(j, e)` of (6.15). -/
def bexp (j e : ℕ) : ℕ := if e = 0 then 8 + 5 * j else 4 + 2 * e

/-- `ν = x / b²` for the frequency class `z` and row `r`. -/
noncomputable def nu (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) : F :=
  (rowElt g z : F) / (g.gen r.1.1 : F) ^ 2

/-- `v_P(ν)`. -/
noncomputable def e0 (r z : RowClass 𝔪) (P : Ideal (𝓞 F)) : ℤ :=
  ((normalizedFactors z.1.1).count P : ℤ) - 2 * ((normalizedFactors r.1.1).count P : ℤ)

/-- The exterior product `∏_P E_P(ν)`. -/
noncomputable def Eprod (g : AllowedGen ι 𝔪) (r z : RowClass 𝔪) : ℂ :=
  ∏ P ∈ (normalizedFactors (z.1.1 * r.1.1)).toFinset,
    Eloc g P ((normalizedFactors r.1.1).count P) (e0 r z P)
      (nu g r z * (g.gen P : F) ^ (-(e0 r z P)))

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_Res
/-! # L3V_Res: the residue map `O_P → R / P R` on `F`, and the local symbols

For a height-one prime `v ∉ S`:
* `L3V.res 𝔪 v w ∈ R / v R` for `v(w) ≤ 1` (`0` otherwise); `res_eq`: `res w = [y]` whenever
  `v(w − y) ≤ exp(−1)`; `res` is additive and multiplicative on `O_v`, `res y = [y]` on `R`,
  `res w = 0 ↔ v(w) < 1`.
* `localSymbol_eq`: `localSymbol ι 𝔪 P t = χ(res t)` (all `t`, `Good`);
* `localAddChar_eq`: `localAddChar g P w = ψ(−res w)` for `v(w) ≤ 1`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

open Classical in
/-- The residue of a `v`-integral element of `F` in `R / v R` (`0` if not `v`-integral). -/
noncomputable def res (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (w : F) :
    SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  if h : v.valuation F w ≤ 1 then
    Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) (C3I.exists_val_sub_le (v := v) 1 w h).choose)
  else 0

/-! ### The local symbols -/

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.S_Twisted
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S.GSection.twist_apply
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

/-! ### `Ψ ↦ Ψ · 1[P ∤ c]` for an exterior prime -/

theorem InI.val_lt_one {v : HeightOneSpectrum (𝓞 F)} {x : F} (h : InI v.asIdeal x) :
    v.valuation F x < 1 := by
  obtain ⟨y, hy, rfl⟩ := h
  exact (v.valuation_lt_one_iff_mem (K := F) y).mpr hy

/-- `P ∤ c` is invariant under `Γ(P)`. -/
theorem val_act_c_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    {γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)} (hγ : γ ∈ Gamma 𝔪 v.asIdeal) (p : Row 𝔪) :
    v.valuation F ((p.act γ).c : F) = 1 ↔ v.valuation F (p.c : F) = 1 := by
  have hγ' := (mem_Gamma_iff' γ).mp hγ
  have ha : v.valuation F ((γ.1 0 0 : SInt 𝔪) : F) = 1 := by
    have h := InI.val_lt_one (hγ' 0 0)
    rw [if_pos rfl] at h
    have := Valuation.map_one_add_of_lt (v := v.valuation F) h
    rwa [add_sub_cancel] at this
  have hc : v.valuation F ((γ.1 1 0 : SInt 𝔪) : F) < 1 := by
    have h := InI.val_lt_one (hγ' 1 0)
    rwa [if_neg (by decide), sub_zero] at h
  have hd : v.valuation F ((p.d : F) * ((γ.1 1 0 : SInt 𝔪) : F)) < 1 := by
    rw [map_mul, mul_comm]
    exact mul_lt_one_of_lt_of_le hc (sInt_val_le_one p.d v hv)
  have e : ((p.act γ).c : F) = (p.c : F) * ((γ.1 0 0 : SInt 𝔪) : F)
      + (p.d : F) * ((γ.1 1 0 : SInt 𝔪) : F) := by
    rw [Row.act_c]; push_cast; ring
  have hca : v.valuation F ((p.c : F) * ((γ.1 0 0 : SInt 𝔪) : F)) = v.valuation F (p.c : F) := by
    rw [map_mul, ha, mul_one]
  rw [e]
  constructor
  · intro h
    by_contra hne
    have hlt : v.valuation F (p.c : F) < 1 := lt_of_le_of_ne (sInt_val_le_one p.c v hv) hne
    have : v.valuation F ((p.c : F) * ((γ.1 0 0 : SInt 𝔪) : F)
        + (p.d : F) * ((γ.1 1 0 : SInt 𝔪) : F)) < 1 :=
      (v.valuation F).map_add_lt (by rw [hca]; exact hlt) hd
    rw [h] at this
    exact lt_irrefl _ this
  · intro h
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hca, h]; exact hd), hca, h]

namespace TSection

variable {ι : F →+* ℂ}

open Classical in
/-- **`Ψ ↦ Ψ·1[P ∤ c]`** for the exterior place `v = P` (MATH2 §5.2, `ρ_∞`).  It raises the level
from `𝔫` to `𝔫 P`. -/
def restrict (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (Ψ : TSection ι 𝔪) :
    TSection ι 𝔪 where
  toFun s p := if v.valuation F (p.c : F) = 1 then Ψ s p else 0
  hom s ε p := by
    have : v.valuation F ((ε • p).c : F) = v.valuation F (p.c : F) := by
      rw [Row.smul_c]; push_cast; rw [map_mul, unit_val_eq_one ε v hv, one_mul]
    rw [this]
    split_ifs
    · exact Ψ.hom s ε p
    · simp
  holo p := by
    by_cases h : v.valuation F (p.c : F) = 1
    · simp only [h, if_true]; exact Ψ.holo p
    · simp only [h, if_false]; exact differentiable_const 0
  bound M := by
    obtain ⟨B, hB⟩ := Ψ.bound M
    refine ⟨B, fun s hs p => ?_⟩
    split_ifs
    · exact hB s hs p
    · rw [norm_zero]; exact (norm_nonneg _).trans (hB s hs p)
  level := by
    obtain ⟨𝔫, h𝔫, h⟩ := Ψ.level
    refine ⟨𝔫 * v.asIdeal, ?_, fun γ hγ s p => ?_⟩
    · have hv0 := v.ne_bot
      rw [← Ideal.zero_eq_bot] at h𝔫 hv0 ⊢
      exact mul_ne_zero h𝔫 hv0
    · have h1 := Gamma_mono (Ideal.mul_le_left (I := 𝔫) (J := v.asIdeal)) hγ
      have h2 := Gamma_mono (Ideal.mul_le_right (I := 𝔫) (J := v.asIdeal)) hγ
      simp only [val_act_c_eq_one_iff v hv h2 p]
      split_ifs
      · exact h γ h1 s p
      · simp

end TSection

end ArtinKP.S
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

/-- The real K-Bessel function, `μ` real. -/
def besselKR (μ z : ℝ) : ℝ := (1 / 2) * ∫ t in Ioi (0 : ℝ), t ^ (μ - 1) * besselKer z t

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.S_Ops
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

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- **`Φ ↦ Φ♯`**, `Φ♯_s(c, d) = Φ_s(c, d/π³)` (MATH2 §5: `Φ^{(3)}`), as a genuine section:
it is `|π|^{6s} A(π³) Φ`. -/
def sharp (hG : Good 𝔪) (π : F) (hπ : π ≠ 0) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 :=
  smulFun (fun s => ((absS 𝔪 π : ℝ) : ℂ) ^ (6 * s))
    ((differentiable_id.const_mul (6 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (absS_pos hπ).ne')))
    (Φ.torus hG (π ^ 3) (pow_ne_zero 3 hπ))

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_BigCell
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
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

/-! ### Classes -/

/-! ### The support of a big-cell section and its stability -/

/-! ### Small-cell sections -/

/-! ### Finite sums: the sum over classes and additive projections -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

instance instAddCommMonoid : AddCommMonoid (GSection ι P 𝔪) where
  add_assoc a b c := by ext; simp [add_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  add_comm a b := by ext; simp [add_comm]
  nsmul := nsmulRec

/-- **Finite additive projection** `Σ_t ϕ(t) n(t)·Φ` (MATH §5.1 (G2)); a section because
sections form a module and `n(t)` preserves them. -/
def addProj (hG : Good 𝔪) (T : Finset F) (ϕ : F → ℂ) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 :=
  ∑ t ∈ T, ϕ t • Φ.nT hG t

end GSection

end ArtinKP.S
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

/-- Nonzero classes prime to `π`. -/
abbrev ClsP (π : R) : Type _ := {a : Associates R // a ≠ 0 ∧ ¬ Associates.mk π ∣ a}

/-- Invariance under units. -/
def UInv (f : R → ℂ) : Prop := ∀ u c : R, IsUnit u → c ≠ 0 → f (u * c) = f c

/-- `(j, c') ↦ π^j c'` on classes. -/
noncomputable def splitFun (π : R) (p : ℕ × ClsP π) : Associates R :=
  Associates.mk π ^ p.1 * p.2.1

lemma splitFun_ne_zero {π : R} (hπ : π ≠ 0) (p : ℕ × ClsP π) : splitFun π p ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by simpa using hπ)) p.2.2.1

/-! ### The norm `N(c) = #(R/cR)` -/

/-! ### Symbols -/

/-! ### Gauss sums: units and the splitting `c = π^j c'` -/

/-! ### The interface -/

namespace Kubota

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

/-- Sections with proportional `Lam` (on `Re s > 2`). -/
def LEq (Φ Ψ : Sec) (z : ℂ) : Prop :=
  ∀ (c ν : R) (s : ℂ), c ≠ 0 → 2 < s.re → D.Lam Φ c ν s = z * D.Lam Ψ c ν s

end Kubota

/-! ### The prime datum and the splitting (4.1′) -/

/-- What is needed of a prime element `π`: B7's hypotheses and table.  In the application
`π = g.gen P`, `g1 = tau P 2`, `g2 = tau P 4` (`B7.gauss_gen_table`). -/
structure PrimeDatum (S : CubicSymbol R) (A : AddData R K) (π : R) (g1 g2 : ℂ) : Prop where
  ne_zero : π ≠ 0
  isMax : (Ideal.span {π}).IsMaximal
  mult : ∀ c : R, c ≠ 0 → ∃ n : ℕ, ¬ π ^ (n + 1) ∣ c
  one_lt : 1 < Nat.card (R ⧸ Ideal.span {π})
  table : ∀ ν₀ : R, ¬ π ∣ ν₀ → ∀ k j : ℕ,
    gauss S A (ν₀ * π ^ k) (π ^ j) =
      tab (nrm π) (S.sym ν₀ π * g1) (S.sym ν₀ π ^ 2 * g2) k j

namespace Kubota

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

/-- The twist `((π/c')(c'/π))^{-m}`. -/
noncomputable def wt (S : CubicSymbol R) (π : R) (m : ℕ) (c : R) : ℂ :=
  ((S.sym π c * S.sym c π)⁻¹) ^ m

/-- Summand of `Y_m`. -/
noncomputable def Yterm (π : R) (Ψ : Sec) (ν₀ : R) (m : ℕ) (s : ℂ) (c : R) : ℂ :=
  gauss S A ν₀ c * wt S π m c * D.Lam Ψ (π ^ m * c) ν₀ s * nrm c ^ (-s)

/-- **The `π`-coprime twisted series**
`Y_m(Ψ; ν₀, s) = ∑_{c' ∈ (R∖0)/U, π ∤ c'} g(ν₀,c') ((π/c')(c'/π))^{-m} Lam Ψ (π^m c') ν₀ s N(c')^{-s}`
(the unknowns `Ψ_m` of the linear system). -/
noncomputable def Y (π : R) (Ψ : Sec) (ν₀ : R) (m : ℕ) (s : ℂ) : ℂ :=
  ∑' b : ClsP π, D.Yterm π Ψ ν₀ m s (rp b.1)

end Kubota

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.E_Residue
/-! # E_Residue: passage to residues and the solution of the system at one prime

* `ResFun s₀`: the abstract **residue functional** — a relation `HasRes f r` ("`f`, given on
  `Re s > 2`, has residue `r` at `s₀`") with exactly the properties (R3)/(R5) of MATH §3.0:
  it depends only on `f` on `Re s > 2`, is additive, is compatible with multiplication by entire
  functions, and the residue is unique.  (`E_Model` shows that the intended definition —
  holomorphic continuation to a connected open set followed by a limit along a ray — has these
  properties.)
* `Theta D s₀`: a residue functional together with the residues `tau Φ ν` of the coefficient
  series `D.aSer Φ ν`.
* `PER T π`: cube periodicity in the exact form of MATH2 §4.4, `τ_Φ(νπ³) = τ_{Ã(π)³Φ}(ν)`.
* Given `PER T π` and `q⁴ x₀³ = 1` (`x₀ = q^{-s₀}`, i.e. `s₀ = 4/3`), for `π ∤ ν₀`:
  `tau_mul_prime` (E1): `τ_Φ(ν₀π) = q² x₀² (ν₀/π)² g₂ · τ_{Ã(π)Φ}(ν₀)`,
  `tau_mul_prime_sq` (E2): `τ_Φ(ν₀π²) = 0`,
  `tau_mul_prime_pow`: `τ_Φ(ν₀π^e) = w(e) (ν₀/π)^{2e} τ_{Ã(π)^eΦ}(ν₀)`, `w = 1, q²x₀²g₂, 0`.
  No division by the determinant is needed and the `Y_m` need no residues: the unknowns are
  eliminated among `C₀, C₁, C₃, C₄` (resp. `C₂, C₅`) by polynomial multipliers.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

namespace Theta

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} {D : Kubota S A Sec} {s₀ : ℂ}
  (T : Theta D s₀) (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

/-- **Cube periodicity at `π`**, in the exact form of MATH2 §4.4 (PER)/(E3):
`τ_Φ(νπ³) = τ_{Ã(π)³Φ}(ν)` for every section and every `ν ≠ 0`. -/
def PER (π : R) : Prop :=
  ∀ (Φ : Sec) (ν : R), ν ≠ 0 → T.tau Φ (ν * π ^ 3) = T.tau ((D.act π)^[3] Φ) ν

section prime

variable {π : R} {g1 g2 : ℂ} (P : PrimeDatum S A π g1 g2)

/-- The local weight `w(e) = 1, q² x₀² g₂, 0` for `e ≡ 0, 1, 2 (mod 3)`; with `s₀ = 4/3` and
`g₂ = √q γ₂(P)` it is `q^{e/3} · Wv P e` of the frozen statement. -/
noncomputable def wloc (q x₀ g2 : ℂ) (e : ℕ) : ℂ :=
  if e % 3 = 0 then 1 else if e % 3 = 1 then q ^ 2 * x₀ ^ 2 * g2 else 0

end prime

end Theta

end ArtinKP.E
end

section
-- module Solutions.Artin.T12.C3I_Cut
/-! # C3I_Cut: the cutoff — exterior primes of `ℚ(μ_n)`, `12 ∣ n`, are good

`N₀ = max(3^[F:ℚ], N 𝔇)`: an exterior prime has norm `> N₀`, so it lies over neither `2` nor `3`
(`12 ∣ N P − 1`) and does not divide the different. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F]

/-- The cutoff. -/
noncomputable def cutN (F : Type*) [Field F] [NumberField F] : ℕ :=
  max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))

end C3I

open NumberField

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L3V_VP
/-! # L3V_VP: the `P`-adic valuation `vP` and the unit-part symbol `uSym` (definitions and the
valuation algebra) -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

open Classical in
/-- The `P`-adic valuation `v_P(x) ∈ ℤ` (`0` if `P` is not a nonzero prime). -/
noncomputable def vP (P : Ideal (𝓞 F)) (x : F) : ℤ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then
    -log ((⟨P, h.1, h.2⟩ : HeightOneSpectrum (𝓞 F)).valuation F x)
  else 0

/-- The symbol `χ_P(x p^{−v_P(x)})` of the unit part of `x` at `P` (`p = gen P`). -/
noncomputable def uSym (g : AllowedGen ι 𝔪) (P : Ideal (𝓞 F)) (x : F) : ℂ :=
  localSymbol ι 𝔪 P (x * (g.gen P : F) ^ (-(vP P x)))

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.Z_Phi
/-! # Z_Phi: the Euler function of ideals of `𝓞 F`

* `Z.phi I = #(𝓞 F ⧸ I)ˣ`.
* `Z.phi_mul`: multiplicativity on coprime ideals (CRT).
* `Z.phi_prime_pow`: `φ(P^{k+1}) + N(P)^k = N(P)^{k+1}`.
* `Z.sum_divisors_phi`: `∑_{𝔡 ∣ 𝔠} φ(𝔡) = N(𝔠)` for `𝔠 ≠ ⊥`.
* `Z.phi_cube`: `φ(𝔞³) = N(𝔞)² φ(𝔞)` for `𝔞 ≠ ⊥`.
* `Z.phi_le`: `φ(𝔞) ≤ N(𝔞)`.
-/

set_option autoImplicit false

open NumberField

namespace ArtinKP

namespace Z

variable {F : Type*} [Field F] [NumberField F]

/-- The Euler function of an ideal: the number of units of `𝓞 F ⧸ I`. -/
noncomputable def phi (I : Ideal (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ I)ˣ

lemma absNorm_ne_zero {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : Ideal.absNorm I ≠ 0 := by
  rwa [Ne, Ideal.absNorm_eq_zero_iff]

/-! ### Divisors -/

lemma finite_dvd {c : Ideal (𝓞 F)} (hc : c ≠ ⊥) : {d : Ideal (𝓞 F) | d ∣ c}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm c)).subset ?_
  intro d hd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_ne_zero hc))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.1 hd))

open Classical in
/-- The finite set of divisors of a nonzero ideal (empty for `⊥`). -/
noncomputable def divs (c : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  if h : c = ⊥ then ∅ else (finite_dvd h).toFinset

end Z

end ArtinKP
end

section
-- module Solutions.Artin.T12.T12B_Euler
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

/-! ### Basic facts on Hecke characters -/

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

/-- The ideals not contained in any member of `T`. -/
def Cop (T : Finset (Ideal (𝓞 F))) : Set (Ideal (𝓞 F)) := {I | ∀ P ∈ T, ¬ I ≤ P}

/-- For each `I ∈ S` with `I ≠ ⊥, ⊤`, a chosen maximal ideal containing it. -/
noncomputable def primesOf (S : Finset (Ideal (𝓞 F))) : Finset (Ideal (𝓞 F)) := by
  classical
  exact (S.filter (fun I => I ≠ ⊤ ∧ I ≠ ⊥)).image
    (fun I => if h : I ≠ ⊤ then (Ideal.exists_le_maximal I h).choose else ⊤)

end T12B

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3P_Zeta
/-! # C3P_Zeta: the incomplete Dedekind zeta function `ζ^S`

`ζ^S(s) = ∏_{P ⊇ 𝔪}(1 − N P^{-s}) ζ_F(s) = R(s)/(s − 1)` with `R` entire, `R(1) = R_S`
(`sZetaResidue`), and `‖R(s)‖ ≤ C (2 + |Im s|)^k` on `9/10 ≤ Re s ≤ 12`. From 8087d96f
(`(s − 1) ζ_K` entire), 4f76b464 (convexity bound for `(s − 1) ζ_{K,T}`, here with `T = ∅`), the
Euler product 4d2ff9db, and Mathlib's class number formula; a field in an arbitrary universe is
replaced by a `Type` model. -/

set_option maxHeartbeats 1000000

open NumberField Complex Filter Topology

namespace ArtinPrimitiveRoots

namespace C3P

universe u

/-- `ζ^S`: the Dedekind zeta function with the Euler factors at the primes containing `𝔪`
removed. -/
noncomputable def zetaS {F : Type*} [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  (∏ᶠ P ∈ {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}, (1 - (Ideal.absNorm P : ℂ) ^ (-s))) *
    dedekindZeta F s

lemma finite_primes_ge {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) :
    {P : Ideal (𝓞 F) | P.IsPrime ∧ P ≠ ⊥ ∧ 𝔪 ≤ P}.Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (Ideal.absNorm 𝔪)).subset ?_
  intro P ⟨_, _, hle'⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]))
    (Ideal.absNorm_dvd_absNorm_of_le hle')

end C3P

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.Z_Series
/-! # Z_Series: the constant-term Dirichlet series `∑ φ(𝔞³) N(𝔞³)^{-s} = ζ^S(3s-3)/ζ^S(3s-2)`

`ζ^S = C3P.zetaS 𝔪` (Dedekind zeta with the Euler factors at the primes over `𝔪` removed).

* `Z.zetaS_eq_tsum`: `ζ^S(w) = ∑_{𝔞 exterior} N𝔞^{-w}` for `Re w > 1`.
* `Z.zetaS_ne_zero`: `ζ^S(w) ≠ 0` for `Re w > 1`.
* `Z.tsum_phi`: `∑_{𝔞 exterior} φ(𝔞) N𝔞^{-w} = ζ^S(w-1)/ζ^S(w)` for `Re w > 2`.
* `Z.tsum_cubeTerm`, `Z.summable_cubeTerm`: the cube form, `Re s > 4/3`.
* `Z.tsum_G0`: the same as a sum over exterior ideals `𝔠` of `G₀(𝔠) N𝔠^{-s}`,
  `G₀(𝔠) = φ(𝔠)·1[𝔠 is a cube]` (MATH2 §3.1).
-/

set_option autoImplicit false

open NumberField ArtinPrimitiveRoots

namespace ArtinKP

namespace Z

variable {F : Type*} [Field F] [NumberField F]

/-- `N(I)^{-w}`. -/
noncomputable def nrm (w : ℂ) (I : Ideal (𝓞 F)) : ℂ := (Ideal.absNorm I : ℂ) ^ (-w)

/-- The set of exterior ideals. -/
def Ext (𝔪 : Ideal (𝓞 F)) : Set (Ideal (𝓞 F)) := {I | IsExterior 𝔪 I}

/-- The summand `φ(𝔞) N𝔞^{-w}` on exterior ideals. -/
noncomputable def phiTerm (𝔪 : Ideal (𝓞 F)) (w : ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  (Ext 𝔪).indicator (fun I => (phi I : ℂ) * nrm w I) I

/-! ### The cube form -/

/-- The summand `φ(𝔞³) N(𝔞³)^{-s}` on exterior ideals `𝔞` (zero elsewhere). -/
noncomputable def cubeTerm (𝔪 : Ideal (𝓞 F)) (s : ℂ) (I : Ideal (𝓞 F)) : ℂ :=
  (Ext 𝔪).indicator (fun I => (phi (I ^ 3) : ℂ) * (Ideal.absNorm (I ^ 3) : ℂ) ^ (-s)) I

/-! ### The form `∑_𝔠 G₀(𝔠) N𝔠^{-s}` of MATH2 §3.1 -/

open Classical in
/-- `G₀(𝔠) = φ(𝔠)·1[𝔠 = 𝔡³]`. -/
noncomputable def G0 (c : Ideal (𝓞 F)) : ℕ := if ∃ d : Ideal (𝓞 F), c = d ^ 3 then phi c else 0

/-- The summand `G₀(𝔠) N𝔠^{-s}` on exterior ideals `𝔠` (zero elsewhere). -/
noncomputable def g0Term (𝔪 : Ideal (𝓞 F)) (s : ℂ) (c : Ideal (𝓞 F)) : ℂ :=
  (Ext 𝔪).indicator (fun c => (G0 c : ℂ) * (Ideal.absNorm c : ℂ) ^ (-s)) c

end Z

end ArtinKP
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

/-- `m_Φ(s)`, in the normalization where `vol(D) · vol(𝔩_M) = 1`:
`(π/(s-1))^r · ∑_c g(0, c) Lam Φ c 0 s N(c)^{-s}`. -/
def mCoeff (s : ℂ) : ℂ :=
  ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F) * aCoeff hG hz6 Φ 0 s

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Const
/-!
# WP-B, part 10: the sum of big-cell sections over the classes (MATH2 §3.1), first half

`sumBig = ∑_{η ∈ T} bigCell η 𝔩_M` for a complete system `T` of pairwise disjoint classes
(`RO.exists_classReps`).

* `validDepth_sumBig`: `M` is a valid depth for `sumBig` at the frequency `0`.
* `LamR_sumBig`: `Lam Φ^Σ c 0 s = vol(𝔩_M) · ⟨η_c, c⟩` for `c ≠ 0` of class `η_c ∈ T`.
* `brk_of_cube`: `⟨η_c, c⟩ = 1` when `c = u b³` (`u ∈ U_S`): the symbol factor disappears on the
  support of `G₀`.
* `kTerm_sumBig_cube`: the summand of `𝔞_{Φ^Σ}(0, s)` at `c = u b³` is
  `vol(𝔩_M) · φ(c) · N(c)^{-s}` (`φ = B7.phi`).

What remains for `m_{Φ^Σ}` is stated in `B_Stubs.lean`.
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

/-- `Φ^Σ = ∑_{η ∈ T} Φ^{big}_{η, 𝔩_M}` (MATH2 §3.1). -/
def sumBig (ι : F →+* ℂ) {P : CubicPkg F} (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (T : Finset {η : F // η ≠ 0}) : GSection ι P 𝔪 :=
  ∑ η ∈ T, bigCell ι P hG hN1 hN η.1 η.2 M 0

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.BZ_Main
/-!
# WP-BZ, part 5: the constant term of `E(Φ^Σ)` — what C9 uses

`Φ^Σ = sumBig ι hG hN1 hN M T`, `T` a complete system of pairwise disjoint classes, `D` any
fundamental cell of `Λ_M = transLat 𝔪 M`, `Re s > 2`, `ht = ∏_w v_w`.

* `vol_pos`, `volume_cell_ne_top`, `volume_cell_toReal`: `vol(D) = covol(𝓞_F)/vol(𝔩_M)`, finite.
* `sumBig_zero_left`: `Φ^Σ_s(0, d) = 0`, so the constant term has **no** `ht^s` term.
* **`const_term_sumBig`**:
  `∫_D E(Φ^Σ)(x, v) dx = (π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2) · ht^{2-s}`.
* **`mean_const_term_sumBig`**: the mean over the cell,
  `vol(D)⁻¹ ∫_D E(Φ^Σ) = C · (π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2) · ht^{2-s}` with
  `C = vol(𝔩_M)/covol(𝓞_F) = vol 𝔪 M / (volume (B1.fundD F)).toReal > 0` (`constC_pos`).
* **`exists_mean_const_term_pole`**: with the function `G` of `Z.exists_zetaRatio` (holomorphic on
  `Re s > 1`, `G(4/3) = ρ_S/(3ζ^S(2)) ≠ 0`), the coefficient is
  `C · (π/(s-1))^r · G(s)/(s - 4/3)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F]

/-- The constant `C = vol(𝔩_M)/covol(𝓞_F)`. -/
def constC (𝔪 : Ideal (𝓞 F)) (M : ℤ) : ℝ := vol 𝔪 M / (volume (B1.fundD F)).toReal

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.X2_Chart
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

/-! ### One factor -/

instance instSigmaFiniteE1Mu1 : SigmaFinite mu1 := by unfold mu1; infer_instance

/-! ### The product -/

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

/-- The complex sum over `H \ G`. -/
def automC (H : Subgroup G) (f : α → ℂ) (a : α) : ℂ := ∑' q : G ⧸ H, f (q.out⁻¹ • a)

end

end ArtinKP.X
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

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN (Γ : Subgroup (SL(2, 𝓞 F))) : Countable (latN Γ) :=
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  ((Set.to_countable (lamN Γ : Set (𝓞 F))).image embO).to_subtype

/-- `Λ_Γ ≃ latN Γ`. -/
def lamEquiv (Γ : Subgroup (SL(2, 𝓞 F))) : lamN Γ ≃ latN Γ :=
  ((lamN Γ).equivMapOfInjective embO embO_injective).toEquiv

/-! ### Orbits of `Λ_Γ` on the classes `≠ ∞` -/

variable {S : Finset (FinitePlace F)}

/-- The orbit relation of the translations of `Γ` on the classes `≠ ∞`. -/
def setN (Γ : Subgroup (SL(2, 𝓞 F))) (S : Finset (FinitePlace F)) :
    Setoid {p : PairClass S // p ≠ PairClass.inf S} where
  r p q := ∃ β ∈ lamN Γ, q.1 = p.1.act (nInt β)
  iseqv := by
    refine ⟨fun p => ⟨0, (lamN Γ).zero_mem, by rw [nInt_zero, PairClass.act_one]⟩, ?_, ?_⟩
    · rintro p q ⟨β, hβ, h⟩
      exact ⟨-β, (lamN Γ).neg_mem hβ, by
        rw [h, ← PairClass.act_mul, ← nInt_add, add_neg_cancel, nInt_zero, PairClass.act_one]⟩
    · rintro p q r ⟨β, hβ, h⟩ ⟨β', hβ', h'⟩
      exact ⟨β + β', (lamN Γ).add_mem hβ hβ', by rw [h', h, ← PairClass.act_mul, ← nInt_add]⟩

/-- Classes `≠ ∞` = (orbits of `Λ_Γ`) × `Λ_Γ`. -/
def orbN (Γ : Subgroup (SL(2, 𝓞 F))) (S : Finset (FinitePlace F)) :
    Quotient (setN Γ S) × lamN Γ ≃ {p : PairClass S // p ≠ PairClass.inf S} :=
  Equiv.ofBijective (fun z => upperEquiv (nInt_upper (z.2 : 𝓞 F)) z.1.out) ⟨by
    rintro ⟨ω, β⟩ ⟨ω', β'⟩ h
    have h1 : ω.out.1.act (nInt (β : 𝓞 F)) = ω'.out.1.act (nInt (β' : 𝓞 F)) :=
      congrArg Subtype.val h
    have h2 : ω'.out.1 = ω.out.1.act (nInt ((β : 𝓞 F) - β')) := by
      rw [sub_eq_add_neg, nInt_add, PairClass.act_mul, h1, ← PairClass.act_mul, ← nInt_add,
        add_neg_cancel, nInt_zero, PairClass.act_one]
    have hω : ω = ω' := by
      rw [← Quotient.out_eq ω, ← Quotient.out_eq ω']
      exact Quotient.sound ⟨(β : 𝓞 F) - β', (lamN Γ).sub_mem β.2 β'.2, h2⟩
    subst hω
    have := act_nInt_free ω.out ((β : 𝓞 F) - β') h2.symm
    have hβ : β = β' := Subtype.ext (sub_eq_zero.mp this)
    rw [hβ], by
    intro p
    obtain ⟨β, hβ, h⟩ := Quotient.mk_out (s := setN Γ S) p
    exact ⟨(⟦p⟧, ⟨β, hβ⟩), Subtype.ext h.symm⟩⟩

/-! ### The terms as shifted kernels -/

/-- The term of the class `p ≠ ∞` along `x ↦ (x, v)`, as one of WP-B's shifted kernels. -/
def hN (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (v : InfinitePlace F → ℝ)
    (p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)})
    (y : InfinitePlace F → ℂ) : ℂ :=
  hKer (wt h𝔪 Ψ s p.1) (Ninf p.1.out.c * X.sNorm (RO.SOf 𝔪) p.1.out.c p.1.out.d)
    (emb (p.1.out.d / p.1.out.c)) s v y

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The tail -/

/-- `E_Ψ(Q, s) − Ψ_s(0,1)·ht(Q)^s`. -/
def tail (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) : ℂ :=
  eis Ψ s Q - Ψ s (Row.inf 𝔪) * ((X.ht Q : ℝ) : ℂ) ^ s

/-! ### Finiteness of the unfolded `L¹` norm -/

/-! ### The integral over a cell -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.RF_Torus
/-!
# WP-RF, part 2: Fourier series on a fundamental cell of a lattice (abstract part of stub S1)

`E` a finite-dimensional real vector space with a Haar measure `μ`, `b : Basis J ℝ E`, lattice
`L = span ℤ (range b)`, cell `D₀ = ZSpan.fundamentalDomain b = {x | ∀ j, b.repr x j ∈ [0,1)}`,
characters `chi b n x = exp(2πi Σ_j n_j · b.repr x j)`, `n : J → ℤ` (these are exactly the
characters of `E` trivial on `L`).

* `map_toTorus`: `x ↦ (b.repr x j mod 1)_j` carries `μ|D₀` to `μ(D₀)` times the probability Haar
  measure of `UnitAddTorus J`.
* `hasSum_sq_coeff` (**Parseval**): `Σ_n |∫_{D₀} conj χ_n · g|² = μ(D₀) · ∫_{D₀} |g|²`.
* `ae_eq_zero_of_coeff` (**uniqueness**): if all coefficients of `g ∈ L²(D₀)` vanish then `g = 0`
  a.e. on `D₀`.

Everything is transported to Mathlib's `UnitAddTorus.mFourierBasis`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate ENNReal
open MeasureTheory Set

noncomputable section

namespace ArtinKP.RF

/-- As in `Mathlib.Analysis.Fourier.AddCircleMulti`: the circle carries its probability Haar
measure. -/
local instance instMeasureSpaceUnitAddCircle_solutions : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureUnitAddCircleVolume_solutions_rfdb280_1 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_rfdb280_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {J : Type*} [Fintype J]

/-- The unit cube `[0,1)^J`. -/
def cube (J : Type*) : Set (J → ℝ) := Set.univ.pi fun _ => Ico (0 : ℝ) 1

/-- Coordinatewise reduction modulo 1. -/
def piMk (y : J → ℝ) : UnitAddTorus J := fun j => (y j : UnitAddCircle)

/-- The section of `piMk` with values in the unit cube. -/
def piSec (t : UnitAddTorus J) : J → ℝ := fun j => (AddCircle.equivIco 1 0 (t j) : ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (b : Module.Basis J ℝ E)

/-- `x ↦ (b.repr x j mod 1)_j`. -/
def toTorus (x : E) : UnitAddTorus J := piMk (b.equivFun x)

/-- The section of `toTorus b` with values in the cell `ZSpan.fundamentalDomain b`. -/
def ofTorus (t : UnitAddTorus J) : E := b.equivFun.symm (piSec t)

/-- The character `exp(2πi Σ_j n_j · b.repr x j)` of `E`, trivial on `span ℤ (range b)`. -/
def chi (n : J → ℤ) (x : E) : ℂ := UnitAddTorus.mFourier n (toTorus b x)

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.RF_Strip
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

/-! ### The density of `X.vol` in product coordinates -/

/-! ### Boxes in `v` -/

/-- The bound for the density on the box. -/
def densBound (F : Type*) [Field F] [NumberField F] (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) + 1) ^ 3) ^ Fintype.card (InfinitePlace F)

/-! ### The basis of `XV F` adapted to a box -/

/-- Scaling by `1/(n+2)`. -/
def scaleEquiv (F : Type*) [Field F] [NumberField F] (n : ℕ) :
    (InfinitePlace F → ℝ) ≃ₗ[ℝ] (InfinitePlace F → ℝ) :=
  LinearEquiv.smulOfNeZero ℝ _ (((n : ℝ) + 2)⁻¹) (by positivity)

/-- The basis `(n+2)·e_w` of `ι → ℝ`. -/
def bT (F : Type*) [Field F] [NumberField F] (n : ℕ) :
    Module.Basis (InfinitePlace F) ℝ (InfinitePlace F → ℝ) :=
  Module.Basis.ofEquivFun (scaleEquiv F n)

variable {J : Type*} [Fintype J] (bV : Module.Basis J ℝ (InfinitePlace F → ℂ))

/-- The basis `bV ⊕ (n+2)·e_w` of `XV F`. -/
def bE (n : ℕ) : Module.Basis (J ⊕ InfinitePlace F) ℝ (XV F) := bV.prod (bT F n)

/-- The characters in `v` used on the box `vBox F n`:
`v ↦ exp(2πi Σ_w k_w v_w / (n+2))`. -/
def phiK (n : ℕ) (k : InfinitePlace F → ℤ) (v : InfinitePlace F → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ w, (k w : ℂ) * ((((n : ℝ) + 2)⁻¹ * v w : ℝ) : ℂ))

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.RF_Fourier
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

lemma pair_add (ν x y : InfinitePlace F → ℂ) : pair ν (x + y) = pair ν x + pair ν y := by
  simp only [pair, Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]

/-- The dual lattice `Λ^⊥` of the translation lattice of `Γ`. -/
def dualLat (Γ : Subgroup (SL(2, 𝓞 F))) : Set (InfinitePlace F → ℂ) :=
  {ν | ∀ γ : GammaN Γ, ∃ m : ℤ, pair ν (GammaN.shift γ) = m}

/-! ### A basis of the translation lattice -/

/-- `bV` is a basis of `ι → ℂ` whose `ℤ`-span is the translation lattice of `Γ`. -/
def IsLatBasis (Γ : Subgroup (SL(2, 𝓞 F))) {J : Type*}
    (bV : Module.Basis J ℝ (InfinitePlace F → ℂ)) : Prop :=
  ∀ x : InfinitePlace F → ℂ, x ∈ Submodule.span ℤ (Set.range bV) ↔
    ∃ γ : GammaN Γ, x = GammaN.shift γ

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

/-- A measurable fundamental domain of the translation lattice of `Γ` inside `{‖x_w‖ ≤ n₀}`. -/
structure Cell (Γ : Subgroup (SL(2, 𝓞 F))) (D : Set (InfinitePlace F → ℂ)) (n₀ : ℕ) : Prop where
  meas : MeasurableSet D
  fund : IsAddFundamentalDomain (latN Γ) D volume
  bdd : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀

/-- From the `hfund` form of WP-X2/WP-RF. -/
theorem Cell.of_hfund {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n₀ : ℕ} (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) : Cell Γ D n₀ := by
  refine ⟨hD, IsAddFundamentalDomain.mk' hD.nullMeasurableSet fun x => ?_, hn₀⟩
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

/-! ### The constant-term functional -/

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

/-- `ht^s` as a function on `X`. -/
def htC (s : ℂ) (P : X F) : ℂ := ((X.ht P : ℝ) : ℂ) ^ s

/-- **The coefficient of `ht^{2−s}`** in the constant term at `∞`, for the cell `D`:
`vol(D)⁻¹ ∫_D (E_Ψ − Ψ_s(0,1) ht^s)(x, 1) dx` (absolutely convergent for `Re s > 2`). -/
def mD (D : Set (InfinitePlace F → ℂ)) (Ψ : TSection ι 𝔪) (s : ℂ) : ℂ :=
  (((volume D).toReal : ℝ) : ℂ)⁻¹ *
    ∫ x in D, tail Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos))

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Res
/-! # WP-N, file 4: the continued coefficient `mext`, its residue `zRes`, the constant term of `θ_Ψ`

MATH2 §2.1(c),(d) and the first step of §2.2, for a cell `D` of `Γ` and a box index `n ≥ 1`:

* `phase s₁`, `cf_phase_ne_zero`: a test function `φ` with `cf D n φ (ht^{s₁}) ≠ 0`.
* `Acoef Γ Ψ D n φ s = cf(Eext) − Ψ_s(0,1)·cf(ht^s)` (written with `resPart` and `hInt`), holomorphic
  on `E.slit`; `Acoef_cross`: `A_φ(s)·⟨ht^{2−s},φ'⟩ = A_{φ'}(s)·⟨ht^{2−s},φ⟩` on `E.slit`.
* `mext Γ Ψ D n`: holomorphic on `E.slit` (`differentiableOn_mext`), equal to `mD D Ψ` for `Re s > 2`
  (`mext_eq_mD`), and `Acoef = mext · ⟨ht^{2−s}, φ⟩` on `E.slit` (`Acoef_eq_mext`) — the shape of the
  constant term of the continuation.
* `zRes Γ Ψ D n = lim (s_t − s₀)·mext(s_t)` (`tendsto_ray_mext`), and
  **`cf_theta`**: `cf D n' φ' (θ_Ψ) = zRes · cf D n' φ' (ht^{2/3})`.
* `zRes_eq_of_continuation`, `zRes_eq_zero_of_theta`, `cf_theta_eq_zero`.
* **`theta_eq_zero_of_inner`**: `⟪[F_{4/3}], θ_Ψ⟫ = 0 → θ_Ψ = 0` (`‖θ‖² = −c₀⟪F, θ⟫`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### A test function that sees `ht^{s₁}` -/

/-- The unit phase of `ht(v)^{s₁}`. -/
def phase (s₁ : ℂ) (v : InfinitePlace F → ℝ) : ℂ :=
  ((∏ w, v w : ℝ) : ℂ) ^ s₁ / ((‖((∏ w, v w : ℝ) : ℂ) ^ s₁‖ : ℝ) : ℂ)

/-! ### The coefficient function `Acoef` and the cross identity -/

/-- `cf(Eext Γ Ψ s) − Ψ_s(0,1)·cf(ht^s)`, with `cf(Eext) = cf(lift (resPart)) + cf(h_s)`. -/
def Acoef (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (D : Set (InfinitePlace F → ℂ)) (n : ℕ)
    (φ : (InfinitePlace F → ℝ) → ℂ) (s : ℂ) : ℂ :=
  cf D n φ (X.lift Γ (resPart Γ Ψ s)) + hInt Ψ n (stripFn D 0 φ) s
    - Ψ s (Row.inf 𝔪) * cf D n φ (htC s)

section

variable (hG : Good 𝔪) [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) {D : Set (InfinitePlace F → ℂ)} {n n' : ℕ}
  {φ φ' : (InfinitePlace F → ℝ) → ℂ}

/-! ### The continued coefficient and its residue -/

/-- **The continuation of the `ht^{2−s}`-coefficient** to `E.slit` (MATH2 §2.1(c)). -/
def mext (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (D : Set (InfinitePlace F → ℂ)) (n : ℕ)
    (s : ℂ) : ℂ :=
  Acoef Γ Ψ D n (phase (2 - s)) s / cf D n (phase (2 - s)) (htC (2 - s))

/-- **The residue of the `ht^{2−s}`-coefficient** (MATH2 §2.1(d)): `z_Ψ` for the cell `D`. -/
def zRes (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (D : Set (InfinitePlace F → ℂ))
    (n : ℕ) : ℂ :=
  cf D n (phase (2 / 3)) (X.lift Γ (theta Γ Ψ)) / cf D n (phase (2 / 3)) (htC (2 / 3))

end

/-! ### `‖θ‖² = −c₀⟪F, θ⟫` -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Level
/-! # WP-N, file 5: `θ_Ψ` under change of `Γ` and under `SL₂(R)` (C5's open item 3; MATH2 §2.1 end)

* `ae_eq_zero_of_box_tests`: a locally integrable function killed by all bounded test functions on
  all boxes vanishes almost everywhere.
* **`lift_theta_of_eis_smul`**: if `E_{Ψ'}(Q, s) = E_Ψ(τQ, s)` for `Re s > 2` (`τ ∈ SL₂(F)`), then
  `θ_{Γ'}(Ψ') = θ_Γ(Ψ) ∘ τ` almost everywhere, for any finite-index `Γ`, `Γ'` fixing `Ψ`, `Ψ'`.
* `lift_theta_congr`: `θ_Γ(Ψ)` does not depend on `Γ` (as a function on `X`, a.e.).
* `lift_theta_translate`: `θ(σ·Ψ)(Q) = θ(Ψ)(σ⁻¹Q)` for `σ ∈ SL₂(R)`.
* `cf_theta_translate`: the constant term of `θ_Ψ` at the cusp `σ⁻¹∞`, i.e. of `Q ↦ θ_Ψ(σ⁻¹Q)` at
  `∞`, is `zRes(σ·Ψ)·ht^{2/3}`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Test functions on boxes -/

/-! ### Transport of a box integral by `τ ∈ SL₂(F)` -/

/-- The test function `ψ` on `box n`, transported by `τ`. -/
def psiT (τ : SL(2, F)) (n : ℕ) (ψ : X F → ℂ) (P : X F) : ℂ :=
  (X.box n : Set (X F)).indicator ψ (τ⁻¹ • P)

/-! ### `θ` under a transformation of the series -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Main
/-! # WP-N, file 6: Corollary N (MATH2 §2.2), modulo the unfolding over the cusps

`theta_eq_zero_of_inner` (file 4) reduces `θ_Ψ = 0` to `⟪[F_{4/3}], θ_Ψ⟫ = 0`.  The remaining step
of Theorem N — a function on `Γ\X` all of whose constant terms vanish is orthogonal to the
pseudo-Eisenstein series `F_{4/3}` — is the **named hypothesis `CuspOrth`** (stated in
`N_Stubs.lean`, route in `WP-N.md`).  Everything else of Corollary N is proved here:

* `CuspVanish`: the constant terms of `θ_Γ(Ψ)` vanish at the cusp `σ⁻¹∞`, tested on a cell of some
  finite-index group fixing `σ·Ψ`.
* `corollaryN`: if `zRes(σ·Ψ) = 0` for all `σ ∈ SL₂(R)` then `θ_Ψ = 0`.
* `corollaryN_of_continuation`: the same with the residues read off arbitrary continuations.
* `zRes_translate_eq_zero_of_theta`: conversely `θ_Ψ = 0` forces every `zRes(σ·Ψ) = 0`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-- The constant term of `θ_Γ(Ψ)` at the cusp `σ⁻¹∞` vanishes: for some finite-index `Γ'` fixing
`σ·Ψ` and some cell `D` of `Γ'`, all functionals `cf D n φ` kill `Q ↦ θ_Γ(Ψ)(σ⁻¹Q)`. -/
def CuspVanish (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) (σ : SL(2, SInt 𝔪)) : Prop :=
  ∃ (Γ' : Subgroup (SL(2, 𝓞 F))) (D : Set (InfinitePlace F → ℂ)) (n₀ : ℕ),
    Γ'.FiniteIndex ∧ Inv Γ' (TSection.translate Pk hG hz6 σ Ψ) ∧ Cell Γ' D n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
        cf D n φ (fun Q => X.lift Γ (theta Γ Ψ) (toF 𝔪 σ⁻¹ • Q)) = 0

/-- **Named hypothesis (owner: WP-N, `N_Stubs.cuspOrth`)**: the unfolding step of Theorem N.
If the constant terms of `θ_Γ(Ψ)` vanish at all cusps, then `θ_Γ(Ψ)` is orthogonal to the source
`[F_{4/3}]` (a pseudo-Eisenstein series with profile supported in heights `[2, 3]`). -/
def CuspOrth (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪) : Prop :=
  (∀ σ : SL(2, SInt 𝔪), CuspVanish Pk hG hz6 Γ Ψ σ) → ⟪srcL2 Γ Ψ (4 / 3), theta Γ Ψ⟫_ℂ = 0

end

end ArtinKP.N
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

/-! ### The two families of lattices -/

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat (Γ : Subgroup (SL(2, 𝓞 F))) (M : ℤ) : Countable ↥(latN Γ ⊓ transLat 𝔪 M) :=
  (AddSubgroup.inclusion_injective (inf_le_left : latN Γ ⊓ transLat 𝔪 M ≤ latN Γ)).countable

/-! ### Cells -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.C9_Const
/-!
# WP-C9, part 2: a `Γ`-invariant function with the constant-term shape is zero

Analytic core of (C10′) (MATH3 §5.1), independent of sections and of θ.

* `integral_conj_eChar_eq_zero`: orthogonality of a nonzero character of the dual lattice over a
  strict cell of `Λ_Γ`.
* **`ae_eq_htC_of_coeff`**: let `f` be measurable, `GammaN Γ`-invariant, `L²` on boxes.  If the
  frequency-`0` functionals of `f` are those of `z·ht^{s₁}` and all functionals at nonzero
  frequencies `ν ∈ Λ_Γ^⊥` vanish, then `f = z·ht^{s₁}` a.e.  (This contains WP-RF's optional
  lemma "nonzero frequencies vanish ⇒ independent of `x`", and its Fubini step, in one
  application of `RF.ae_eq_zero_of_strip` to `f − z·ht^{s₁}`.)
* `isOpenPosMeasure_vol`: `X.vol` is positive on nonempty open sets (chart + positive density).
* `lowInt`, `exists_lower_mem`: a finite-index `Γ` contains `[[1,0],[k,1]]`, `k ≠ 0`.
* `not_ae_ht_smul`: `ht(γP) = ht(P)` a.e. is impossible when the lower left entry of `γ` is
  nonzero (`X.pairHt_mul_pairHt_le`: then `ht² ≤ 1/|N(c)|²` everywhere).
* **`eq_zero_of_lift_ae_eq_htC`**: `u ∈ L²(Γ\X)` with `lift u = z·ht^{s₁}` a.e., `Re s₁ ≠ 0`, is `0`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Characters -/

/-! ### Strip integrals as box integrals -/

/-! ### The constant-term shape forces the function -/

/-! ### `X.vol` is positive on open sets -/

/-! ### Lower unipotent elements -/

/-- `[[1, 0], [β, 1]]`. -/
def lowInt (β : 𝓞 F) : SL(2, 𝓞 F) := ⟨!![1, 0; β, 1], by simp [Matrix.det_fin_two]⟩

/-! ### Step (iii) -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.C9_Nonvanish
/-!
# WP-C9, part 1: `θ_{Φ^Σ} ≠ 0` (MATH2 §3)

`Φ^Σ = B.sumBig ι hG hN1 hN M T` (`T` a complete disjoint system of classes, `M ≥ 0`),
`Ψ^Σ = twist Φ^Σ`.

* `mD_eq_of_mean`: reconciliation of the two normalizations.  WP-N's coefficient `mD D Ψ s` is a
  mean over a cell `D` of `Λ_Γ = N.latN Γ`; WP-BZ computes means over cells of
  `Λ_M = B.transLat 𝔪 M`.  The two lattices are commensurable (`T.relIndex_inf_left/right`) and
  the means agree (`T.mean_eq`).
* `mD_sumBig`: `mD D Ψ^Σ s = C·(π/(s-1))^r·G(s)/(s-4/3)` for `Re s > 2`, `G` as in
  `BZ.exists_mean_const_term_pole`.
* **`zRes_sumBig`**: `zRes Γ Ψ^Σ D n = C·(3π)^r·G(4/3)`, and **`zRes_sumBig_ne_zero`**.
* **`theta_sumBig_ne_zero`**: `θ_{Ψ^Σ} ≠ 0`, for every finite-index `Γ` fixing `Ψ^Σ`.
* **`exists_theta_bigCell_ne_zero`**: some single big-cell section has `θ ≠ 0`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The class-sum section -/

section sumBig

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0})

/-- `Ψ^Σ`, the twisted class-sum section. -/
def psiSum (ι : F →+* ℂ) : TSection ι 𝔪 := (sumBig ι hG hN1 hN M Tc).twist hG hz6

/-- The meromorphic model of the constant-term coefficient: `C·(π/(s-1))^r·G(s)/(s-4/3)`. -/
def mModel (𝔪 : Ideal (𝓞 F)) (M : ℤ) (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  ((BZ.constC 𝔪 M : ℝ) : ℂ) * ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
    * (G s / (s - 4 / 3))

end sumBig

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.C9_Tau
/-!
# WP-C9, part 4: (C10′) and (C9) in the vocabulary of WP-T (`T.tau`, `T.theta`)

WP-T's `T.coeff_theta` computes the coefficient functional of `θ_{Φ.twist}` at the frequency
`T.freq ν`, `ν ∈ R ∖ 0` (`R = SInt 𝔪`), as `kap · τ_Φ(ν) · Wc`.  The core lemma
`C9.theta_eq_zero_of_coeff` needs the vanishing at **every** nonzero frequency of WP-RF's dual
lattice `RF.dualLat Γ`.  The bridge is the one named hypothesis of this file:

* `DualCover 𝔪 Γ`: every nonzero `ν' ∈ RF.dualLat Γ` is `T.freq ν` for some `ν ∈ R`.
  (True when `Λ_Γ ⊇ emb(𝔪^N)` — `TransLevel 𝔪 Γ` — and the different of `F` is supported in the
  primes of `𝔪`: trace duality.  Proved in `C9_Dual.lean` / stated in `C9_Stubs.lean`, see
  WP-C9.md.)

Results:

* `stabGroup Ψ` (the full stabilizer of `Ψ` in `SL₂(𝓞)`), finite index, `TransLevel` for twists.
* **`theta_eq_zero_of_tau`** — (C10′) in WP-T's form: `τ_Φ(ν) = 0` for all `ν ∈ R ∖ 0` implies
  `θ_{Φ.twist} = 0`.
* **`exists_tau_sumBig_ne_zero`**, **`exists_tau_bigCell_ne_zero`** — the hypothesis of package
  G (MATH3 §1.2 (G1)): some `τ_{Φ^Σ}(ν₁) ≠ 0`, and some single class `η` with
  `τ_{Φ^big_η}(ν) ≠ 0`.
* `exists_kir_ne_zero_of_theoremE`: given Theorem E in any form `τ_Φ(ν) = c(ν)·𝒦_Φ(ν)`, the
  Kirillov function is not identically zero.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The full stabilizer -/

/-- The stabilizer of `Ψ` in `SL₂(𝓞_F)`. -/
def stabGroup (Ψ : TSection ι 𝔪) : Subgroup (SL(2, 𝓞 F)) := Ψ.stab.comap (RO.intMat 𝔪)

/-- `Λ_Γ ⊇ emb(𝔪^N)` for some `N`: the translations of `Γ` have a level supported in `𝔪`. -/
def TransLevel (𝔪 : Ideal (𝓞 F)) (Γ : Subgroup (SL(2, 𝓞 F))) : Prop :=
  ∃ N : ℕ, ∀ β ∈ 𝔪 ^ N, nInt β ∈ Γ

/-! ### The bridge between the two parametrizations of the frequencies -/

/-- **Named hypothesis (trace duality).**  Every nonzero frequency of WP-RF's dual lattice of the
translations of `Γ` is `T.freq ν` for some `ν ∈ R = SInt 𝔪`. -/
def DualCover (𝔪 : Ideal (𝓞 F)) (Γ : Subgroup (SL(2, 𝓞 F))) : Prop :=
  ∀ ν' ∈ dualLat Γ, ν' ≠ 0 → ∃ ν : SInt 𝔪, T.freq ((ν : SInt 𝔪) : F) = ν'

/-! ### (C10′) in WP-T's form -/

/-! ### The hypothesis of package G -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.DD_Cut
/-!
# WP-DD, part 1: the different is supported in `S` once the cut-off is large

* `DiffInS 𝔪`: no prime outside `placesOf 𝔪` divides the different of `F`. This is, verbatim,
  the hypothesis `hdiff` of `C9_Dual` (`C9.dualCover_of_transLevel`, `C9.theta_eq_zero_of_tau'`).
* `cutD F = N(𝔡_F)`; `diffInS_of_smallPrimesDvd : cutD F ≤ N → SmallPrimesDvd N 𝔪 → DiffInS 𝔪`.
* `smallPrimesDvd_mono`; `exists_cutoff_diffInS`, and the combined, monotone form
  `exists_cutoff_good_diffInS : ∃ N₁, ∀ N, N₁ ≤ N → ∀ 𝔪 ≠ ⊥, SmallPrimesDvd N 𝔪 → Good 𝔪 ∧ DiffInS 𝔪`.
* `diffInS_of_cutN`: the cut-off `C3I.cutN F` already used at assembly (`H_Aut`) is enough;
  `diffInS_of_good`: the alternative source `C3I.Good.diff` at every exterior prime.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

namespace ArtinKP.DD

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- The different of `F` is supported in the primes of `𝔪`: no prime outside `placesOf 𝔪`
divides `𝔡_F`. (The hypothesis `hdiff` of `C9_Dual`, by `Iff.rfl`.) -/
def DiffInS (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 → ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal

/-- The cut-off for the different: its absolute norm. -/
noncomputable def cutD (F : Type*) [Field F] [NumberField F] : ℕ :=
  Ideal.absNorm (differentIdeal ℤ (𝓞 F))

end ArtinKP.DD
end

section
-- module Solutions.Artin.KP.F_Alg_Sum
/-!
# WP-FA, part 1: summation tools for cube periodicity (MATH2 §5)

* `tsum_orbit_rel`: reindexing of a sum over orbits of a group action along an equivariant
  partial bijection given as a relation (used for rows modulo units).
* `IsReps c T`: `T` is a complete set of representatives of `R ⧸ (c)`; `sum_reps`: sums over `T`
  of periodic functions are `B7.rsum`s; affine substitution; the counts and the vanishing of
  twisted sums used in the strata of Proposition 5.4.
* `sum_reps_addChar` (MATH2 §5.1): `∑_{t ∈ T} e(μ t / π^n) = q^n · 1[π^n ∣ μ]` — the character sum
  behind `(U u)_ν = q³ · 1[v_P(ν) ≥ 0] · u_{νπ³}`.
-/

set_option autoImplicit false

namespace ArtinKP.FA

open ArtinKP.B7

/-! ### Sums over orbits -/

section orbit

variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β]

/-- The orbit quotient `α / G`. -/
abbrev OQ (G α : Type*) [Group G] [MulAction G α] : Type _ := MulAction.orbitRel.Quotient G α

end orbit

/-! ### Complete sets of representatives -/

section reps

variable {R : Type*} [CommRing R]

/-- `T` is a complete set of representatives of `R ⧸ (c)`. -/
def IsReps (c : R) (T : Finset R) : Prop := ∀ x : R, ∃! t, t ∈ T ∧ c ∣ x - t

end reps

/-! ### The additive character sum of §5.1 -/

end ArtinKP.FA
end

section
-- module Solutions.Artin.KP.F_Alg_Symbol
/-!
# WP-FA, part 2: the strata of Proposition 5.4 and their symbols (MATH2 §5.3)

`π` generates an exterior prime (`PrimeElt`).  For `m ≤ 3` and `t ∈ R` the relation
`Rel π m t p p₁` says `p · [[1, t], [0, π³]] = π^m · p₁` with `m = min(v_P(c), 3)`:

  `p = (π^m c₁, d)`,  `p₁ = (c₁, c₁ t + π^(3-m) d)`,  and `π ∤ c₁` if `m < 3`.

* bijection part: `rel_smul`, `rel_fun`, `rel_inj`, `rel_dom_iff`, `rel_cod_iff`;
* symbol part: `kappa_rel` (`π ∤ c₁`), `kappa_rel_three` (`m = 3`, all cells, incl. the lower
  cells `π ∣ c₁`), `Phi_rel` (the `S_f`-part for a `t` that is deep for `Φ`);
* the phase `Theta` on the strata `m = 1, 2` and its vanishing sum `rsum_Theta`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section basic

variable {ι : F →+* ℂ} {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪}

theorem PrimeElt.coe_ne_zero (H : PrimeElt ι 𝔪 v π) : (π : F) ≠ 0 := fun h =>
  H.ne_zero (Subtype.ext h)

end basic

/-! ### The relation -/

/-- `p · [[1, t], [0, π³]] = π^m · p₁`, `m = min(v_P(c), 3)`. -/
def Rel (π : SInt 𝔪) (m : ℕ) (t : SInt 𝔪) (p p₁ : Row 𝔪) : Prop :=
  p.c = π ^ m * p₁.c ∧ p₁.d = p₁.c * t + π ^ (3 - m) * p.d ∧ (m < 3 → ¬ π ∣ p₁.c)

/-! ### Powers in the cubic symbol -/

/-! ### The phase on the strata `m = 1, 2` -/

open Classical in
/-- `Θ_m(x) = (d/π)^{-m}` if `x = π^(3-m) d` with `π ∤ d`, and `0` otherwise. -/
def Theta (ι : F →+* ℂ) (π : SInt 𝔪) (m : ℕ) (x : SInt 𝔪) : ℂ :=
  if h : ∃ d, x = π ^ (3 - m) * d ∧ ¬ π ∣ d then ((cubicExt ι 𝔪 h.choose π)⁻¹) ^ m else 0

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.F_Alg_Main
attribute [-instance] _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-!
# WP-FA, part 3: Proposition 5.4 as a reindexing identity (MATH2 §5.3)

`π` generates the exterior prime `v` (`PrimeElt`), `T` is a complete set of representatives of
`R/π³R` whose elements are deep for the genuine section `Φ`, and `f : F → F → ℂ` is an arbitrary
function with `f(πc, πd) = cc · f(c, d)` and `f(εc, εd) = |ε|_{S_f}^s f(c, d)` for `ε ∈ U_S`
(in the application `f = I_{(c,d)}(P)^s`, `cc = N_∞(π)^{-s}`).  With `Ψ = κΦ`, `Ψ♯ = κΦ♯`,
`X = cc³ |π|_{S_f}^{-3s}` and `q = #(R/πR)`:

  `∑_{t ∈ T} ∑_{p ∈ Row/U_S} Ψ_s(p) f(p·[[1,t],[0,π³]])
      = q³X · ∑_{p₁} Ψ♯_s(p₁) f(p₁) + (1 - q²X) · ∑_{p₁} (Ψ♯·1[P ∤ c₁])_s(p₁) f(p₁)`

(`prop54`; `prop54_omega` is the form with the weight `ω(a₁)` and needs no summability of the
right-hand side).  The counting part is `fiber_sum`, the symbol part is `W_spec`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- Rows modulo units, `𝒫 = R²_prim / U_S`. -/
abbrev RowQ (𝔪 : Ideal (𝓞 F)) : Type _ := OQ (SInt 𝔪)ˣ (Row 𝔪)

variable {ι : F →+* ℂ} (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪} (H : PrimeElt ι 𝔪 v π) (Φ : GSection ι P 𝔪)

/-- The value of `Ψ_s = κΦ_s` on the source row of the stratum `(m, t)` over `p₁`
(`W_spec`), written in terms of `p₁`. -/
def W (m : ℕ) (t : SInt 𝔪) (s : ℂ) (p₁ : Row 𝔪) : ℂ :=
  if m = 0 then (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s p₁
  else if m = 3 then ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))
    * (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s p₁
  else Theta ι π m (p₁.d - p₁.c * t) * cubicExt ι 𝔪 π p₁.c ^ (3 - m) * kappaRow ι p₁
    * Φ s ((π : F) ^ m * (p₁.c : F)) ((π : F) ^ m * ((p₁.d : F) / (π : F) ^ 3))

/-! ### The reindexing identity -/

section main

variable {T : Finset (SInt 𝔪)} (hT : IsReps (π ^ 3) T)
  (hdeep : ∀ t ∈ T, ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d)
  (f : F → F → ℂ) (s cc : ℂ)
  (hfπ : ∀ c d : F, f ((π : F) * c) ((π : F) * d) = cc * f c d)
  (hfU : ∀ (ε : (SInt 𝔪)ˣ) (c d : F), f (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * d)
    = ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ s * f c d)

/-- The summand of `U E_Φ`: `Ψ_s(p) · f(p · [[1, t], [0, π³]])`. -/
def gU (t : SInt 𝔪) (p : Row 𝔪) : ℂ :=
  Φ.twist hG hz6 s p * f (p.c : F) ((p.c : F) * (t : F) + (π : F) ^ 3 * (p.d : F))

end main

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.F_Eis_Op
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-!
# WP-FB, part 2: the maps `g_t` on `X F`, the operator `U`, and the product formula at `π`

MATH2 §5.1: `g_t : (x, v) ↦ ((x + t)/π³, v/|π³|)` is the action of the `GL₂(F)` matrix
`[[1, t], [0, π³]]`, of determinant `π³`; it is **not** in `SL₂(F)`, and the tree's action on
`X F` is of `SL(2, F)` only.  So the map is defined in coordinates, for an arbitrary `a ≠ 0` in
place of `π³`:

* `gmap a ha t : X F → X F`, `(x, v) ↦ ((x + t)/a, v/|a|)` (ordinary moduli at each place);
  `gmap_eq_torus_trans` (it is `X.torus ∘ X.trans`), `measurePreserving_gmap`, `continuous_gmap`;
* `Nh a = ∏_w |a|_w` (ordinary moduli; `Nh a ^ 2 = B.Ninf a`, so `Nh a = N_∞(a)^{1/2}`);
* `pairHt_gmap`: `I_{(c,d)}(g_t Q) = Nh a · I_{(c, c t + a d)}(Q)`
  (MATH2: `N_∞(π)^{3/2}` for `a = π³`); `ht_gmap`;
* `U a ha T u Q = ∑_{t ∈ T} u (g_t Q)`;
* `Ninf_mul_absS_of_span`: `N_∞(π) · |π|_{S_f} = N P` for a generator `π` of `P·R`, `P` exterior
  (the product formula; WP-FA §6 item 2), and `Ninf_mul_absS_gen` at `g.gen P`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### `Nh`: the product of the ordinary moduli -/

/-- `Nh a = ∏_w |a|_w` with ordinary moduli; `Nh a ^ 2 = N_∞(a)`. -/
def Nh (a : F) : ℝ := ∏ w : InfinitePlace F, ‖w.embedding a‖

/-! ### The maps `g_t` -/

/-- `g_{a,t} : (x, v) ↦ ((x + t)/a, v/|a|)`: the action of `[[1, t], [0, a]] ∈ GL₂(F)` on `X`
(MATH2 §5.1 with `a = π³`). -/
def gmap (a : F) (ha : a ≠ 0) (t : F) (Q : X F) : X F :=
  X.mk (fun w => (Q.x w + w.embedding t) / w.embedding a) (fun w => Q.v w / ‖w.embedding a‖)
    (fun w => div_pos (Q.v_pos w) (norm_pos_iff.2 ((map_ne_zero _).2 ha)))

@[simp] theorem x_gmap (a : F) (ha : a ≠ 0) (t : F) (Q : X F) (w : InfinitePlace F) :
    (gmap a ha t Q).x w = (Q.x w + w.embedding t) / w.embedding a := rfl

@[simp] theorem v_gmap (a : F) (ha : a ≠ 0) (t : F) (Q : X F) (w : InfinitePlace F) :
    (gmap a ha t Q).v w = Q.v w / ‖w.embedding a‖ := rfl

/-! ### The operator `U` -/

/-- **The operator `U`** of MATH2 §5.1: `(U u)(Q) = ∑_{t ∈ T} u(g_t Q)`,
`g_t = gmap a ha t`; in the application `a = π³` and `T` is a deep complete set of
representatives of `R/π³R`. -/
def U (a : F) (ha : a ≠ 0) (T : Finset (SInt 𝔪)) (u : X F → ℂ) (Q : X F) : ℂ :=
  ∑ t ∈ T, u (gmap a ha (t : F) Q)

/-! ### The product formula at a generator of an exterior prime -/

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Fourier
/-!
# WP-FB, part 4: the operator `U` on Fourier coefficients (MATH2 §5.1)

Vocabulary of WP-B (`B_FourArch`): `emb : F →+ ℂ^r`, `eInf`, and the character
`chiInf ν x = conj e_∞(ν x)` against which the `ν`-th coefficient is taken; a coefficient is an
integral over a cell `D` (a fundamental domain of a lattice `L ⊂ ℂ^r` of periods).

* `sum_eInf_reps`: `∑_{t ∈ T} e_∞(μ t/πⁿ) = (N P)ⁿ · 1[πⁿ ∣ μ]` for `T` deep
  (`FA.sum_reps_sAddChar` and `B.psiS_small`);
* `setIntegral_image_mulE`: the change of variables `x = a·y` on `ℂ^r`, Jacobian `N_∞(a)`;
* `setIntegral_translate`, `integrableOn_translate`: integrals of periodic functions over a
  cell are translation invariant;
* `coeff_sum_translate`: on `ℂ^r`, for an `L`-periodic `h`,
  `∫_{aD} (∑_t h((x+t)/a)) conj e_∞(νx) dx = N_∞(a) (∑_t e_∞(νt)) ∫_D h(y) conj e_∞(νa·y) dy`;
* `coeff_U`: the same for `U a T u` at height `v`;
* `coeff_U_gen`: **`(Uu)_ν(v) = q³ · 1[ν ∈ R] · u_{νπ³}(v/|π³|)`** at `π = g.gen P`
  (cells `π³D` and `D`; the factor `N_∞(π³) = vol(π³D)/vol(D)` is the normalization of the cell).
-/

set_option autoImplicit false

open scoped ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-! ### The character sum in `e_∞` form -/

/-! ### Scaling on `ℂ^r` -/

/-- Multiplication by `A ∈ ℂ^r` as an `ℝ`-linear map of `ℂ^r`. -/
def mulE (A : InfinitePlace F → ℂ) : (InfinitePlace F → ℂ) →ₗ[ℝ] (InfinitePlace F → ℂ) :=
  LinearMap.pi fun w => (LinearMap.mul ℝ ℂ (A w)).comp (LinearMap.proj w)

/-! ### Translation invariance over a cell -/

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Main
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-!
# WP-FB, part 3: Proposition 5.4 for the Eisenstein series `B.eis`, `Re s > 2` (MATH2 §5.3)

With `Ψ = Φ.twist`, `Ψ♯ = (Φ.sharp π).twist`, `q = #(R/πR) = N P`, `T` a complete set of
representatives of `R/π³R` deep for `Φ`, and `U = FB.U (π³) T`:

  `U (eis Ψ s) Q = Nh(π³)^s · [ q³·(q^{-s})³ · eis Ψ♯ s Q + (1 − q²·(q^{-s})³) · eis (restrict Ψ♯) s Q ]`

pointwise in `Q : X F`, for every `s` with `Re s > 2`; `Nh(π³)^s = N_∞(π)^{3s/2}`
(`Nh_pi_cube_cpow`), `q³(q^{-s})³ = q^{3-3s}`, `q²(q^{-s})³ = q^{2-3s}` (`q_cpow_three`,
`q_cpow_two`).

* `primeElt_gen'`: `FA.PrimeElt` at `g.gen P`, unconditional (S2's cubic symbol);
* `fQ`, `fQ_pi`, `fQ_unit`: the summand `f = I_p(Q)^s` and its two homogeneities;
* `term_gmap`, `eis_gmap`: `eis Ψ s (g_t Q) = Nh(π³)^s · ∑' gU`;
* `U_eis_primeElt`: the identity for any `PrimeElt`, with FA's constants;
* `U_eis`: the same with `X = (q^{-s})³` under `N_∞(π)|π|_{S_f} = q`;
* `U_eis_gen`, `exists_U_eis_gen`: at an allowed generator of a good exterior prime, all
  hypotheses discharged; the second also produces the deep `T`, uniformly in `s`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-! ### The summand `f = I_p(Q)^s` -/

/-- `f_Q(c, d) = I_{(c,d)}(Q)^s`. -/
def fQ (s : ℂ) (Q : X F) (c d : F) : ℂ := ((X.pairHt c d Q : ℝ) : ℂ) ^ s

/-! ### The Eisenstein series at `g_t Q` -/

/-! ### Rewriting the constants in MATH2's form -/

/-! ### At an allowed generator of a good exterior prime -/

/-! ### Regularity in `s` and `Q`, and almost-everywhere classes

What a later package needs to continue the identity of `U_eis_gen` analytically: `T` does not
depend on `s` (`exists_U_eis_gen`); both sides are holomorphic in `s` on `Re s > 2` for each
`Q` (`differentiableOn_U_eis`, `B.differentiableOn_eis`) and continuous in `Q`; and `U` is
defined on almost-everywhere classes (`U_ae_congr`, from `measurePreserving_gmap`), so it acts
on `L²_loc`-valued functions of `s`. -/

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.T_Vanish
/-! # WP-T, file 8: vanishing of the coefficients at characters outside the full dual lattice

Let `Γ`, `Γ'` be of finite index, both fixing `Ψ`, `D` a bounded strict cell of `Λ_Γ` and
`ν' ∈ RF.dualLat Γ`.  If `e_{ν'}(g) ≠ 1` for some `g ∈ Λ_{Γ'}`, then the `ν'`-th Fourier
coefficient over `D` vanishes: for the series (`integral_eis_eChar_eq_zero`, `Re s > 2`), for the
continuation (`Afun_eChar_eq_zero`, on `E.slit`) and for `θ_Ψ` (**`coeff_theta_eq_zero`**).

For a genuine section `Φ` the group `Γ'` can be taken with `Λ_{Γ'} ⊇ Λ_M` for every depth `M ≥ 0`
of unipotent invariance (`transLat_le_latN_stabGroup`), whence
**`coeff_theta_eq_zero_of_transLat`**: only the characters trivial on `Λ_M` contribute to `θ`.
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

section vanish

variable (hG : Good 𝔪) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] [Γ'.FiniteIndex]
  {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ' Ψ) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
  {ν' : InfinitePlace F → ℂ} {g : InfinitePlace F → ℂ}

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN (Γ Γ' : Subgroup (SL(2, 𝓞 F))) : Countable ↥(latN Γ ⊓ latN Γ') :=
  (AddSubgroup.inclusion_injective (inf_le_left : latN Γ ⊓ latN Γ' ≤ latN Γ)).countable

end vanish

/-! ### Genuine sections: the stabilizer contains `n(Λ_M)` -/

section genuine

variable {P : CubicPkg F} (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪)

/-- The largest subgroup of `SL₂(𝓞_F)` fixing `Ψ`. -/
def stabGroup (Ψ : TSection ι 𝔪) : Subgroup (SL(2, 𝓞 F)) := Ψ.stab.comap (RO.intMat 𝔪)

end genuine

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.F_Per_Mean
/-! # WP-F, file 1: means over cells of admissible lattices; scaled lattices

* `Adm A`: the lattice `A ⊂ ℂ^r` lies between `emb(I)` (`I` a nonzero ideal) and `emb(𝓞_F)`.
  `latN Γ`, `transLat 𝔪 M` (`M ≥ 0`) and `scaleLat a (transLat 𝔪 M)` (`a ∈ R`, `M` large) are
  admissible.
* `mean_adm`: a continuous `A₁`-periodic function whose integrals over all translates of a cell of
  `A₂` are `vol·I` has integral `vol(D₁)·I` over every bounded strict cell of `A₁` (`T.mean_eq`).
* `scaleLat a L`, `scaleSet a D`: the lattice `a·L` and its cell `a·D`.
* `hasCoef_adm`: `T.hasCoef_latN` for cells of any admissible lattice of periods.
* `const_adm`: the constant term of `E_Φ` over such a cell (`B.const_term_mCoeff`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Admissible lattices -/

/-- A lattice between the image of a nonzero ideal and `emb(𝓞_F)`. -/
structure Adm (A : AddSubgroup (InfinitePlace F → ℂ)) : Prop where
  le : A ≤ latO F
  ideal : ∃ I : Ideal (𝓞 F), I ≠ ⊥ ∧ idealLat I ≤ A

/-! ### Scaled lattices and cells -/

/-- `a·L`. -/
def scaleLat (a : F) (L : AddSubgroup (InfinitePlace F → ℂ)) :
    AddSubgroup (InfinitePlace F → ℂ) :=
  L.map (AddMonoidHom.mulLeft (emb a))

/-- `a·D`. -/
def scaleSet (a : F) (D : Set (InfinitePlace F → ℂ)) : Set (InfinitePlace F → ℂ) :=
  (fun y => emb a * y) '' D

/-! ### Coefficients over cells of admissible lattices -/

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_U
/-! # WP-F, file 3: Proposition 5.4 integrated against a character over a cell

`U_coeff`: for `Re s > 2`, a cell `D` of `Λ_M` (`M ≥ 0` valid for `(Φ, μ)`), `a = π³`:

`N_∞(π)^{3s/2}·[q^{3−3s} ∫_{aD} E_{Ψ♯} χ_{μ/a} + (1 − q^{2−3s}) ∫_{aD} E_{Ψ♯ρ_∞} χ_{μ/a}]
   = N_∞(a)·1[π³ ∣ μ]·q³·∫_D E_Ψ(·, v/|a|) χ_μ`

(`FB.U_eis_gen` integrated; the left side by linearity, the right side by `FB.coeff_U_gen`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

include h in
lemma gen_coe_ne_zero : (g.gen v.asIdeal : F) ≠ 0 := T.coe_ne_zero (gen_ne_zero h g)

/-- The right-hand side of Proposition 5.4 (`FB.U_eis_gen`) without the factor `N_∞(π)^{3s/2}`. -/
def rhs54 (s : ℂ) (Q : X F) : ℂ :=
  (Ideal.absNorm v.asIdeal : ℂ) ^ (3 - 3 * s)
      * eis ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6) s Q
    + (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (2 - 3 * s))
      * eis (TSection.restrict v (not_le_of_good h)
          ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) s Q

/-- `T` is a complete set of representatives of `R/π³R` for which Proposition 5.4 holds. -/
def IsU (T : Finset (SInt 𝔪)) : Prop :=
  IsReps (g.gen v.asIdeal ^ 3) T ∧ ∀ s : ℂ, 2 < s.re → ∀ Q : X F,
    FB.U ((g.gen v.asIdeal : F) ^ 3) (pow_ne_zero 3 (gen_coe_ne_zero h g)) T
        (eis (Φ.twist hG hz6) s) Q
      = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) * rhs54 hG hz6 h g Φ s Q

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.N2_Lattice
/-! # WP-N2, file 1: independence of `mD` and `zRes` from the auxiliary choices `(Γ, D, n)`

* `avg_eq_of_le` (abstract): for additive subgroups `Λ₂ ≤ Λ₁` of a measurable group, a strict
  fundamental set `D₁` of `Λ₁` and an (a.e.) fundamental domain `D₂` of `Λ₂` of finite measure, the
  mean of a `Λ₁`-periodic function over `D₂` is its mean over `D₁`.  (The union of the translates
  of `D₁` by coset representatives is a strict fundamental set of `Λ₂`; finiteness of the index is
  a consequence of `μ D₂ < ∞`.)
* `exists_strict_cell`: every finite-index `Γ` has a bounded measurable *strict* fundamental set of
  its translation lattice.
* **`mD_congr`**: `mD D Ψ s` (`Re s > 2`) does not depend on the group fixing `Ψ` nor on the cell.
* **`zRes_congr`**: `zRes Γ Ψ D n` does not depend on `(Γ, D, n)` (`n ≥ 1`); so `z_Ψ` is intrinsic
  (WP-N open item 4; the intrinsic value `zPsi` is in `N2_Cor`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### Fundamental domains of a subgroup and of a subgroup of it -/

section abstract

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] {μ : Measure E}
  [μ.IsAddLeftInvariant]

/-- The union of the translates of `D₁` by representatives of `Λ₁ / Λ₂`. -/
def unionDom (Λ₁ Λ₂ : AddSubgroup E) (D₁ : Set E) : Set E :=
  ⋃ q : Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁, (fun x => -((q.out : Λ₁) : E) + x) ⁻¹' D₁

end abstract

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Strict cells -/

/-- Every finite-index subgroup has a bounded measurable strict fundamental set of its
translations (the `D` of `X2_Lattice`, with an integer bound). -/
theorem exists_strict_cell (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    ∃ (D : Set (InfinitePlace F → ℂ)) (n₀ : ℕ), MeasurableSet D ∧
      (∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D) ∧
      (∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) ∧ 1 ≤ n₀ ∧ Cell Γ D n₀ := by
  obtain ⟨D, hD, hb, hfund⟩ := exists_fundamental_translations Γ (exists_ideal_translations Γ)
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have hbd : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ ((N + 1 : ℕ) : ℝ) := fun x hx w =>
    (norm_le_pi_norm x w).trans ((hR x hx).trans (hN.trans (by push_cast; linarith)))
  exact ⟨D, N + 1, hD, hfund, hbd, Nat.le_add_left 1 N, Cell.of_hfund hD hfund hbd⟩

/-! ### Periodicity of the tail -/

/-! ### Independence of `mD` -/

/-! ### Independence of `zRes` -/

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.N2_Unfold
/-! # WP-N2, file 2: the analysis at a cusp (step 4 of stub N-1)

Setting (`CuspSetup`): `τ ∈ SL₂(F)`, a subgroup `K ≤ Γ` such that `τ K τ⁻¹` is upper triangular
and preserves the height (the stabilizer of the cusp `τ⁻¹∞`), and a group `Γ₂` with a bounded
strict fundamental set `D₂` of its translations, all of whose translations `n(β)` are of the form
`τ k τ⁻¹`, `k ∈ K`.

**`integral_cusp_eq_zero`**: if `u` is `K`-invariant and all constant-term functionals
`cf D₂ n φ` kill `u ∘ τ⁻¹`, then `∫_{K\X} c(ht(τP)) u(P) = 0` for every bounded measurable profile
`c` (the integral over `K\X` taken with any partition of unity of `K`).

Proof: unfold from `K` to the translation subgroup `K₂ = K ∩ τ⁻¹ N(Γ₂) τ` (`transSub`), whose
partition of unity is the indicator of the strip `{x(τP) ∈ D₂}`.  In place of a partition of unity
for the unit part acting on `v` (WP-N's route) the test function is
`ψ_n(P) = 1[v(τP) ∈ vBox n] / B_n(v(τP))`, `B_n(v) = #{q ∈ K/K₂ : q⁻¹·v ∈ vBox n}`; then
`Σ_{K₂\K} ψ_n = 1[0 < B_n < ∞]`, `B_n` is finite by proper discontinuity and positive for large
`n`, and `ψ_n` is a function of `v(τP)` alone.  Dominated convergence in `n`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### Pointwise unfolding -/

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The translation subgroup of a cusp stabilizer -/

/-- The elements `k` of `K` with `τ k τ⁻¹` a translation of `Γ₂`. -/
def transSub (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) : Subgroup K where
  carrier := {k | ∃ γ : GammaN Γ₂,
    τ * intSL F ((k : Γ) : SL(2, 𝓞 F)) = intSL F ((γ : Γ₂) : SL(2, 𝓞 F)) * τ}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ⟩ ⟨γ', hγ'⟩
    refine ⟨γ * γ', ?_⟩
    simp only [Subgroup.coe_mul, map_mul]
    rw [← mul_assoc, hγ, mul_assoc, hγ', mul_assoc]
  inv_mem' := by
    rintro a ⟨γ, hγ⟩
    refine ⟨γ⁻¹, ?_⟩
    simp only [Subgroup.coe_inv, map_inv]
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hγ, mul_assoc, mul_inv_cancel, mul_one]

/-- The data at a cusp `τ⁻¹∞`. -/
structure CuspSetup (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F)))
    (D₂ : Set (InfinitePlace F → ℂ)) (n₂ : ℕ) : Prop where
  upper : ∀ k : K, (τ * intSL F ((k : Γ) : SL(2, 𝓞 F)) * τ⁻¹) 1 0 = 0
  ht_inv : ∀ (k : K) (P : X F), X.ht (τ • (k • P)) = X.ht (τ • P)
  meas : MeasurableSet D₂
  fund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ₂, (fun w => x w + GammaN.shift γ w) ∈ D₂
  bdd : ∀ x ∈ D₂, ∀ w, ‖x w‖ ≤ n₂
  lift : ∀ γ : GammaN Γ₂, ∃ k : K,
    τ * intSL F ((k : Γ) : SL(2, 𝓞 F)) = intSL F ((γ : Γ₂) : SL(2, 𝓞 F)) * τ

variable {τ : SL(2, F)} {K : Subgroup Γ} {Γ₂ : Subgroup (SL(2, 𝓞 F))}
  {D₂ : Set (InfinitePlace F → ℂ)} {n₂ : ℕ}

/-- The scaling factors of `k ∈ K` on `v(τP)`. -/
def sc (τ : SL(2, F)) (k : K) (w : InfinitePlace F) : ℝ :=
  Complex.normSq (w.embedding ((τ * intSL F ((k : Γ) : SL(2, 𝓞 F)) * τ⁻¹) 0 0))

/-- The strip `{x(τP) ∈ D₂}`. -/
def stripS (τ : SL(2, F)) (D₂ : Set (InfinitePlace F → ℂ)) : Set (X F) :=
  (fun P : X F => (τ • P).x) ⁻¹' D₂

/-- The set `{v(τP) ∈ vBox n}`. -/
def Sv (τ : SL(2, F)) (n : ℕ) : Set (X F) := (fun P : X F => (τ • P).v) ⁻¹' vBox F n

/-! ### The multiplicity `B_n` -/

/-- `B_n(v) = #{q ∈ K/K₂ : q⁻¹·v ∈ vBox n}`. -/
def Bn (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ)
    (v : InfinitePlace F → ℝ) : ℝ≥0∞ :=
  ∑' q : K ⧸ transSub τ K Γ₂,
    (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) (fun w => sc τ (q.out)⁻¹ w * v w)

/-! ### The test functions -/

/-- `ψ_n(P) = 1[v(τP) ∈ vBox n] / B_n(v(τP))`. -/
def psiN (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (P : X F) : ℂ :=
  (Sv τ n).indicator (fun _ => (1 : ℂ)) P * ((((Bn τ K Γ₂ n (τ • P).v)⁻¹).toReal : ℝ) : ℂ)

/-- `χ_n(P) = 1[0 < B_n(v(τP)) < ∞]`. -/
def chiN (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (P : X F) : ℂ :=
  (((Bn τ K Γ₂ n (τ • P).v).toReal * ((Bn τ K Γ₂ n (τ • P).v)⁻¹).toReal : ℝ) : ℂ)

/-! ### The main statement at a cusp -/

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.N2_Cusp
/-! # WP-N2, file 3: the cusp `σ⁻¹∞` of a finite-index `Γ` (step 3 of stub N-1)

For `σ ∈ SL₂(R)`, `p₀ = rowClass (Row.bot σ)` (the class with `ht_{p₀}(P) = ht(σP)/‖p₀‖`) and
`K = stab Γ p₀`:

* `exists_ideal_conj`: `σ Γ σ⁻¹` contains the translations by a nonzero ideal of `𝓞_F`.
* `cuspSetup`: the `CuspSetup` of file 2 for `τ = σ`, `K`, the group
  `Γ₂ = Γ' ⊓ Γ(𝔫)` and a strict cell of it (`Γ'` any group, `𝔫` from `exists_ideal_conj`).
* **`cusp_integral_eq_zero`**: if the constant term of `θ_Γ(Ψ)` vanishes at the cusp `σ⁻¹∞`
  (`N.CuspVanish`), then `∫_{K\X} c(ht(σP)) θ(P) = 0` for every bounded measurable `c`.
  The passage from the cell of `CuspVanish` to the cell of `Γ₂` is `zRes_congr`.
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

/-- The stabilizer in `Γ` of a pair class. -/
def stab (Γ : Subgroup (SL(2, 𝓞 F))) {S : Finset (FinitePlace F)} (p : PairClass S) :
    Subgroup Γ where
  carrier := {γ | p.act (γ : SL(2, 𝓞 F)) = p}
  one_mem' := by
    change p.act ((1 : Γ) : SL(2, 𝓞 F)) = p
    rw [Subgroup.coe_one, PairClass.act_one]
  mul_mem' := by
    intro a b ha hb
    change p.act ((a * b : Γ) : SL(2, 𝓞 F)) = p
    rw [Subgroup.coe_mul, PairClass.act_mul, ha, hb]
  inv_mem' := by
    intro a ha
    change p.act ((a⁻¹ : Γ) : SL(2, 𝓞 F)) = p
    have h1 : p.act (a : SL(2, 𝓞 F)) = p := ha
    conv_lhs => rw [← h1]
    rw [Subgroup.coe_inv, ← PairClass.act_mul, mul_inv_cancel, PairClass.act_one]

/-! ### The class of a bottom row -/

end

end ArtinKP.N2
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

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Orbits of pair classes -/

/-- The orbit relation of `Γ` on pair classes. -/
def orbSetoid (Γ : Subgroup (SL(2, 𝓞 F))) (S : Finset (FinitePlace F)) :
    Setoid (PairClass S) where
  r p q := ∃ γ ∈ Γ, q = p.act γ
  iseqv := ⟨fun p => ⟨1, Γ.one_mem, (PairClass.act_one p).symm⟩,
    fun ⟨γ, hγ, h⟩ => ⟨γ⁻¹, Γ.inv_mem hγ, by
      rw [h, ← PairClass.act_mul, mul_inv_cancel, PairClass.act_one]⟩,
    fun ⟨γ, hγ, h⟩ ⟨γ', hγ', h'⟩ => ⟨γ * γ', Γ.mul_mem hγ hγ', by
      rw [h', h, PairClass.act_mul]⟩⟩

/-- The `Γ`-orbits of pair classes (the cusps of `Γ`). -/
abbrev Orb (Γ : Subgroup (SL(2, 𝓞 F))) (S : Finset (FinitePlace F)) : Type _ :=
  Quotient (orbSetoid Γ S)

/-- The orbit of a class. -/
def orbOf (Γ : Subgroup (SL(2, 𝓞 F))) {S : Finset (FinitePlace F)} (p : PairClass S) :
    Orb Γ S := Quotient.mk (orbSetoid Γ S) p

lemma orbOf_act (Γ : Subgroup (SL(2, 𝓞 F))) {S : Finset (FinitePlace F)} (p : PairClass S)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Γ) : orbOf Γ (p.act γ) = orbOf Γ p :=
  (Quot.sound (⟨γ, hγ, rfl⟩ : (orbSetoid Γ S).r p (p.act γ))).symm

lemma exists_of_orbOf_eq {Γ : Subgroup (SL(2, 𝓞 F))} {S : Finset (FinitePlace F)}
    {p q : PairClass S} (h : orbOf Γ p = orbOf Γ q) : ∃ γ ∈ Γ, q = p.act γ :=
  Quotient.exact (s := orbSetoid Γ S) h

/-- An orbit is `stab \ Γ`. -/
def orbEquiv (Γ : Subgroup (SL(2, 𝓞 F))) {S : Finset (FinitePlace F)} (p₀ : PairClass S) :
    (Γ ⧸ stab Γ p₀) ≃ {p : PairClass S // orbOf Γ p = orbOf Γ p₀} :=
  Equiv.ofBijective
    (fun q => ⟨p₀.act (((q.out)⁻¹ : Γ) : SL(2, 𝓞 F)), orbOf_act Γ p₀ ((q.out)⁻¹ : Γ).2⟩) (by
    constructor
    · intro a b hab
      have h : p₀.act (((a.out)⁻¹ : Γ) : SL(2, 𝓞 F)) = p₀.act (((b.out)⁻¹ : Γ) : SL(2, 𝓞 F)) :=
        congrArg Subtype.val hab
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      refine QuotientGroup.eq.mpr ?_
      change p₀.act (((a.out)⁻¹ * b.out : Γ) : SL(2, 𝓞 F)) = p₀
      rw [Subgroup.coe_mul, PairClass.act_mul, h, ← PairClass.act_mul, ← Subgroup.coe_mul,
        inv_mul_cancel, Subgroup.coe_one, PairClass.act_one]
    · rintro ⟨p, hp⟩
      obtain ⟨γ, hγ, rfl⟩ := exists_of_orbOf_eq hp.symm
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (stab Γ p₀) (⟨γ, hγ⟩ : Γ)⁻¹
      refine ⟨QuotientGroup.mk (⟨γ, hγ⟩ : Γ)⁻¹, Subtype.ext ?_⟩
      change p₀.act (((QuotientGroup.mk (s := stab Γ p₀) (⟨γ, hγ⟩ : Γ)⁻¹).out⁻¹ : Γ) :
        SL(2, 𝓞 F)) = p₀.act γ
      rw [hk, mul_inv_rev, inv_inv, Subgroup.coe_mul, PairClass.act_mul]
      have hk' : p₀.act (((k : Γ)⁻¹ : Γ) : SL(2, 𝓞 F)) = p₀ := (stab Γ p₀).inv_mem k.2
      rw [hk'])

/-! ### The pseudo-Eisenstein series by orbits -/

open Classical in
/-- The indicator weight of an orbit. -/
def aOrb {Γ : Subgroup (SL(2, 𝓞 F))} {S : Finset (FinitePlace F)} (o : Orb Γ S)
    (p : PairClass S) : ℂ := if orbOf Γ p = o then 1 else 0

/-! ### `L¹` bounds -/

/-! ### One orbit -/

/-! ### Cusp representatives -/

lemma exists_bot_rowClass (h𝔪 : 𝔪 ≠ ⊥) (p : PairClass (RO.SOf 𝔪)) :
    ∃ σ : SL(2, SInt 𝔪), RO.rowClass h𝔪 (Row.bot σ) = p := by
  obtain ⟨r, rfl⟩ := RO.rowClass_surjective h𝔪 p
  obtain ⟨σ, hσ⟩ := Row.exists_bot r
  exact ⟨σ, by rw [hσ]⟩

/-- A matrix `σ ∈ SL₂(R)` with the cusp `σ⁻¹∞` in the orbit `o` (bottom row in the class
`o.out`). -/
def cuspMat (h𝔪 : 𝔪 ≠ ⊥) (Γ : Subgroup (SL(2, 𝓞 F))) (o : Orb Γ (RO.SOf 𝔪)) : SL(2, SInt 𝔪) :=
  (exists_bot_rowClass h𝔪 o.out).choose

/-! ### Stub N-1 -/

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.N2_Cor
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

/-- A chosen finite-index group fixing `Ψ`. -/
def levelGroup (Ψ : TSection ι 𝔪) : Subgroup (SL(2, 𝓞 F)) :=
  (exists_finiteIndex_inv Pk hG hz6 Ψ).choose

instance levelGroup_finiteIndex (Ψ : TSection ι 𝔪) : (levelGroup Pk hG hz6 Ψ).FiniteIndex :=
  (exists_finiteIndex_inv Pk hG hz6 Ψ).choose_spec.1

/-- A chosen cell of `levelGroup Ψ`. -/
def levelCell (Ψ : TSection ι 𝔪) : Set (InfinitePlace F → ℂ) :=
  (exists_strict_cell (levelGroup Pk hG hz6 Ψ)).choose

/-- Its bound. -/
def levelN (Ψ : TSection ι 𝔪) : ℕ :=
  (exists_strict_cell (levelGroup Pk hG hz6 Ψ)).choose_spec.choose

/-- **The residue `z_Ψ`** of the `ht^{2−s}`-coefficient of the constant term of `E_Ψ` at `∞`
(MATH2 §2.1(d)); independent of all choices by `zRes_eq_zPsi`. -/
def zPsi (Ψ : TSection ι 𝔪) : ℂ :=
  zRes (levelGroup Pk hG hz6 Ψ) Ψ (levelCell Pk hG hz6 Ψ) (levelN Pk hG hz6 Ψ)

end

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.F_Per_Const
/-! # WP-F, file 4: the constant term of `E_{Ψρ_∞}` (Lemma 5.2 for `ρ_∞`, by Proposition 5.4)

MATH2 proves `m_{Φρ_∞} = m_Φ / L_P` by unfolding with a congruence condition.  Here it is read off
from Proposition 5.4 at the frequency `0`: `U E_Φ = N^{3s/2}[q^{3−3s} E_{Φ♯} + (1−q^{2−3s}) E_{Φ♯ρ_∞}]`,
the constant term of `U E_Φ` is `q³` times that of `E_Φ` at height `v/|π³|`, and
`m_{Φ♯} = |π|³ m_Φ`.  Result (`mD_restrict`): for every genuine section `Φ₁`, `Re s > 2`,

  `mD D (restrict (Φ₁.twist)) s = (1 − q^{3−3s})/(1 − q^{2−3s}) · mD D (Φ₁.twist) s`,

and hence `zPsi (restrict Ψ₁) = q/(q+1) · zPsi Ψ₁` (`zPsi_restrict`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

/-! ### Algebra -/

/-- The ratio `1/L_P(s) = (1 − q^{3−3s})/(1 − q^{2−3s})`. -/
def ratio (q s : ℂ) : ℂ := (1 - q ^ 3 * (q ^ (-s)) ^ 3) / (1 - q ^ 2 * (q ^ (-s)) ^ 3)

/-! ### Powers of positive reals -/

/-! ### The constant term of `E_{Φ♯ρ_∞}` over scaled cells -/

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Z
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

/-- `TSection` is an additive commutative monoid (pointwise). -/
instance instAddCommMonoidTSection : AddCommMonoid (TSection ι 𝔪) where
  add := (· + ·)
  zero := 0
  add_assoc a b c := by ext s p; simp [add_assoc]
  zero_add a := by ext s p; simp
  add_zero a := by ext s p; simp
  add_comm a b := by ext s p; simp [add_comm]
  nsmul := nsmulRec

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Kernel
/-! # WP-F, file 6: the Kernel Lemma 5.3

* `translate_restrict_of_dvd`: for `σ ∈ SL₂(R)` with `π ∣ σ₁₀`, `σ·(Ψρ_∞) = (σ·Ψ)ρ_∞`.
* `sum_translate_restrict`: for `π ∤ σ₁₀` and `T₁` representatives of `R/π` fixing `σ·Ψ`,
  `∑_{t ∈ T₁} n(t)·σ·(Ψρ_∞) + (σ·Ψ)ρ_∞ = q • σ·Ψ` (the `q + 1` points of `ℙ¹(R/P)`).
* `zPsi_translate_restrict`: `z_{σ·(Φρ_∞)} = (q/(q+1)) z_{σ·Φ}` for **every** `σ ∈ SL₂(R)`
  (MATH2 §5.2: "the finite identities among the `z_η`").
* **`kernel`**: `θ_{Φρ_∞} = (q/(q+1)) θ_Φ` (Corollary N, `N2.theta_eq_zero_iff`).

MATH2 obtains the finite cusps from an unfolding with the lattice `Λ ∩ πR`; here they follow from
the cusp `∞` (`zPsi_restrict`), linearity of `z`, and `z_{n(t)·Ψ} = z_Ψ`.
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

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪)

/-- The constant `q/(q+1)`. -/
def cq (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  (Ideal.absNorm v.asIdeal : ℂ) / ((Ideal.absNorm v.asIdeal : ℂ) + 1)

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Main
/-! # WP-F, file 7: Theorem F1 (cube periodicity) and `E.Theta.PER`

* `Winf_scale`: `W_s(νa; v/|a|) = N_∞(a)^{(s−2)/2} · W_s(ν; v)`.
* `hasCoefT_restrict`: the `ν`-th Fourier coefficient of `E_{Φ♯ρ_∞}` over the cell `π³D`, from
  Proposition 5.4 (`U_coeff`): the coefficient series is
  `(1 − q^{2−3s})⁻¹ · (q³ N_∞(π)⁻³ 𝔞_Φ(νπ³, s) − q^{3−3s} 𝔞_{Φ♯}(ν, s))`.
* **`tau_sharp`** (Theorem F1): `τ_{Φ♯}(ν) = |π|_{S_f}³ · τ_Φ(νπ³)`.
* **`per`**: `(T.theta hG hz6).PER (g.gen P)`.
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

/-! ### Scaling of the archimedean factor -/

/-! ### Algebra -/

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

/-- The coefficient series of `E_{Φ♯ρ_∞}` at the frequency `ν`. -/
def bR (ν : SInt 𝔪) (s : ℂ) : ℂ :=
  (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ 2 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 3)⁻¹
    * ((Ideal.absNorm v.asIdeal : ℂ) ^ 3 * ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ)⁻¹ ^ 3
        * (kubota hG hz6).aSer Φ (ν * g.gen v.asIdeal ^ 3) s
      + (-((Ideal.absNorm v.asIdeal : ℂ) ^ 3 * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 3))
        * (kubota hG hz6).aSer (Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)) ν s)

end gen

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.G1_FI
/-!
# WP-G1, part 5: Lemma FI — finite Fourier inversion on the dual lattices

For an `S_f`-character `ψ` with bounded dual lattices (`HasDual ψ d₀`; for `ψ_{S_f}` this is
`psiS_dual`), `A_M = {β : ψ(β 𝔩_M) = 1}`:

* `sum_char`: orthogonality.  For `β ∈ A_M` and `J ≤ M`,
  `Σ_{t ∈ 𝔩_J/𝔩_M} ψ(βt) = [𝔩_J : 𝔩_M]·1[β ∈ A_J]`.
* `exists_fourier` — **Lemma FI** (MATH3 §4.4): every function on `A_M` invariant under
  translation by `A_J` (`J ≤ M`) is a finite trigonometric polynomial
  `β ↦ Σ_{t ∈ T} ϕ(t) ψ(βt)` with frequencies `T ⊂ 𝔩_J`.
* `exists_fourier_indicator`: the indicator of a coset `β₁ + 𝔩_k` (any depth function `k`),
  restricted to `A_M` — the form used for (G2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem SfChar.map_neg' (ψ : SfChar 𝔪) (x : F) : ψ (-x) = conj (ψ x) := by
  have h : ψ x * ψ (-x) = 1 := by rw [← ψ.map_add, add_neg_cancel, ψ.map_zero]
  have h0 : ψ x ≠ 0 := left_ne_zero_of_mul_eq_one h
  rw [← Complex.inv_eq_conj (ψ.norm_one x)]
  exact eq_inv_of_mul_eq_one_right h

/-- The dual lattice `A_M` as a subgroup of `F`. -/
def dualLat (ψ : SfChar 𝔪) (M : ℤ) : AddSubgroup F where
  carrier := {β | Adual ψ M β}
  zero_mem' := fun h _ => by rw [zero_mul]; exact ψ.map_zero
  add_mem' := fun {a b} ha hb h hh => by rw [add_mul, ψ.map_add, ha h hh, hb h hh, one_mul]
  neg_mem' := fun {a} ha h hh => by
    rw [neg_mul, SfChar.map_neg', ha h hh, map_one]

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Delta
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-!
# WP-G1, part 8: the delta section (MATH3 §1.2 (G1)–(G3), §5 (C10)), as far as it is algebra

For `D = B.kubota hG hz6`, `T : E.Theta D (4/3)`:

* `exists_Kir_adual`: `𝒦_Φ(β) ≠ 0 → β ∈ A_N` (support in a dual lattice; no class decomposition
  and no scalar law needed).
* `exists_delta` — **the delta section**: if the Kirillov function of *some* section is not
  identically zero (hypothesis `hne`, the analytic input (C9)+(C10′)+Theorem E of MATH3 (G1)),
  then for every `k` with `k + 1` deep there is `Φ₀` with
  `𝒦_{Φ₀}(β) = 1[β ∈ 1 + 𝔩_{k+1}]` for all `β ∈ F^×` (`= 1_{U_k}`, `U_k = SLevel 𝔪 k`), and
  `ξ_{Φ₀}` is the same function (`xi_delta`).
  Construction: additive projection `Φ₂ = Σ_t ϕ(t) n(t) Φ₁` by Lemma FI, then
  `Φ₀ = 𝒦_{Φ₁}(β₁)⁻¹ Σ_j Ã(β₁/u_j) Φ₂`, `u_j = 1 + a_j`, `a_j` running over `𝔩_{k+1}/𝔩_{K'}`.
* `KW T`: the statement of MATH3's Lemma KW (`𝒦_Φ ≡ 0 ⇒ 𝒦_{wΦ} ≡ 0`).  It is **not** section
  level (its proof needs (Exp), (Aut), (C10′) and Theorem E); it is a named hypothesis here.
* `Kir_w_delta_inv` — **(INV)** of MATH3 §4.2, from `KW`: `𝒦_{wΦ₀}(βu) = 𝒦_{wΦ₀}(β)` for
  `u ∈ 1 + 𝔩_{k+1}`, `Φ₀` a delta section.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

/-! ### Lemma KW as a hypothesis, and (INV) -/

/-- **The statement of MATH3's Lemma KW**: the kernel of the Kirillov map is `w`-stable.
Not a section-level fact: MATH3's proof uses the theta function (`(Exp)`: its Fourier expansion with
coefficients `τ`; `(Aut)`: automorphy under `w`; `(C10′)`: all `τ_Φ(ν) = 0 ⇒ θ̃_Φ = 0`) and
Theorem E (`τ_Φ(ν) = N(ν)^{1/3} coef(ν) 𝒦_Φ(ν)`). -/
def KW : Prop :=
  ∀ Φ : GSection ι P 𝔪, (∀ β : F, β ≠ 0 → Kir hG hz6 T Φ β = 0) →
    ∀ β : F, β ≠ 0 → Kir hG hz6 T (wSec hG Φ) β = 0

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.T12.L3X_Meas
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

instance instDiscrSFin : DiscreteMeasurableSpace (SFin 𝔪 k) := ⟨fun _ => trivial⟩

/-! ### The finite norm -/

/-! ### `lnorm` -/

/-- `log |y|_S`. -/
noncomputable def lnorm (y : SModel 𝔪 k) : ℝ := ∑ w, y.1 w + Real.log y.2.2.norm

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3J_Kappa
/-! # L3J_Kappa: the κ-clauses of the corrected KP cut are satisfiable

`κ₀(t) = ∫ g_{5/6}(log t − y) g_{7/6}(y) dy`, with `g_a(b) = exp(a b − e^b)`, is the Mellin
convolution of `t^{5/6} e^{-t}` and `t^{7/6} e^{-t}`. So `mellin κ₀ s = Γ(s+5/6) Γ(s+7/6)` for
`Re s > −5/6`, and `κ₀(t) ≤ C_N min(t^α, t^{-N})` for every `0 < α ≤ 5/6` and every `N > 0`.
It is the archimedean Whittaker profile `t K_{1/3}(2√t)` of (5.7)/(5.11), up to normalization. -/

namespace ArtinPrimitiveRoots.L3J

open MeasureTheory Set

noncomputable section

/-- `g_a(b) = exp(a b − e^b)`. -/
def gA (a b : ℝ) : ℝ := Real.exp (a * b - Real.exp b)

/-- The profile `κ₀`. -/
def kappa0 (t : ℝ) : ℝ := ∫ y, gA (5 / 6) (Real.log t - y) * gA (7 / 6) y

end

end ArtinPrimitiveRoots.L3J
end

section
-- module Solutions.Artin.KP.K_Kappa
/-! # WP-K, file 3: the profile `κ`

* `cc a b x = ∫ g_a(x−y) g_b(y) dy` (`g_a(u) = exp(a u − e^u)`, `L3J.gA`): the Mellin convolution of
  `t^a e^{−t}` and `t^b e^{−t}` in the variable `x = log t`; `L3J.kappa0 (e^x) = cc (5/6) (7/6) x`.
  `hasDerivAt_cc`: `cc a b ' = a · cc a b − cc (a+1) b`; `contDiff_cc`: smooth;
  `cc_bound`: `cc a b x ≤ C min(e^{αx}, e^{−Nx})` for `a ≠ b`, `0 < α ≤ min a b`.
* `kappa0_eq_bessel`: `κ₀(t) = 2 t K_{1/3}(2√t)`.
* `kappaB c t = t · K_{1/3}(c √t)` (`t > 0`; `0` otherwise) `= (2/c²) κ₀(c² t/4)`;
  `kappaB_clauses`: all `κ`-clauses of the frozen goal with `cκ = 2/c²`, `Aκ = (c²/4)⁻¹ = 4/c²`
  (for `c = 4π`: `cκ = 1/(8π²)`, `Aκ = 1/(4π²)`).
* `kappaB_contDiff`, `kappaB_iteratedDeriv_bound`, `kappaB_iteratedDeriv_bound_shift`,
  `kappaB_ofReal_iteratedDeriv_bound_shift`: `s ↦ κ(e^{x+s})` is smooth and its derivatives of
  order `≤ 2` are `≤ C min(e^{αx}, e^{−Nx})`, `0 < α ≤ 5/6`, any `N > 0`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open ArtinPrimitiveRoots.L3J (gA kappa0 )

noncomputable section

/-! ## The functions `g_a` -/

/-! ## The family `cc a b` -/

/-- `cc a b x = ∫ g_a(x − y) g_b(y) dy`. -/
def cc (a b x : ℝ) : ℝ := ∫ y, gA a (x - y) * gA b y

/-! ## Bounds for `cc a b` -/

/-! ## `κ₀` is a K-Bessel function -/

/-! ## The Bessel profile `κ(t) = t K_{1/3}(c√t)` -/

/-- `κ(t) = t · K_{1/3}(c √t)` for `t > 0`, and `0` for `t ≤ 0`. -/
def kappaB (c t : ℝ) : ℝ := if 0 < t then t * besselKR (1 / 3) (c * Real.sqrt t) else 0

/-! ## Smoothness and derivative bounds in the logarithmic variable -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.G2a_Bessel
/-! # WP-G2a, file 10: the `v`-derivative of the Jacquet integral at `s = 4/3`

* `cc_shift`: `cc (a+c) (b+c) x = e^{cx}·cc a b x`; **`zK_eq_cc`**: `z·K_{1/3}(z) = cc (1/3) (2/3) (2 log (z/2))`
  (the lemma "of the type `kappa0_eq_bessel`" that WP-K left open; MATH3 §5.2 (ii)).
* `jacquet_eq_cc`, **`hasDerivAt_jacquet`**: `v ↦ jacquet (4/3) a v` is differentiable on `v > 0`
  with derivative `jd a v` (from `K.hasDerivAt_cc`).
* `grid_decay`: the uniform bound used for both the function and its derivative;
  **`jd_bound`**: `|a|^{2/3}(1+|a|)^p·|jd a v| ≤ K (1+|a|)^{-4}` for `v` in a compact of `(0, ∞)`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B ArtinKP.RF ArtinPrimitiveRoots

noncomputable section

/-- The constant of `jacquet_eq_cc`. -/
def c1 : ℂ := (2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) *
  (((2 * Real.pi) ^ (1 / 3 : ℝ) * (4 * Real.pi)⁻¹ : ℝ) : ℂ)

/-- The real profile: `|a|^{-2/3}·cc (1/3) (2/3) (2 log (2π|a|t))`. -/
def jr (n t : ℝ) : ℝ := n ^ (-(2 / 3 : ℝ)) * cc (1 / 3) (2 / 3) (2 * Real.log (2 * Real.pi * n * t))

/-- The derivative of `t ↦ jacquet (4/3) a t`. -/
def jd (a : ℂ) (v : ℝ) : ℂ :=
  c1 * ((‖a‖ ^ (-(2 / 3 : ℝ)) *
    ((1 / 3 * cc (1 / 3) (2 / 3) (2 * Real.log (2 * Real.pi * ‖a‖ * v))
      - cc (1 / 3 + 1) (2 / 3) (2 * Real.log (2 * Real.pi * ‖a‖ * v))) * (2 / v)) : ℝ) : ℂ)

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.RF_Parseval
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 9: Parseval along `x` in the form of WP-X stub S1 (a)

For `g : (ι → ℂ) → ℂ` measurable, periodic under the translation lattice `Λ` of `Γ` and square
integrable on a strict fundamental set `D` of `Λ`:

`∑_{ν ∈ Λ^⊥} |∫_D conj(e_ν) g|² = vol(D) · ∫_D |g|²`   (`parseval_strip`).

The sum is over the subtype `dualLat Γ`; `dualEquiv` identifies it with `ℤ^J` for a lattice basis
(`nuOf bV m` is the frequency with `e_ν = chi bV m`).
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

lemma pair_smul (ν x : InfinitePlace F → ℂ) (a : ℝ) : pair ν (a • x) = a * pair ν x := by
  simp only [pair, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-- `pair ν` as a real linear functional. -/
def pairLin (ν : InfinitePlace F → ℂ) : (InfinitePlace F → ℂ) →ₗ[ℝ] ℝ where
  toFun := pair ν
  map_add' := pair_add ν
  map_smul' a x := by simp [pair_smul]

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.H0_Cut
/-! # WP-H0, file 1: the intermediate cut `KPCut` ("one unknown function `J`")

`KPCut n F ι` is the frozen goal 8b3180bd with
* `κ := K.kappaB c` (`t ↦ t·K_{1/3}(c√t)`), for some `c > 0`;
* `Fm cl y' := J cl y'_f · ∏_w e^{−i m_w θ'_w} κ(e^{x'_w})`, for some `J : SFinCls → SFin → ℂ`
  (it may depend on `m`; signs and constants are absorbed in it);
* a majorant `bf ≥ |J|` with the frozen summability clause, for some `0 < α ≤ 5/6`.

All `let`s of the frozen statement (`lsym … Eloc`, `fp`, `coef`, `Ez`, `D`) are copied verbatim
(generated from the `Theorems/` file by `proofs/kp/scratch/h0/gen_cut.py`).
`KPCutEq` is the variant "the two `tsum`s are equal" (`D ≡ 0`); `KPCutEq → KPCut`. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

open Classical in
/-- The intermediate cut: the conclusion of the frozen goal for the explicit `κ` and the
product-form `Fm`; the only unknown is `J` (with its majorant `bf`). -/
def KPCut (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
      if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yz.2 : F) * t = (yz.1 : F) then
        sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
      else 0
    let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
      if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
        sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
      else 0
    let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
      if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
      else if e % 3 = 1 then
        (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
      else 0
    let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
      if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
    let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
          sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
    let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P j v =>
        if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
        else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
    let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P e₀ t v =>
        if e₀ + 2 < 0 then 0 else
          Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
            sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
            ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
      if k = 0 then Wsph P e₀ t else
        ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
          mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (c α : ℝ), 0 < c ∧ 0 < α ∧ α ≤ 5 / 6 ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ cl y, ‖J cl y‖ ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
    ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 →
    let κ : ℝ → ℝ := K.kappaB c
    let Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ := fun cl y =>
      J cl y.2.2 *
        ∏ w, ((AddCircle.toCircle ((-m w) • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
    let fp : SModel 𝔪 k → ℂ := fun y =>
      if y.2.2 = 0 then
        ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
      else 0
    let coef : RowClass 𝔪 → ℂ := fun z =>
      residueSymbol ι 𝔪 𝔟 (rowElt g z) *
        ∏ P ∈ (normalizedFactors z.1.1).toFinset,
          Wsph P ((normalizedFactors z.1.1).count P : ℤ)
            ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))
    let Ez : RowClass 𝔪 → ℂ := fun z =>
      (∏ P ∈ (normalizedFactors (z.1.1 * 𝔟)).toFinset,
        Eloc P ((normalizedFactors 𝔟).count P)
          (((normalizedFactors z.1.1).count P : ℤ) -
            2 * ((normalizedFactors 𝔟).count P : ℤ))
          ((rowElt g z : F) / (g.gen 𝔟 : F) ^ 2 *
            (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
              2 * ((normalizedFactors 𝔟).count P : ℤ)))))
    let D : SModel 𝔪 k → ℂ := fun y =>
      (∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y)) -
        ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)) - y)
    ∀ (w : InfinitePlace F) (φ : AddCircle (2 * Real.pi)) (y : SModel 𝔪 k),
      D (y + ((0, Pi.single w φ, 0) : SModel 𝔪 k)) = D y

open Classical in
/-- The strong form of the cut: the two sums are equal (both constant terms vanish). -/
def KPCutEq (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    let lsym : Ideal (𝓞 F) → F → ℂ := fun P t =>
      if h : ∃ yz : SInt 𝔪 × SInt 𝔪, yz.2 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yz.2 : F) * t = (yz.1 : F) then
        sexticResidueSymbol ι 𝔪 P h.choose.1 * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P h.choose.2)
      else 0
    let ladd : Ideal (𝓞 F) → F → ℂ := fun P w =>
      if h : ∃ yzr : SInt 𝔪 × SInt 𝔪 × SInt 𝔪, yzr.2.1 ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          yzr.2.2 ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) ∧
          (yzr.2.1 : F) * (w - (yzr.1 : F)) = (yzr.2.2 : F) then
        sAddChar 𝔪 (-((h.choose.1 : F) / (g.gen P : F)))
      else 0
    let Wv : Ideal (𝓞 F) → ℕ → ℂ := fun P e =>
      if e % 3 = 0 then (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ)) : ℝ) : ℂ)
      else if e % 3 = 1 then
        (((Ideal.absNorm P : ℝ) ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) * gaussPhase g 2 P
      else 0
    let Wsph : Ideal (𝓞 F) → ℤ → F → ℂ := fun P e₀ t =>
      if e₀ < 0 then 0 else lsym P t ^ (2 * e₀.toNat) * Wv P e₀.toNat
    let tau : Ideal (𝓞 F) → ℕ → ℂ := fun P j =>
      ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
        starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j *
          sAddChar 𝔪 (-((quotLift v : F) / (g.gen P : F)))
    let mask : (P : Ideal (𝓞 F)) → ℕ → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P j v =>
        if j = 0 then (if v = 0 then 1 - (Ideal.absNorm P : ℂ)⁻¹ else -(Ideal.absNorm P : ℂ)⁻¹)
        else (tau P j)⁻¹ * starRingEnd ℂ (sexticResidueSymbol ι 𝔪 P (quotLift v)) ^ j
    let Wweyl : (P : Ideal (𝓞 F)) → ℤ → F → (SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪))) → ℂ :=
      fun P e₀ t v =>
        if e₀ + 2 < 0 then 0 else
          Wv P (e₀ + 2).toNat * lsym P t ^ (4 + 2 * (e₀ + 2).toNat) *
            sexticResidueSymbol ι 𝔪 P (quotLift v) ^ 4 *
            ladd P ((g.gen P : F) ^ (e₀ + 2).toNat * t / (quotLift v : F))
    let Eloc : Ideal (𝓞 F) → ℕ → ℤ → F → ℂ := fun P k e₀ t =>
      if k = 0 then Wsph P e₀ t else
        ∑ᶠ v : SInt 𝔪 ⧸ P.map (algebraMap (𝓞 F) (SInt 𝔪)),
          mask P (k % 6) v * (if v = 0 then Wsph P e₀ t else Wweyl P e₀ t v)
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (c α : ℝ), 0 < c ∧ 0 < α ∧ α ≤ 5 / 6 ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ cl y, ‖J cl y‖ ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
    ∀ 𝔟 : Ideal (𝓞 F), IsExterior 𝔪 𝔟 →
    let κ : ℝ → ℝ := K.kappaB c
    let Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ := fun cl y =>
      J cl y.2.2 *
        ∏ w, ((AddCircle.toCircle ((-m w) • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
    let fp : SModel 𝔪 k → ℂ := fun y =>
      if y.2.2 = 0 then
        ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
      else 0
    let coef : RowClass 𝔪 → ℂ := fun z =>
      residueSymbol ι 𝔪 𝔟 (rowElt g z) *
        ∏ P ∈ (normalizedFactors z.1.1).toFinset,
          Wsph P ((normalizedFactors z.1.1).count P : ℤ)
            ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))
    let Ez : RowClass 𝔪 → ℂ := fun z =>
      (∏ P ∈ (normalizedFactors (z.1.1 * 𝔟)).toFinset,
        Eloc P ((normalizedFactors 𝔟).count P)
          (((normalizedFactors z.1.1).count P : ℤ) -
            2 * ((normalizedFactors 𝔟).count P : ℤ))
          ((rowElt g z : F) / (g.gen 𝔟 : F) ^ 2 *
            (g.gen P : F) ^ (-(((normalizedFactors z.1.1).count P : ℤ) -
              2 * ((normalizedFactors 𝔟).count P : ℤ)))))
    ∀ y : SModel 𝔪 k,
      ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y) =
        ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
          Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / (g.gen 𝔟 : F) ^ 2)) - y)

end ArtinKP.H0
end

section
-- module Solutions.Artin.T12.L3P_Sfin
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L3P_Sfin: the finite places of `S`, combinatorially

`S` a finite type with `q v > 1`. For `j : S → ℤ`, `NN j = ∏ q_v^{j_v}`. The weight
`Om j = Σ_{e ⊆ S} (−1)^{|e|} 1[j + 1_e ≥ 0] / NN (j + 1_e)` is the profile of the Fourier transform
of `∏_v 1_{𝒪_v^×}` (self-dual normalisation), and
`Σ_j Om j · NN j^{1−z} = ∏_v (1 − q_v^{z−1}) / (1 − q_v^{−z})` for `Re z > 0`.
-/

namespace ArtinPrimitiveRoots.L3P

open scoped BigOperators Classical

set_option linter.unusedSectionVars false

/-! ### Products of geometric series over `S → ℕ` -/

/-! ### The weight `Om` -/

section Om

variable {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ)

/-- `log q_v`. -/
noncomputable def lq (v : S) : ℝ := Real.log (q v)

/-- `NN j = ∏ q_v^{j_v} = exp (Σ j_v log q_v)`. -/
noncomputable def NN (j : S → ℤ) : ℝ := Real.exp (∑ v, (j v : ℝ) * lq q v)

end Om

end ArtinPrimitiveRoots.L3P
end

section
-- module Solutions.Artin.T12.L3P_Val
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L3P_Val: valuations as counts of principal fractional ideals

For `x ≠ 0` in a number field, `v.valuation x = exp (−count_v (x))`, where
`count_v (x) = FractionalIdeal.count F v (spanSingleton x)`. Membership in a nonzero fractional
ideal is a comparison of counts.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

/-- `count_v (x)`. -/
noncomputable def ordv (v : HeightOneSpectrum (𝓞 F)) (x : F) : ℤ :=
  FractionalIdeal.count F v (spanSingleton (𝓞 F)⁰ x)

theorem spanSingleton_ne_zero {x : F} (hx : x ≠ 0) : spanSingleton (𝓞 F)⁰ x ≠ 0 :=
  (spanSingleton_eq_zero_iff).not.2 hx

theorem ordv_algebraMap (v : HeightOneSpectrum (𝓞 F)) {r : 𝓞 F} (hr : r ≠ 0) :
    ordv v (algebraMap (𝓞 F) F r) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors : ℤ) := by
  rw [ordv, ← coeIdeal_span_singleton, count_coe F v]
  rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]

theorem ordv_mul (v : HeightOneSpectrum (𝓞 F)) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordv v (x * y) = ordv v x + ordv v y := by
  rw [ordv, ← spanSingleton_mul_spanSingleton, count_mul F v (spanSingleton_ne_zero hx)
    (spanSingleton_ne_zero hy)]
  rfl

theorem ordv_inv (v : HeightOneSpectrum (𝓞 F)) (x : F) : ordv v x⁻¹ = -ordv v x := by
  rw [ordv, ← spanSingleton_inv, count_inv]; rfl

theorem valuation_eq_exp_neg_ordv (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x = WithZero.exp (-ordv v x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl; simp at hx
  have hrK : algebraMap (𝓞 F) F r ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  rw [div_eq_mul_inv, map_mul, map_inv₀, valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_if_neg _ hr0, intValuation_if_neg _ hs0, ordv_mul v hrK (inv_ne_zero hsK),
    ordv_inv, ordv_algebraMap v hr0, ordv_algebraMap v hs0, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr 1; ring

theorem valuation_le_one_iff (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    v.valuation F x ≤ 1 ↔ 0 ≤ ordv v x := by
  rw [valuation_eq_exp_neg_ordv v hx, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos]

/-- For nonzero fractional ideals, `I ≤ J ↔ ∀ v, count_v J ≤ count_v I`. -/
theorem le_iff_count {I J : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum (𝓞 F), count F v J ≤ count F v I := by
  constructor
  · intro h v; exact count_mono F v hI h
  · intro h
    set K := I * J⁻¹
    have hK : K ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
    have hcount : ∀ v, 0 ≤ count F v K := fun v => by
      rw [count_mul F v hI (inv_ne_zero hJ), count_inv]; linarith [h v]
    have hpow : ∀ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ count F v K =
        coeIdealHom (𝓞 F)⁰ F (v.asIdeal ^ (count F v K).toNat) := fun v => by
      rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hcount v)]; rfl
    have hKle : K ≤ 1 := by
      rw [← finprod_heightOneSpectrum_factorization' F hK]
      simp_rw [hpow]
      have e := MonoidHom.map_finprod_of_injective (coeIdealHom (𝓞 F)⁰ F).toMonoidHom
        coeIdeal_injective (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ (count F v K).toNat)
      calc _ = (coeIdealHom (𝓞 F)⁰ F) (∏ᶠ v : HeightOneSpectrum (𝓞 F),
            v.asIdeal ^ (count F v K).toNat) := e.symm
        _ ≤ 1 := coeIdeal_le_one
    have : I = K * J := by
      simp only [K]; rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    rw [this]
    calc K * J ≤ 1 * J := mul_le_mul_left hKle J
      _ = J := one_mul J

theorem eq_of_count_eq {I J : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), count F v I = count F v J) : I = J :=
  le_antisymm ((le_iff_count hI hJ).2 fun v => (h v).ge) ((le_iff_count hJ hI).2 fun v => (h v).le)

theorem mem_iff_count {x : F} (hx : x ≠ 0) {J : FractionalIdeal (𝓞 F)⁰ F} (hJ : J ≠ 0) :
    x ∈ J ↔ ∀ v : HeightOneSpectrum (𝓞 F), count F v J ≤ ordv v x := by
  rw [← spanSingleton_le_iff_mem, le_iff_count (spanSingleton_ne_zero hx) hJ]; rfl

theorem ordv_add_ge (v : HeightOneSpectrum (𝓞 F)) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (ordv v x) (ordv v y) ≤ ordv v (x + y) := by
  have h := Valuation.map_add (v.valuation F) x y
  rw [valuation_eq_exp_neg_ordv v hx, valuation_eq_exp_neg_ordv v hy,
    valuation_eq_exp_neg_ordv v hxy] at h
  rcases le_total (ordv v x) (ordv v y) with hle | hle
  · rw [min_eq_left hle]
    rw [max_eq_left (WithZero.exp_le_exp.2 (neg_le_neg hle))] at h
    have := WithZero.exp_le_exp.1 h; linarith
  · rw [min_eq_right hle]
    rw [max_eq_right (WithZero.exp_le_exp.2 (neg_le_neg hle))] at h
    have := WithZero.exp_le_exp.1 h; linarith

/-- In a nonzero fractional ideal, the count is attained. -/
theorem exists_mem_ordv_eq {J : FractionalIdeal (𝓞 F)⁰ F} (hJ : J ≠ 0)
    (w : HeightOneSpectrum (𝓞 F)) : ∃ x ∈ J, x ≠ 0 ∧ ordv w x = count F w J := by
  have hw0 : (w.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 w.ne_bot
  have hJw : J * w.asIdeal ≠ 0 := mul_ne_zero hJ hw0
  have hne : ¬ J ≤ J * w.asIdeal := by
    intro h
    have := count_mono F w hJ h
    rw [count_mul F w hJ hw0, count_self] at this
    linarith
  rw [SetLike.not_le_iff_exists] at hne
  obtain ⟨x, hxJ, hxJw⟩ := hne
  have hx0 : x ≠ 0 := by rintro rfl; exact hxJw (zero_mem _)
  refine ⟨x, hxJ, hx0, le_antisymm ?_ (((mem_iff_count hx0 hJ).1 hxJ) w)⟩
  by_contra hlt
  push Not at hlt
  apply hxJw
  rw [mem_iff_count hx0 hJw]
  intro v
  rw [count_mul F v hJ hw0, count_maximal]
  split_ifs with hvw
  · subst hvw; linarith
  · rw [add_zero]; exact (mem_iff_count hx0 hJ).1 hxJ v

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

/-- The finite places of `S`, as a type. -/
abbrev SP (𝔪 : Ideal (𝓞 F)) : Type _ := ↥(placesOf 𝔪)

theorem mem_SInt_iff {x : F} (hx : x ≠ 0) :
    x ∈ (placesOf 𝔪).integer F ↔ ∀ v ∉ placesOf 𝔪, 0 ≤ ordv v x := by
  change (∀ v ∉ placesOf 𝔪, v.valuation F x ≤ 1) ↔ _
  simp only [valuation_le_one_iff _ hx]

/-- The prime `v` as a unit fractional ideal. -/
noncomputable def primeU (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) (coeIdeal_ne_zero.2 v.ne_bot)

/-- The valuation vector at `S`. -/
noncomputable def valS (x : F) : SP 𝔪 → ℤ := fun v => ordv v.1 x

variable [Fintype (SP 𝔪)]

/-- `P^k = ∏_{v ∈ S} 𝔭_v^{k_v}`. -/
noncomputable def Pk (k : SP 𝔪 → ℤ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := ∏ v : SP 𝔪, primeU v.1 ^ k v

theorem coe_Pk (k : SP 𝔪 → ℤ) :
    ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ v : SP 𝔪, (v.1.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ k v := by
  rw [Pk, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val]
  rfl

theorem Pk_ne_zero (k : SP 𝔪 → ℤ) :
    ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := (Pk k).ne_zero

theorem count_Pk (k : SP 𝔪 → ℤ) (w : HeightOneSpectrum (𝓞 F)) :
    count F w ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) =
      if h : w ∈ placesOf 𝔪 then k ⟨w, h⟩ else 0 := by
  rw [coe_Pk, count_prod F w _ _ fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.2 v.1.ne_bot)]
  simp_rw [count_zpow, count_maximal]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨w, h⟩]
    · simp
    · intro v _ hv
      have : v.1 ≠ w := fun e => hv (Subtype.ext e)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun v _ => ?_
    have : v.1 ≠ w := fun e => h (e ▸ v.2)
    simp [this]

omit [Fintype (SP 𝔪)] in
/-- Elements of `𝔟 R` have `w`-adic order at least `count_w 𝔟` outside `S`. -/
theorem ordv_ge_of_mem_map (𝔟 : Ideal (𝓞 F)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ placesOf 𝔪)
    {y : SInt 𝔪} (hy : y ∈ 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) (hy0 : (y : F) ≠ 0) :
    count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ ordv w (y : F) := by
  suffices h : ∀ y ∈ 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪)), (y : F) = 0 ∨
      count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ ordv w (y : F) from (h y hy).resolve_left hy0
  intro y hy
  rw [Ideal.map, Ideal.span] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    by_cases hb0 : b = 0
    · left; simp [hb0]
    · right
      have hbK : algebraMap (𝓞 F) F b ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      have h1 : spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F b) ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [spanSingleton_le_iff_mem]; exact mem_coeIdeal_of_mem _ hb
      have h2 := count_mono F w (spanSingleton_ne_zero hbK) h1
      exact h2
  | zero => left; rfl
  | add x y _ _ hx hy =>
    by_cases hx0 : (x : F) = 0
    · have : ((x + y : SInt 𝔪) : F) = (y : F) := by simp [hx0]
      rw [this]; exact hy
    by_cases hy0 : (y : F) = 0
    · have : ((x + y : SInt 𝔪) : F) = (x : F) := by simp [hy0]
      rw [this]; exact hx
    by_cases hxy : ((x + y : SInt 𝔪) : F) = 0
    · left; exact hxy
    right
    have h1 := hx.resolve_left hx0
    have h2 := hy.resolve_left hy0
    have hxy' : (x : F) + (y : F) ≠ 0 := by simpa using hxy
    have := ordv_add_ge w hx0 hy0 hxy'
    simp only [Subalgebra.coe_add]
    exact (le_min h1 h2).trans this
  | smul r x _ hx =>
    by_cases h0 : ((r • x : SInt 𝔪) : F) = 0
    · left; exact h0
    right
    have hrx : ((r • x : SInt 𝔪) : F) = (r : F) * (x : F) := rfl
    rw [hrx] at h0 ⊢
    have hr0 : (r : F) ≠ 0 := left_ne_zero_of_mul h0
    have hx0 : (x : F) ≠ 0 := right_ne_zero_of_mul h0
    rw [ordv_mul w hr0 hx0]
    have hr : 0 ≤ ordv w (r : F) := (mem_SInt_iff hr0).1 r.2 w hw
    linarith [hx.resolve_left hx0]

omit [Fintype (SP 𝔪)] in
theorem count_eq_zero_of_exterior {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∈ placesOf 𝔪) : count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
  rw [count_coe F w h𝔟.1, Nat.cast_eq_zero]
  by_contra hc
  have hdvd := (Associates.count_ne_zero_iff_dvd h𝔟.1 w.irreducible).1 hc
  have h1 : 𝔟 ≤ w.asIdeal := Ideal.le_of_dvd hdvd
  have h2 : 𝔟 ⊔ 𝔪 ≤ w.asIdeal := sup_le h1 hw
  rw [h𝔟.2, top_le_iff] at h2
  exact w.isPrime.ne_top h2

omit [Fintype (SP 𝔪)] in
theorem ne_zero_of_span_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) : (m : F) ≠ 0 := by
  intro h0
  have hm0 : m = 0 := Subtype.ext h0
  rw [hm0, Ideal.span_singleton_eq_bot.2 rfl] at hm
  apply h𝔟.1
  rw [eq_bot_iff]
  intro b hb
  have : algebraMap (𝓞 F) (SInt 𝔪) b ∈ (⊥ : Ideal (SInt 𝔪)) := hm ▸ Ideal.mem_map_of_mem _ hb
  rw [Ideal.mem_bot] at this
  have h2 : algebraMap (𝓞 F) F b = 0 := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) this
    simpa using this
  rw [Ideal.mem_bot]
  exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 h2

/-- `m R = 𝔟 R` with `𝔟` exterior gives `(m) = 𝔟 · P^{val_S m}` as fractional ideals of `𝓞`. -/
theorem spanSingleton_eq_mul_Pk {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    spanSingleton (𝓞 F)⁰ (m : F) =
      (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * ((Pk (valS (𝔪 := 𝔪) (m : F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
  have hm0 := ne_zero_of_span_eq h𝔟 hm
  have h𝔟0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := coeIdeal_ne_zero.2 h𝔟.1
  refine eq_of_count_eq (spanSingleton_ne_zero hm0) (mul_ne_zero h𝔟0 (Pk_ne_zero _)) fun w => ?_
  rw [count_mul F w h𝔟0 (Pk_ne_zero _), count_Pk]
  change ordv w (m : F) = _
  split_ifs with hw
  · rw [count_eq_zero_of_exterior h𝔟 hw, zero_add]; rfl
  · rw [add_zero]
    refine le_antisymm ?_ (ordv_ge_of_mem_map 𝔟 hw (hm ▸ Ideal.mem_span_singleton_self m) hm0)
    obtain ⟨x, hx, hx0, hxo⟩ := exists_mem_ordv_eq h𝔟0 w
    obtain ⟨b, hb, rfl⟩ := (mem_coeIdeal _).1 hx
    have hbm : algebraMap (𝓞 F) (SInt 𝔪) b ∈ Ideal.span {m} := hm ▸ Ideal.mem_map_of_mem _ hb
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hbm
    have hrF : (r : F) * (m : F) = algebraMap (𝓞 F) F b := by
      have := congrArg (fun z : SInt 𝔪 => (z : F)) hr
      simpa using this
    have hr0 : (r : F) ≠ 0 := by
      intro h; rw [h, zero_mul] at hrF; exact hx0 hrF.symm
    rw [← hxo, ← hrF, ordv_mul w hr0 hm0]
    have := (mem_SInt_iff hr0).1 r.2 w hw
    linarith

/-- `q_v = N 𝔭_v`. -/
noncomputable def qS (v : SP 𝔪) : ℝ := (Ideal.absNorm v.1.asIdeal : ℝ)

/-! ### Units, the different, and the trace dual -/

theorem unit_ne_zero (ε : (SInt 𝔪)ˣ) : ((ε : SInt 𝔪) : F) ≠ 0 := by
  intro h; exact ε.ne_zero (Subtype.ext h)

end ArtinPrimitiveRoots.L3P
end

section
-- module Solutions.Artin.T12.L3X_Rho
/-! # L3X_Rho: a partition of unity for `Γ = U_S⁶` acting on `SModel 𝔪 k`

* `valF : SFin 𝔪 k → (S_f → ℤ)`, the valuations at `S_f` (they descend from `F^×`).
* `rho0 y = Ω(−log y, val y)` with L3P's fundamental-domain weight; every `U_S`-orbit meets it with
  total weight `|μ_F|`.
* `rho y = |μ_F|⁻¹ Σ_{s ∈ U_S/U_S⁶} rho0 (u_s y)`; then `Σ_{γ ∈ Γ} rho (γ y) = 1`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain NumberField.Units

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The `S`-unit coset representative of a class. -/
def uRep (s : SClass 𝔪) : SUnit 𝔪 := Function.surjInv QuotientGroup.mk_surjective s

theorem mk_uRep (s : SClass 𝔪) : (QuotientGroup.mk (uRep s) : SClass 𝔪) = s :=
  Function.surjInv_eq _ s

/-- `Γ = U_S⁶`. -/
abbrev Gam (𝔪 : Ideal (𝓞 F)) : Subgroup (SUnit 𝔪) := (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range

/-- `U_S/U_S⁶ × Γ ≃ U_S`, `(s, γ) ↦ u_s γ`. -/
def unitEquiv : SClass 𝔪 × Gam 𝔪 ≃ SUnit 𝔪 where
  toFun p := uRep p.1 * (p.2 : SUnit 𝔪)
  invFun u := ((QuotientGroup.mk u : SClass 𝔪), ⟨(uRep (QuotientGroup.mk u : SClass 𝔪))⁻¹ * u, by
    rw [← QuotientGroup.leftRel_apply, ← Quotient.eq'']
    exact (mk_uRep _)⟩)
  left_inv p := by
    obtain ⟨s, γ⟩ := p
    have h1 : (QuotientGroup.mk (uRep s * (γ : SUnit 𝔪)) : SClass 𝔪) = s := by
      refine (QuotientGroup.eq.2 ?_).trans (mk_uRep s)
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem γ.2
    refine Prod.ext h1 (Subtype.ext ?_)
    simp only
    rw [h1, inv_mul_cancel_left]
  right_inv u := by
    simp only [mul_inv_cancel_left]

/-! ### The weights -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Pack
/-! # L3X_Pack: the two cuts with top-level definitions

* `fpF κ m`: the forward `S`-Whittaker function `1_{y_f = 0} ∏_w ω_{m_w}(y_w) κ(|y_w|_w)`.
* `coefF'` (the cut's forward coefficient), `Fw`, `Rf`: the forward and the reflected
  nonconstant Fourier expansions.
* `KPk g k`, `SBk g k`, `SLk χ g k`: the conclusions of the three cuts at level `k`;
  `kp_unpack`, `sb_unpack`, `sl_unpack`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The forward `S`-Whittaker function. -/
def fpF (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (y : SModel 𝔪 k) : ℂ :=
  if y.2.2 = 0 then
    ∏ w, ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)
  else 0

/-- The cut's forward coefficient (the same as `L3X.coefF`, written with `L3V.Wsph`). -/
def coefF' (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (z : RowClass 𝔪) : ℂ :=
  residueSymbol ι 𝔪 𝔟 (rowElt g z) *
    ∏ P ∈ (normalizedFactors z.1.1).toFinset,
      L3V.Wsph g P ((normalizedFactors z.1.1).count P : ℤ)
        ((rowElt g z : F) * (g.gen P : F) ^ (-((normalizedFactors z.1.1).count P : ℤ)))

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Phi
/-! # L3X_Phi: the weight `Φ = ρ · 1_B([y]) · L(y)⁻¹` and the `S`-functions

* `Lmod` is a unitary character of `SModel`, radially trivial, rotating by `ω_{m_w}`.
* `psi y = 1_B([y]) L(y)⁻¹` is `Γ`-invariant; `Phi = ρ · psi`.
* `fpF` facts: its norm, and `L(y)⁻¹ fpF(y) = ∏_w κ(|y_w|)` on `y_f = 0`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Angular characters -/

/-! ### The weight -/

/-! ### The forward `S`-function -/

section Fp

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ)

/-- `|fpF|` as a real function. -/
def fpAbs (y : SModel 𝔪 k) : ℝ := if y.2.2 = 0 then ∏ w, κ (Real.exp (y.1 w)) else 0

end Fp

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Main
/-! # WP-H0, file 2: `KPCut` implies the frozen goal 8b3180bd

* `FmOf κ m J`: the product-form reflected `S`-Whittaker function of the cut.
* `FmOf_clauses`: for `κ = K.kappaB c` and `‖J‖ ≤ bf` it satisfies every `Fm`-clause of the goal
  (measurable, `bf ≥ 0`, C² along each radial coordinate, the derivative bound with
  `C = C_κ ^ #places`).
* `goal_of_KPCut`: the frozen statement, verbatim, from `KPCut`. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The product-form reflected function: `J cl y_f · ∏_w e^{−i m_w θ_w} κ(e^{x_w})`. -/
def FmOf (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ)
    (cl : SFinCls 𝔪 k) (y : SModel 𝔪 k) : ℂ :=
  J cl y.2.2 *
    ∏ w, ((AddCircle.toCircle ((-m w) • y.2.1 w) : Circle) : ℂ) * (κ (Real.exp (y.1 w)) : ℂ)

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ)

/-- The constant in front of the radial profile at `w`. -/
def radConst (cl : SFinCls 𝔪 k) (y : SModel 𝔪 k) (w : InfinitePlace F) : ℂ :=
  J cl y.2.2 * (∏ w', ((AddCircle.toCircle ((-m w') • y.2.1 w') : Circle) : ℂ)) *
    ∏ w' ∈ Finset.univ.erase w, (κ (Real.exp (y.1 w')) : ℂ)

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.T12.L3P_Gen
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L3P_Gen: `R ∖ 0 = U_S · {gen 𝔟}`

With a system of allowed generators, every nonzero `m ∈ R` is uniquely `ε · gen 𝔟` with `𝔟`
exterior and `ε ∈ R^×`. Sums over `R` (with vanishing term at `0`) are sums over these pairs.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} [Fintype (SP 𝔪)]

/-- Exterior ideals. -/
abbrev Ext (𝔪 : Ideal (𝓞 F)) : Type _ := {𝔟 : Ideal (𝓞 F) // IsExterior 𝔪 𝔟}

theorem isUnit_of_ordv_eq_zero {x : F} (hx0 : x ≠ 0) (h : ∀ w ∉ placesOf 𝔪, ordv w x = 0) :
    ∃ ε : (SInt 𝔪)ˣ, ((ε : SInt 𝔪) : F) = x := by
  have h1 : x ∈ (placesOf 𝔪).integer F := (mem_SInt_iff hx0).2 fun w hw => (h w hw).ge
  have h2 : x⁻¹ ∈ (placesOf 𝔪).integer F := (mem_SInt_iff (inv_ne_zero hx0)).2 fun w hw => by
    rw [ordv_inv, h w hw, neg_zero]
  refine ⟨⟨⟨x, h1⟩, ⟨x⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩,
    rfl⟩

theorem ordv_eq_count_outside {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ∉ placesOf 𝔪) : ordv w (m : F) = count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  have := congrArg (count F w) (spanSingleton_eq_mul_Pk h𝔟 hm)
  rw [count_mul F w (coeIdeal_ne_zero.2 h𝔟.1) (Pk_ne_zero _), count_Pk, dif_neg hw, add_zero] at this
  exact this

variable {ι : F →+* ℂ}

theorem span_unit_mul_gen (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪) (ε : (SInt 𝔪)ˣ) :
    Ideal.span {(ε : SInt 𝔪) * g.gen 𝔟.1} = 𝔟.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  rw [← g.span_gen 𝔟.1 𝔟.2, Ideal.span_singleton_mul_left_unit ε.isUnit]

theorem gen_ne_zero (g : AllowedGen ι 𝔪) (𝔟 : Ext 𝔪) : ((g.gen 𝔟.1 : SInt 𝔪) : F) ≠ 0 :=
  ne_zero_of_span_eq 𝔟.2 (g.span_gen 𝔟.1 𝔟.2)

/-- The parametrization `(𝔟, ε) ↦ ε · gen 𝔟`. -/
noncomputable def par (g : AllowedGen ι 𝔪) (p : Ext 𝔪 × (SInt 𝔪)ˣ) : SInt 𝔪 :=
  (p.2 : SInt 𝔪) * g.gen p.1.1

theorem par_injective (g : AllowedGen ι 𝔪) : Function.Injective (par g) := by
  rintro ⟨𝔟, ε⟩ ⟨𝔟', ε'⟩ h
  simp only [par] at h
  have h1 := span_unit_mul_gen g 𝔟 ε
  have h2 := span_unit_mul_gen g 𝔟' ε'
  rw [h] at h1
  have hb : 𝔟 = 𝔟' := by
    apply Subtype.ext
    apply coeIdeal_injective (K := F)
    refine eq_of_count_eq (coeIdeal_ne_zero.2 𝔟.2.1) (coeIdeal_ne_zero.2 𝔟'.2.1) fun w => ?_
    by_cases hw : w ∈ placesOf 𝔪
    · rw [count_eq_zero_of_exterior 𝔟.2 hw, count_eq_zero_of_exterior 𝔟'.2 hw]
    · rw [← ordv_eq_count_outside 𝔟.2 h1 hw, ← ordv_eq_count_outside 𝔟'.2 h2 hw]
  subst hb
  have hg0 := gen_ne_zero g 𝔟
  have : ((ε : SInt 𝔪) : F) = ((ε' : SInt 𝔪) : F) := by
    have := congrArg (fun z : SInt 𝔪 => (z : F)) h
    simp only [Subalgebra.coe_mul] at this
    exact mul_right_cancel₀ hg0 this
  rw [Prod.mk.injEq]
  exact ⟨rfl, Units.ext (Subtype.ext this)⟩

theorem exists_par (g : AllowedGen ι 𝔪) {m : SInt 𝔪} (hm : (m : F) ≠ 0) :
    ∃ p, par g p = m := by
  set J := spanSingleton (𝓞 F)⁰ (m : F) *
    ((Pk (-valS (𝔪 := 𝔪) (m : F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
  have hJ0 : J ≠ 0 := mul_ne_zero (spanSingleton_ne_zero hm) (Pk_ne_zero _)
  have hcount : ∀ w, count F w J = if w ∈ placesOf 𝔪 then 0 else ordv w (m : F) := by
    intro w
    rw [count_mul F w (spanSingleton_ne_zero hm) (Pk_ne_zero _), count_Pk]
    split_ifs with hw
    · simp [valS, ordv]
    · rw [add_zero]; rfl
  have hJle : J ≤ 1 := by
    rw [le_iff_count hJ0 one_ne_zero]
    intro w
    rw [count_one, hcount]
    split_ifs with hw
    · exact le_rfl
    · exact (mem_SInt_iff hm).1 m.2 w hw
  obtain ⟨𝔟, h𝔟J⟩ := le_one_iff_exists_coeIdeal.1 hJle
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl; apply hJ0; rw [← h𝔟J, coeIdeal_bot]
  have h𝔟ext : IsExterior 𝔪 𝔟 := by
    refine ⟨h𝔟0, ?_⟩
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    have hP0 : P ≠ ⊥ := fun h => h𝔟0 (le_bot_iff.1 (h ▸ le_sup_left.trans hle))
    set w : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime, hP0⟩
    have hw : w ∈ placesOf 𝔪 := le_sup_right.trans hle
    have h1 : count F w (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
      rw [h𝔟J, hcount, if_pos hw]
    rw [count_coe F w h𝔟0, Nat.cast_eq_zero] at h1
    exact (Associates.count_ne_zero_iff_dvd h𝔟0 w.irreducible).2
      (Ideal.dvd_iff_le.2 (le_sup_left.trans hle)) h1
  set b : Ext 𝔪 := ⟨𝔟, h𝔟ext⟩
  have hg0 := gen_ne_zero g b
  -- `m / gen 𝔟` is an `S`-unit
  have hq : ∀ w ∉ placesOf 𝔪, ordv w ((m : F) / (g.gen 𝔟 : F)) = 0 := by
    intro w hw
    rw [div_eq_mul_inv, ordv_mul w hm (inv_ne_zero hg0), ordv_inv,
      ordv_eq_count_outside h𝔟ext (g.span_gen 𝔟 h𝔟ext) hw, h𝔟J, hcount, if_neg hw]
    ring
  obtain ⟨ε, hε⟩ := isUnit_of_ordv_eq_zero (div_ne_zero hm hg0) hq
  refine ⟨(b, ε), Subtype.ext ?_⟩
  simp only [par, Subalgebra.coe_mul, hε, b]
  rw [div_mul_cancel₀ _ hg0]

end ArtinPrimitiveRoots.L3P
end

section
-- module Solutions.Artin.KP.H0_Row
/-! # WP-H0, file 3: the coordinate dictionary, part 1 — rows and frequencies

`(z, γ) ↦ γ · rowElt g z` is a bijection `RowClass 𝔪 × U_S⁶ ≃ R ∖ {0}` (`rowEquiv`), so each of the
two `∑'` of the frozen goal is a sum over `ν ∈ R ∖ 0` (`tsum_forward`, `tsum_reflected`, with the
exact summands of the goal). `rowOf ν` is the row class of `ν`: its ideal is the unique exterior
ideal `𝔷` with `𝔷R = νR` (`span_eq_map_rowOf`, `rowOf_ideal_unique`), its multiplicities are the
valuations of `ν` (`count_rowOf`), and it only depends on `ν` modulo `U_S⁶` (`rowOf_gam_mul`). -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- An `S`-unit as a unit of `R`. -/
abbrev uInt (u : SUnit 𝔪) : (SInt 𝔪)ˣ := Set.unitEquivUnitsInteger (placesOf 𝔪) F u

theorem coe_uInt (u : SUnit 𝔪) : (((uInt u : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = ((u : Fˣ) : F) := rfl

/-- `γ · rowElt g z` as an element of `R`. -/
def rowSInt (g : AllowedGen ι 𝔪) (p : RowClass 𝔪 × L3X.Gam 𝔪) : SInt 𝔪 :=
  ((uInt (p.2 : SUnit 𝔪) : (SInt 𝔪)ˣ) : SInt 𝔪) * rowElt g p.1

theorem rowSInt_eq_par (g : AllowedGen ι 𝔪) (p : RowClass 𝔪 × L3X.Gam 𝔪) :
    rowSInt g p = L3P.par g (p.1.1, uInt (L3X.unitEquiv (p.1.2, p.2))) := by
  apply Subtype.ext
  show (((p.2 : SUnit 𝔪) : Fˣ) : F) * ((((uInt (L3X.uRep p.1.2) : (SInt 𝔪)ˣ) : SInt 𝔪) : F) *
      (g.gen p.1.1.1 : F)) =
    (((L3X.uRep p.1.2 * (p.2 : SUnit 𝔪) : SUnit 𝔪) : Fˣ) : F) * (g.gen p.1.1.1 : F)
  rw [coe_uInt]
  push_cast
  ring

section

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
include h𝔪

theorem rowSInt_injective : Function.Injective (rowSInt g) := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  intro p q h
  rw [rowSInt_eq_par, rowSInt_eq_par] at h
  have h' := L3P.par_injective g h
  rw [Prod.mk.injEq] at h'
  have h2 : L3X.unitEquiv (p.1.2, p.2) = L3X.unitEquiv (q.1.2, q.2) :=
    (Set.unitEquivUnitsInteger (placesOf 𝔪) F).injective h'.2
  have h3 := L3X.unitEquiv.injective h2
  rw [Prod.mk.injEq] at h3
  exact Prod.ext (Prod.ext h'.1 h3.1) h3.2

theorem coe_rowSInt_ne_zero (p : RowClass 𝔪 × L3X.Gam 𝔪) : ((rowSInt g p : SInt 𝔪) : F) ≠ 0 := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  rw [rowSInt_eq_par]
  exact mul_ne_zero (L3P.unit_ne_zero _) (L3P.gen_ne_zero g p.1.1)

theorem rowSInt_ne_zero (p : RowClass 𝔪 × L3X.Gam 𝔪) : rowSInt g p ≠ 0 := fun h =>
  coe_rowSInt_ne_zero h𝔪 g p (by rw [h]; rfl)

theorem exists_rowSInt {ν : SInt 𝔪} (hν : ν ≠ 0) : ∃ p, rowSInt g p = ν := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have hν' : (ν : F) ≠ 0 := fun h => hν (Subtype.ext h)
  obtain ⟨⟨𝔟, ε⟩, hp⟩ := L3P.exists_par g hν'
  set u : SUnit 𝔪 := (Set.unitEquivUnitsInteger (placesOf 𝔪) F).symm ε with hu
  refine ⟨((𝔟, (L3X.unitEquiv.symm u).1), (L3X.unitEquiv.symm u).2), ?_⟩
  rw [rowSInt_eq_par]
  simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  rw [show uInt u = ε from MulEquiv.apply_symm_apply _ _]
  exact hp

/-- **The parametrization of `R ∖ 0`**: `(z, γ) ↦ γ · rowElt g z`. -/
def rowEquiv : RowClass 𝔪 × L3X.Gam 𝔪 ≃ {ν : SInt 𝔪 // ν ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨rowSInt g p, rowSInt_ne_zero h𝔪 g p⟩)
    ⟨fun _ _ h => rowSInt_injective h𝔪 g (congrArg Subtype.val h), fun ν => by
      obtain ⟨p, hp⟩ := exists_rowSInt h𝔪 g ν.2
      exact ⟨p, Subtype.ext hp⟩⟩

/-- The row class of a nonzero `ν ∈ R`. -/
def rowOf (ν : {ν : SInt 𝔪 // ν ≠ 0}) : RowClass 𝔪 := ((rowEquiv h𝔪 g).symm ν).1

/-- The sixth-power unit of a nonzero `ν ∈ R`: `ν = gamOf ν · rowElt g (rowOf ν)`. -/
def gamOf (ν : {ν : SInt 𝔪 // ν ≠ 0}) : L3X.Gam 𝔪 := ((rowEquiv h𝔪 g).symm ν).2

omit h𝔪 in
theorem coe_ne_zero (ν : {ν : SInt 𝔪 // ν ≠ 0}) : ((ν : SInt 𝔪) : F) ≠ 0 := fun h =>
  ν.2 (Subtype.ext h)

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H0_Rot
/-! # WP-H0, file 5: for the product form, "radial difference" is the same as "equal sums"

For the product-form `Fm` both sums of the frozen goal are of pure angular type `m` in `y`
(`Dcut_add_rot`), so their difference is rotation invariant only if it vanishes:
`KPCut ↔ KPCutEq`. The automorphic packages therefore have to prove the exact identity of the two
`tsum`s; there is no slack in the "radial constant term" variant. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The difference `D` of the frozen goal, as a function of its data (`b` stands for `g.gen 𝔟`). -/
def Dcut (g : AllowedGen ι 𝔪) (coef Ez : RowClass 𝔪 → ℂ) (fp : SModel 𝔪 k → ℂ)
    (Fm : SFinCls 𝔪 k → SModel 𝔪 k → ℂ) (b : F) (y : SModel 𝔪 k) : ℂ :=
  (∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
      coef p.1 * fp (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * (rowElt g p.1 : F)) + y)) -
    ∑' p : RowClass 𝔪 × (powMonoidHom 6 : SUnit 𝔪 →* SUnit 𝔪).range,
      Ez p.1 * Fm (QuotientAddGroup.mk (sEmb 𝔪 k ((rowElt g p.1 : F) / b ^ 2)).2.2)
        (sEmb 𝔪 k ((((p.2 : SUnit 𝔪) : Fˣ) : F) * ((rowElt g p.1 : F) / b ^ 2)) - y)

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H0_Nu
/-! # WP-H0, file 6: the cut as an identity of sums over `ν ∈ R ∖ 0`, with named local data

`KPCutNu` is the form of the cut the automorphic packages should prove: with the top-level
definitions `L3X.coefF'`, `L3V.Eprod` (definitionally the frozen `coef`, `Ez`), `L3X.fpF`, `FmOf`,
and the two sums indexed by nonzero `S`-integers:

  `∑_{ν ∈ R∖0} c⁺_𝔟(ν) f⁺(ν y) = ∑_{ν ∈ R∖0} c⁻_𝔟(ν) Fm([ν/b²], (ν/b²)/y)`,  `b = gen 𝔟`.

`KPCutNu ↔ KPCutEq ↔ KPCut`, and `goal_of_KPCutNu` is the frozen goal from it. -/

namespace ArtinKP.H0

open NumberField UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

/-- The cut as an identity of sums over the nonzero `S`-integers. -/
def KPCutNu (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥), SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (c α : ℝ), 0 < c ∧ 0 < α ∧ α ≤ 5 / 6 ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ cl y, ‖J cl y‖ ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
    ∀ (𝔟 : Ideal (𝓞 F)) (h𝔟 : IsExterior 𝔪 𝔟) (y : SModel 𝔪 k),
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
          L3X.coefF' g 𝔟 (rowOf h𝔪 g ν) *
            L3X.fpF (K.kappaB c) m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y) =
        ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
          L3V.Eprod g (⟨𝔟, h𝔟⟩, 1) (rowOf h𝔪 g ν) *
            FmOf (K.kappaB c) m J
              (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
              (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) - y)

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H_Grid
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-HA, file 1: a grid bound for sums over separated point sets (pure analysis)

`grid_sum`: let `e : T → (W → ℂ)` (`W` finite) be such that two distinct points never lie in a
common cell of mesh `h` (in every real and imaginary coordinate). Then

  `∑_{t ∈ T} ∏_w (1 + ‖e t w‖)⁻⁴ ≤ (2 (1 + ζ₂ / h²))^{2 #W}`,

with absolute convergence. No measure theory: the points are injected into the grid
`(W × Bool → Bool × ℕ)` (sign and `⌊|x| / h⌋`), and the sum over the grid is a product of
one-dimensional sums (`pi_prod_summable`). -/

namespace ArtinKP.H

open Finset

/-- `∑_{j ≥ 0} (j + 1)⁻²` (`= π²/6`; only its finiteness is used). -/
noncomputable def zeta2 : ℝ := ∑' j : ℕ, (((j : ℝ) + 1) ^ 2)⁻¹

/-- The cell of a real number: its sign and `⌊|x| / h⌋`. -/
noncomputable def cellOf (h x : ℝ) : Bool × ℕ := (decide (x < 0), ⌊|x| / h⌋₊)

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.H_Sum
/-! # WP-HA, file 2: sums over the nonzero `S`-integers, grouped by their class in `SFin`

* `one_le_prod_mul_norm`: the product formula for `d ∈ R ∖ 0`:
  `∏_w |d|_w · |d|_{S_f} = N(dR) ≥ 1`.
* `sep_class`: two distinct `ν, ν' ∈ R ∖ 0` of the same class `s ∈ SFin` satisfy
  `∏_w |ν − ν'|_w ≥ |s|_{S_f}⁻¹`.
* `fiber_sum`: `∑_{ν ∈ R∖0, [ν] = s} ∏_w (1 + w ν)⁻⁴ ≤ K (1 + |s|_{S_f}^{4r})`, `r = #places`,
  with `K` independent of `s`.
* `summable_class_weight`: `∑_{ν ∈ R∖0} B([ν]) ∏_w (1 + w ν)⁻⁴ < ∞` when `B ≥ 0`,
  `∑_s B(s) < ∞` and `∑_s B(s) |s|^{4r} < ∞`.

No hypothesis on the signature of `F` is used (the count is crude). -/

namespace ArtinKP.H

open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- The exponent `4·#places` of `|s|_{S_f}` in the fibre bound. -/
def expo (F : Type*) [Field F] [NumberField F] : ℕ := Fintype.card (InfinitePlace F) * 4

end

end ArtinKP.H
end

section
-- module Solutions.Artin.T12.L3V_Ideal
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # L3V_Ideal: prime-exponent bookkeeping for ideals of `𝓞 F`

`cnt P I = v_P(I)` (count in `normalizedFactors`), `prim I` its prime support; products, powers,
prime-power products over a finset, ideal equality from exponents, squarefreeness and coprimality
in exponent form, norms; `residueSymbol` over a squarefree ideal, and reciprocity
`χ_𝔠(gen 𝔡) = χ_𝔡(gen 𝔠)` for coprime exterior `𝔠, 𝔡`. -/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace L3V

variable {F : Type*} [Field F] [NumberField F]

/-- `v_P(I)`. -/
noncomputable abbrev cnt (P I : Ideal (𝓞 F)) : ℕ := (normalizedFactors I).count P

/-- The prime support of `I`. -/
noncomputable abbrev prim (I : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) := (normalizedFactors I).toFinset

end L3V

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.KP.H_Dig
/-! # WP-HA, file 4: the digit sums

Local, at a good prime `P` (`C3I.Good`), with `χ = C3I.chi`, `ψ = C3I.psi`:

* `sum_mask_psi`: (6.4) `∑_d α_{P,k mod 6}(d) ψ(a d) = χ(a)^k` for `k ≥ 1` and every residue `a`;
* `sum_mask_sAddChar`: the same with `e(x d̃ / p)`, `x ∈ R`: the value is `χ_P(x)^k`.

Global, for an exterior ideal `𝔟`:

* `Dig 𝔪 𝔟`: digit vectors `(v_P)_{P ∣ 𝔟}`, `v_P ∈ R/PR`; `xdig g 𝔟 v = ∑_P ṽ_P / p_P ∈ F`;
  `maskProd g 𝔟 v = ∏_P α_{P, v_P(𝔟) mod 6}(v_P)`;
* `digCoef g r v z`: the exterior product of `L3V.Eprod` with each `Eloc` replaced by the value
  at the digit `v_P` (`Wsph` at the zero digit and outside `𝔟`, `Wweyl` at a nonzero digit);
* `sum_maskProd_sAddChar`: `∑_v maskProd(v) e(x · x_v) = χ_𝔟(x)` (needs good primes);
* `sum_maskProd_digCoef`: `∑_v maskProd(v) digCoef(v, z) = Eprod g r z` (no hypothesis);
* `residueSymbol_rowOf`, `residueSymbol_neg`: `χ_𝔟` is `U_S⁶`-invariant and even. -/

namespace ArtinKP.H

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Local: (6.4) -/

/-! ### The additive character on finite sums -/

/-! ### Digit vectors -/

/-- Digit vectors for `𝔟`: one residue class modulo `P` for each prime `P ∣ 𝔟`. -/
abbrev Dig (𝔪 𝔟 : Ideal (𝓞 F)) : Type _ :=
  (P : {P : Ideal (𝓞 F) // P ∈ (normalizedFactors 𝔟).toFinset}) →
    SInt 𝔪 ⧸ P.1.map (algebraMap (𝓞 F) (SInt 𝔪))

/-- The rational point `x_v = ∑_{P ∣ 𝔟} ṽ_P / p_P` of a digit vector. -/
def xdig (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : Dig 𝔪 𝔟) : F :=
  ∑ P : {P : Ideal (𝓞 F) // P ∈ (normalizedFactors 𝔟).toFinset},
    (quotLift (v P) : F) / (g.gen P.1 : F)

/-- The product of the masks `α_{P, v_P(𝔟) mod 6}(v_P)`. -/
def maskProd (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : Dig 𝔪 𝔟) : ℂ :=
  ∏ P : {P : Ideal (𝓞 F) // P ∈ (normalizedFactors 𝔟).toFinset},
    L3V.mask g P.1 ((normalizedFactors 𝔟).count P.1 % 6) (v P)

/-- The local value at `P` for the digit vector `v`: `W_P(a(ν))` at the zero digit and at the
primes not dividing `𝔟`, the Weyl value `W_P(a(ν) w n(v_P / p))` at a nonzero digit. -/
def digLoc (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : Dig 𝔪 𝔟) (P : Ideal (𝓞 F)) (e₀ : ℤ)
    (t : F) : ℂ :=
  if hP : P ∈ (normalizedFactors 𝔟).toFinset then
    (if v ⟨P, hP⟩ = 0 then L3V.Wsph g P e₀ t else L3V.Wweyl g P e₀ t (v ⟨P, hP⟩))
  else L3V.Wsph g P e₀ t

end

end ArtinKP.H
end

section
-- module Solutions.Artin.KP.G2a_Major
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 2: the summable majorant of `τ_Φ(ν)·W_{4/3}(ν; v)`

* `ThmE hG hz6 g`: **named hypothesis**, Theorem E for the instance `T.theta hG hz6` in the form
  of `H.tau_eq_coefF'` (`thmE_of_PER` derives it from cube periodicity at every exterior prime
  plus the standing data of `H_Tau`).
* `absNorm_rowOf`: the product formula, exact: `N(νR) = ∏_w |ν|_w^{mult} · |ν|_{S_f}`.
* `norm_tau_le`: `|τ_Φ(ν)| ≤ ∏_w |ν|_w^{2/3} · bf([ν])` with `bf` summable against `|y|^σ`,
  `σ > −1/3` (G1's majorant of the Kirillov function).
* `exists_major`: for every box `vBox F n₀` and every `p` a summable `u` with
  `∏_w (1+|ν|_w)^p · |τ_Φ(ν) W_{4/3}(ν; v)| ≤ u ν` for all `v` in the box.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F]

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (g : AllowedGen ι 𝔪)

/-- **Named hypothesis: Theorem E** for `T.theta hG hz6`, in the form of `H.tau_eq_coefF'`. -/
def ThmE (P : CubicPkg F) : Prop :=
  ∀ (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}),
    T.tau hG hz6 Φ (ν : SInt 𝔪) =
      (((Ideal.absNorm (H0.rowOf hG.ne_bot g ν).1.1 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        T.tau hG hz6 ((B.kubota hG hz6).act (ν : SInt 𝔪) Φ) 1

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Def
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 3: the series `thetaS` (definition, convergence, continuity, linearity)

`term Φ ν Q = τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` (`Q = (x, v)`), `thetaS Φ Q = Σ_{ν ∈ R∖0} term Φ ν Q`.
Under Theorem E (`ThmE`) the series converges absolutely, uniformly on every set `vOpen n`
(`v ∈ (1/(n+1), n+1)^r`, any `x`), together with every polynomial weight `∏_w (1+|ν|_w)^p`;
`thetaS Φ` is continuous on `X F`, additive in `Φ` and homogeneous for `smulFun`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable [IsTotallyComplex F]
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- The `ν`-th term of the Fourier expansion of `θ̃_Φ` (without the constant `kapC`). -/
def term (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) (Q : X F) : ℂ :=
  T.tau hG hz6 Φ (ν : SInt 𝔪) * T.WX (4 / 3) ((ν : SInt 𝔪) : F) Q *
    eInf (emb ((ν : SInt 𝔪) : F) * Q.x)

/-- The non-constant part of `θ̃_Φ` (without `kapC`). -/
def thetaS (Φ : GSection ι P 𝔪) (Q : X F) : ℂ := ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, term hG hz6 Φ ν Q

/-- `{v ∈ (1/(n+1), n+1)^r}`, open in `X F`. -/
def vOpen (F : Type*) [Field F] [NumberField F] (n : ℕ) : Set (X F) :=
  {Q | ∀ w, 1 / ((n : ℝ) + 1) < Q.v w ∧ Q.v w < (n : ℝ) + 1}

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Exp
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 6: the pointwise theta function and **(Exp)**

* `kapC F = covol(𝓞_F)⁻¹` (`= T.kap 𝔪 M` for every `M ≥ 0`).
* `IsExp Φ z`: for every finite-index `Γ` fixing `Φ.twist`,
  `X.lift Γ (C5.theta Γ Φ.twist) = z·ht^{2/3} + kapC·thetaS Φ` almost everywhere.
* **`exists_isExp`** (Theorem E + `hdiff`): such a `z` exists.  (Fourier uniqueness on the full
  stabilizer, `C9.ae_eq_htC_of_coeff`; other groups by `N.lift_theta_congr`.)
* `zc Φ` := that `z` (unique: `isExp_unique`); **`thetaT Φ Q := zc Φ·ht(Q)^{2/3} + kapC·thetaS Φ Q`**,
  continuous, and `thetaT_ae`: it represents `θ_{Φ.twist}` for every admissible `Γ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- The constant of the Fourier expansion: `covol(𝓞_F)⁻¹`. -/
def kapC (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F] : ℂ :=
  ((((volume (B1.fundD F)).toReal : ℝ)) : ℂ)⁻¹

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- `z` is the constant term making `z·ht^{2/3} + kapC·thetaS Φ` a representative of `θ`. -/
def IsExp (Φ : GSection ι P 𝔪) (z : ℂ) : Prop :=
  ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex], Inv Γ (Φ.twist hG hz6) →
    X.lift Γ (C5.theta Γ (Φ.twist hG hz6)) =ᵐ[X.vol F]
      fun Q => z * htC (2 / 3) Q + kapC F * thetaS hG hz6 Φ Q

variable {hG hz6} {g : AllowedGen ι 𝔪}

variable (hG hz6)

open Classical in
/-- The constant term `z_Φ` of `θ̃_Φ`. -/
def zc (Φ : GSection ι P 𝔪) : ℂ := if h : ∃ z : ℂ, IsExp hG hz6 Φ z then h.choose else 0

/-- **The pointwise theta function** `θ̃_Φ` (MATH3 §0). -/
def thetaT (Φ : GSection ι P 𝔪) (Q : X F) : ℂ :=
  zc hG hz6 Φ * htC (2 / 3) Q + kapC F * thetaS hG hz6 Φ Q

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.K_Weyl
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatComplexH3Vol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol
/-! # WP-K, file 4: the Weyl flip on `H³ = SL₂(ℂ)/SU(2)`, and Fourier terms

Model: WP-X's `ArtinKP.X.H3 = {(x, v) : ℂ × ℝ | 0 < v}` with its `SL(2,ℂ)`-action; a right
`SU(2)`-invariant function on `SL₂(ℂ)` is `g ↦ f (g • j0)`, `j0 = (0, 1)`.

For `g = n(x) a(y)` (`a(y) = diag(y, y⁻¹)`, `y ∈ ℂˣ`), the two curves through `g • j0 = (x, |y|²)`
* `ζ ↦ g n(ζ) • j0 = (x + y² ζ, |y|²)`                               (`curveN`, `orbit_N`),
* `ζ ↦ g w n(ζ) • j0 = (x − y² ζ̄/(1+|ζ|²), |y|²/(1+|ζ|²))`           (`curveW`, `orbit_W`)
have Wirtinger derivatives at `ζ = 0` related by

  `∂_ζ (f ∘ curveW) = −∂_ζ̄ (f ∘ curveN)`,  `∂_ζ̄ (f ∘ curveW) = −∂_ζ (f ∘ curveN)`   (`weyl_flip`):

right translation by `w` exchanges the derivatives of weight `+1` and `−1` along `n(ζ)`, up to
the sign `−1` (MATH §4.5 "Weyl element"; `Ad(w) X_ζ = Y_{−ζ} ≡ X_{−ζ̄}` mod `𝔰𝔲(2)`).
On a Fourier term `f(x, v) = e(Tr νx) W(v)`: `∂_ζ (f ∘ curveN) = 2πi ν y² f`,
`∂_ζ̄ (f ∘ curveN) = 2πi conj(ν y²) f` (`dz_fourierTerm_curveN`), hence
`∂_ζ (f ∘ curveW) = −2πi conj(ν y²) f`, `∂_ζ̄ (f ∘ curveW) = −2πi ν y² f` (`weyl_flip_fourierTerm`).
-/

open scoped MatrixGroups ComplexConjugate

namespace ArtinKP.K

open ArtinKP.X

noncomputable section

/-! ## Matrices and orbits -/

/-- `n(x) = [[1, x], [0, 1]]`. -/
def nMat (x : ℂ) : SL(2, ℂ) := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- `n̄(η) = [[1, 0], [η, 1]]`. -/
def nbarMat (η : ℂ) : SL(2, ℂ) := ⟨!![1, 0; η, 1], by simp [Matrix.det_fin_two]⟩

/-- `a(y) = diag(y, y⁻¹)`. -/
def aMat (y : ℂˣ) : SL(2, ℂ) :=
  ⟨!![(y : ℂ), 0; 0, ((y⁻¹ : ℂˣ) : ℂ)], by simp [Matrix.det_fin_two]⟩

/-- The Weyl element `w = [[0, 1], [−1, 0]]`. -/
def wMat : SL(2, ℂ) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

/-- The base point `j = (0, 1)`, with stabilizer `SU(2)`. -/
def j0 : H3 := H3.mk 0 1 one_pos

@[simp] lemma coe_nMat (x : ℂ) : (nMat x : Matrix (Fin 2) (Fin 2) ℂ) = !![1, x; 0, 1] := rfl
@[simp] lemma coe_nbarMat (η : ℂ) : (nbarMat η : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; η, 1] := rfl
@[simp] lemma coe_aMat (y : ℂˣ) :
    (aMat y : Matrix (Fin 2) (Fin 2) ℂ) = !![(y : ℂ), 0; 0, ((y⁻¹ : ℂˣ) : ℂ)] := rfl
@[simp] lemma coe_wMat : (wMat : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := rfl

/-- The curve `ζ ↦ n(x) a(y) n(ζ) • j` in coordinates. -/
def curveN (x y ζ : ℂ) : ℂ × ℝ := (x + y ^ 2 * ζ, ‖y‖ ^ 2)

/-- The curve `ζ ↦ n(x) a(y) w n(ζ) • j` in coordinates. -/
def curveW (x y ζ : ℂ) : ℂ × ℝ :=
  (x - y ^ 2 * (conj ζ * (((1 + ‖ζ‖ ^ 2)⁻¹ : ℝ) : ℂ)), ‖y‖ ^ 2 * (1 + ‖ζ‖ ^ 2)⁻¹)

/-! ## Wirtinger derivatives and the flip -/

/-- `∂/∂ζ` of a real-differentiable `φ : ℂ → ℂ`. -/
def dz (φ : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ φ ζ 1 - Complex.I * fderiv ℝ φ ζ Complex.I)

/-- `∂/∂ζ̄` of a real-differentiable `φ : ℂ → ℂ`. -/
def dzbar (φ : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ φ ζ 1 + Complex.I * fderiv ℝ φ ζ Complex.I)

/-! ## Fourier terms -/

/-! ## The Whittaker function at `s = 4/3` and the profile `κ` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.G2a_Dx
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-G2a, file 8: the mixed first `x`-derivative `∂_m` and Fourier series

`∂^{(+1)} = ∂_x`, `∂^{(−1)} = ∂_x̄` (Wirtinger, `K.dz`, `K.dzbar`) in one coordinate `x_w` of
`x : InfinitePlace F → ℂ`; `∂_m = ∏_w ∂^{(m_w)}_{x_w}` (MATH3 §0), defined by iterating over a
list of places.

* `Dw m w f`: the Wirtinger derivative of type `m` in the `w`-th coordinate.
* `DList m l f`: iteration over the list `l`; `Dm m f := DList m Finset.univ.toList f`.
* **`DList_series`**: for a Fourier series `Σ_i c_i e_∞(ν_i x)` whose coefficients are summable
  against every power of `1 + ‖ν_i‖`, `DList m l` acts termwise:
  the `i`-th term is multiplied by `∏_{w ∈ l} (−2πi · ν_{i,w}^{(m_w)})`.
-/

open scoped ComplexConjugate Topology
open NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.K ArtinKP.B

noncomputable section

/-! ### One complex variable -/

/-- `h ↦ 2πi(a h + conj (a h))`, the differential of the exponent of `archChar (a ζ)`. -/
def linA (a : ℂ) : ℂ →L[ℝ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ) • ((a • ContinuousLinearMap.id ℝ ℂ) +
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (a • ContinuousLinearMap.id ℝ ℂ))

/-- `φ ↦ ∂_ζ φ` as a functional of the real differential. -/
def dzL : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) -
    Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

/-- `φ ↦ ∂_ζ̄ φ` as a functional of the real differential. -/
def dzbarL : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) +
    Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

/-- `z^{(+1)} = z`, `z^{(−1)} = z̄` (MATH3 §0). -/
def cj (m : ℤ) (z : ℂ) : ℂ := if m = 1 then z else conj z

/-! ### Several variables -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The Wirtinger derivative of type `m` in the coordinate `w`. -/
def Dw (m : ℤ) (w : W) (f : (W → ℂ) → ℂ) (x : W → ℂ) : ℂ :=
  if m = 1 then dz (fun ζ => f (Function.update x w ζ)) (x w)
  else dzbar (fun ζ => f (Function.update x w ζ)) (x w)

/-- Iterated Wirtinger derivatives along a list of coordinates. -/
def DList (m : W → ℤ) : List W → ((W → ℂ) → ℂ) → (W → ℂ) → ℂ
  | [], f => f
  | w :: l, f => Dw (m w) w (DList m l f)

/-- **`∂_m = ∏_w ∂^{(m_w)}_{x_w}`** (each coordinate once). -/
def Dm (m : W → ℤ) (f : (W → ℂ) → ℂ) : (W → ℂ) → ℂ := DList m Finset.univ.toList f

/-- The character `e(ν; x) = ∏_w archChar (−ν_w x_w)` (`= B.eInf (ν * x)`). -/
def eW (ν x : W → ℂ) : ℂ := ∏ w, archChar (-(ν w * x w))

variable {I : Type*}

/-- The eigenvalue of `DList m l` on the character of frequency `ν`. -/
def eig (m : W → ℤ) (l : List W) (ν : W → ℂ) : ℂ :=
  (l.map fun w => -(2 * Real.pi * Complex.I) * cj (m w) (ν w)).prod

/-! ### Constants are killed -/

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Fwd
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 9: `∂_m θ̃_Φ` termwise and the forward field (MATH3 §1.1)

* `thetaX Φ v hv x = θ̃_Φ(x, v)` as a function of `x` at fixed height `v`.
* **`Dm_thetaX`**: `∂_m θ̃_Φ(·, v)` is the termwise series; the constant term is killed and the
  `ν`-th term is multiplied by `∏_w (−2πi·ν_w^{(m_w)})`.
* `ThetaM m Φ X Y := ∏_w Y_w^{(m_w)} · (∂_m θ̃_Φ)(X, |Y|)` (MATH3's `Θ_m^Φ(X, Y)`).
* `place_kappaB`: `(νY)^{(m)}·jacquet (4/3) (−ν) |Y| = C0·|ν|^{−2/3}·ω_m(νY)·κ(|νY|²)`,
  `κ = K.kappaB (4π)`, `C0 = (2π)^{4/3}/Γ(4/3)`.
* **`ThetaM_tau`**: the expansion with coefficient `τ_Φ(ν)` (no Theorem E beyond convergence);
* **`ThetaM_forward`** = MATH3 (1.1):
  `Θ_m^Φ(X,Y) = kapC·C_a^r·Σ_ν coef^S(ν)·ξ_Φ(ν)·e_∞(νX)·∏_w ω_{m_w}(ν_wY_w)·κ(|ν_wY_w|²)`,
  `C_a = −2πi·C0`, with `summable_forward`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

/-! ### One place -/

/-- `ω_m(z) = z^{(m)}/|z|`. -/
def omg (m : ℤ) (z : ℂ) : ℂ := cj m z / (‖z‖ : ℂ)

/-- `C0 = (2π)^{4/3}/Γ(4/3)`. -/
def C0 : ℂ := (2 * Real.pi : ℂ) / Complex.Gamma (4 / 3) * (((2 * Real.pi) ^ (1 / 3 : ℝ) : ℝ) : ℂ)

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- `θ̃_Φ(x, v)` as a function of `x` at fixed `v`. -/
def thetaX (Φ : GSection ι P 𝔪) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w)
    (x : InfinitePlace F → ℂ) : ℂ := thetaT hG hz6 Φ (X.mk x v hv)

variable {hG hz6} {g : AllowedGen ι 𝔪}

variable (hG hz6)

/-- **MATH3's `Θ_m^Φ(X, Y) = ∏_w Y_w^{(m_w)}·(∂_m θ̃_Φ)(X, |Y|)`.** -/
def ThetaM (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪) (X : InfinitePlace F → ℂ)
    (Y : InfinitePlace F → ℂ) (hY : ∀ w, Y w ≠ 0) : ℂ :=
  (∏ w, cj (m w) (Y w)) *
    Dm m (thetaX hG hz6 Φ (fun w => ‖Y w‖) (fun w => norm_pos_iff.mpr (hY w))) X

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Block
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 11: first derivatives in a block `(x_w, v_w)`

* `exists_major_prod`: the majorant of `G2a_Major` for an arbitrary product of one-place factors
  satisfying the one-place bound.
* `serA Φ q x v = Σ_ν q(ν)·τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` in ambient coordinates.
* **`differentiableAt_block`**: for `q` of polynomial growth, `serA Φ q` is differentiable in the
  block `(x_w, v_w)` at every point with `v > 0`, the other coordinates fixed (termwise, with a
  summable majorant of the differentials on `ℂ × (a, b)`: MATH3 (Exp), "first partial derivatives
  in each block, locally uniformly").
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- The weighted series in ambient coordinates. -/
def serA (Φ : GSection ι P 𝔪) (q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) (x : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) : ℂ :=
  ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
    q ν * (T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) v) *
      eInf (emb ((ν : SInt 𝔪) : F) * x)

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-! ### The differential of one term in a block -/

/-- The differential of `z ↦ archChar (a (z.1 − b)) · jacquet (4/3) a z.2` on `ℂ × ℝ`. -/
def blockD (a b : ℂ) (z : ℂ × ℝ) : ℂ × ℝ →L[ℝ] ℂ :=
  archChar (a * (z.1 - b)) •
      ((1 : ℝ →L[ℝ] ℝ).smulRight (jd a z.2)).comp (ContinuousLinearMap.snd ℝ ℂ ℝ) +
    jacquet (4 / 3) a z.2 •
      (archChar (a * (z.1 - b)) • linA a).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.GK_J
/-! # WP-GK, file 2: the function `J` and its majorant `bf` (MATH3 §4)

For a section `Φ₀` and a level `k`:

* `Jdef hG hz6 Φ₀ cl y' = (−1)^r · ⟨ν̃, η′⟩ · ξ_{wΦ₀}(η′)` with chosen representatives `ν̃` of
  `cl : SFinCls 𝔪 k` and `η′` of `y' : SFin 𝔪 k` (MATH3 (2d)).
* `exists_bf_J`: a majorant `bf` on `SFin 𝔪 k` with `‖J cl y‖ ≤ bf y` and `Σ bf · |y|^σ < ∞` for
  `σ > −1/3`, for every section `Φ₀` (no hypothesis on `Φ₀`).
* `xi_w_inv` — **(INV)** for `ξ`: `ξ_{wΦ₀}(βu) = ξ_{wΦ₀}(β)` for `u ∈ U_k`, `Φ₀` a delta section.
* `Jdef_mk` — **well-definedness**: for a delta section `Φ₀` (level `k`, `k + 1` deep) and any
  representatives `x, η ∈ F^×`: `J([x], [η]) = (−1)^r ⟨x, η⟩ ξ_{wΦ₀}(η)`.
* `xi_w_PhiY` — MATH3 (4.1): `ξ_{wΦ_{y_f}}(ν̃) = ⟨ν̃, β₀⟩⁻¹ ξ_{wΦ₀}(ν̃/β₀)` for
  `Φ_{y_f} = |β₀|^{1/3} Ã(β₀) Φ₀`, and its `J`-form `xi_w_PhiY_eq_J`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {k : ℕ}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- The majorant, as a function. -/
def bfdef (Φ₀ : GSection ι P 𝔪) (k : ℕ) : SFin 𝔪 k → ℝ :=
  Classical.choose (exists_summable_majorant_norm_jdef hG hz6 Φ₀ k)

/-! ### (INV) and well-definedness for a delta section -/

section delta

variable (g : AllowedGen ι 𝔪)
  (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
    C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (hd : DD.DiffInS 𝔪)

/-- `Φ₀` is a delta section of level `k`: `𝒦_{Φ₀} = 1_{U_k}` on all of `F^×`. -/
def IsDelta (k : ℕ) (Φ₀ : GSection ι P 𝔪) : Prop :=
  ∀ β : F, β ≠ 0 → G1.Kir hG hz6 (T.theta hG hz6) Φ₀ β
    = open Classical in if Small 𝔪 ((k : ℤ) + 1) (β - 1) then 1 else 0

/-! ### MATH3 (4.1) -/

/-- `Φ_{y_f} = |β₀|^{1/3} · Ã(β₀) Φ₀` for a representative `β₀` (MATH3 §1.2). -/
def PhiB (Φ₀ : GSection ι P 𝔪) (β₀ : Fˣ) : GSection ι P 𝔪 :=
  (((absS 𝔪 (β₀ : F) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) • Φ₀.torusT hG (β₀ : F) β₀.ne_zero

end delta

end

end ArtinKP.GK
end

section
-- module Solutions.Artin.KP.GR_Arch
/-! # WP-GR, file 1: the archimedean dictionary

G2a's profile `∏_w ω_{m_w}(ν_w Y_w)·κ(|ν_w Y_w|²)` (`G2a.omg`, `K.kappaB (4π)`) against the
frozen `L3X.fpF κ m (sEmb ν + y)` and `H0.FmOf κ m J cl (sEmb ν̃ − y)`.

* `Yof y w = exp(y.1 w / 2)·e^{iθ_w}` (MATH3 §0), `Yrt` a square root of it.
* `omg_polar`: for `m = ±1`, `ω_m(z·r·e^{iθ}) = e^{i m arg z}·e^{i m θ}`.
* `arch_forward`: the product at `ν_w·Y_w`;
* `arch_reflected`: the product of type `−m` at `ν̃_w / Y_w`.
-/

open scoped ComplexConjugate Topology Classical
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.G2a ArtinKP.K

noncomputable section

/-! ### One place -/

/-! ### The archimedean coordinate `Y(y)` -/

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- `Y_w = exp(y.1 w / 2)·e^{iθ_w}`: `|Y_w|² = exp(y.1 w)` is the normalized absolute value. -/
def Yof (y : SModel 𝔪 k) (w : InfinitePlace F) : ℂ :=
  ((Real.exp (y.1 w / 2) : ℝ) : ℂ) * ((AddCircle.toCircle (y.2.1 w) : Circle) : ℂ)

lemma Yof_ne_zero (y : SModel 𝔪 k) (w : InfinitePlace F) : Yof y w ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') (Circle.coe_ne_zero _)

/-- A square root of `Y_w`. -/
def Yrt (y : SModel 𝔪 k) (w : InfinitePlace F) : ℂ := Complex.exp (Complex.log (Yof y w) / 2)

end

end ArtinKP.GR
end

section
-- module Solutions.Artin.KP.GR_Flip
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-GR, file 2: MATH3 (2.3) — cusp change and Weyl flip for `Θ_m^Φ`

* `Dm_thetaX_affine`: the chain rule `∂_m[ζ ↦ θ̃_Φ(X₀ + Aζ, v)]_{ζ=0} = ∏_w A_w^{(m_w)}·(∂_m θ̃_Φ)(X₀, v)`
  (termwise on the Fourier series, `G2a.DList_series`).
* `orbit_cusp`: `γ·n(ξ)a(y)n(ζ)·j = n(a/c)·a(1/(cy))·w·n(ζ)·j` for `ξ = −d/c` (the K-part is
  exactly `w`); `smul_curveN`: the same on `X F`, in the coordinates `K.curveN`, `K.curveW`.
* `WeylFlip P hG hz6`: **named hypothesis** = the statement of the stub `G2a.weyl_flip_thetaT`
  (owner WP-GW), for all `m` with values `±1`.
* **`ThetaM_flip`** = MATH3 (2.3):
  `Θ_m^Φ(emb ξ, y²) = (−1)^r · Θ_{−m}^{γΦ}(emb(a/c), 1/(cy)²)`, `γΦ = translate γ Φ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

/-! ### One place: the orbit identity -/

lemma curveW_pos (x : ℂ) {y : ℂ} (hy : y ≠ 0) (ζ : ℂ) : 0 < (curveW x y ζ).2 := by
  unfold curveW
  have : 0 < ‖y‖ := norm_pos_iff.mpr hy
  positivity

lemma curveN_pos (x : ℂ) {y : ℂ} (hy : y ≠ 0) (ζ : ℂ) : 0 < (curveN x y ζ).2 := by
  unfold curveN
  have : 0 < ‖y‖ := norm_pos_iff.mpr hy
  positivity

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable [IsTotallyComplex F] {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### The chain rule along an affine map -/

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-! ### The Weyl flip (named hypothesis) and MATH3 (2.3) -/

variable (hG hz6 P)

/-- **Named hypothesis (owner WP-GW)**: the statement of the stub `G2a.weyl_flip_thetaT` for
every type `m` with values `±1`. -/
def WeylFlip : Prop :=
  ∀ (m : InfinitePlace F → ℤ), (∀ w, m w = 1 ∨ m w = -1) → ∀ (Ψ : GSection ι P 𝔪)
    (X₀ y : InfinitePlace F → ℂ) (hy : ∀ w, y w ≠ 0),
    Dm m (fun ζ : InfinitePlace F → ℂ => thetaT hG hz6 Ψ
        (X.mk (fun w => (curveW (X₀ w) (y w) (ζ w)).1) (fun w => (curveW (X₀ w) (y w) (ζ w)).2)
          (fun w => curveW_pos (X₀ w) (hy w) (ζ w)))) 0 =
      (-1) ^ Fintype.card (InfinitePlace F) *
        Dm (fun w => -m w) (fun ζ : InfinitePlace F → ℂ => thetaT hG hz6 Ψ
          (X.mk (fun w => (curveN (X₀ w) (y w) (ζ w)).1) (fun w => (curveN (X₀ w) (y w) (ζ w)).2)
            (fun w => curveN_pos (X₀ w) (hy w) (ζ w)))) 0

end

end ArtinKP.GR
end

section
-- module Solutions.Artin.KP.GR_Theta
/-! # WP-GR, file 3: `Θ` and its two expansions (MATH3 §1, §2; §6.1 (6))

* `thmE`: G2a's named hypothesis `ThmE` from WP-GK (`GK.per_all`, `S2.cubicSymbol_gen`).
* `Ccon = kapC·(−2πi·C0)^r` (MATH3's `C`).
* **`ThetaG`**: `Θ(x, y) = C⁻¹·Θ_m^{nT(−x)Φ_{y_f}}(emb(−x), Y(y))`, `Φ_{y_f} = GK.PhiB hG Φ₀ (rep y_f)`.
* `xi_PhiB`: `ξ_{Φ_{y_f}}(β) = 1[[β] + y_f = 0]` for a delta section `Φ₀`.
* **`thetaG_forward`**: HB's forward expansion, for every `x ∈ F`.
* **`thetaG_reflected`**: HB's reflected expansion (MATH3 (2.4) with (4.1)), for every `x ∈ F` and
  `γ ∈ SL₂(R)` with bottom row `(c, cx)`, `c ≠ 0`; needs the named hypothesis `WeylFlip`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- MATH3's constant `C = c_B·C_a^r`, `c_B = kapC F`, `C_a = −2πi·(2π)^{4/3}/Γ(4/3)`. -/
def Ccon (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F] : ℂ :=
  kapC F * (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F)

variable {k : ℕ}

/-- **The function `Θ`** of the contract (MATH3 §1.1):
`Θ(x, y) = C⁻¹·Θ_m^{nT(−x)Φ_{y_f}}(emb(−x), Y(y))`, `Φ_{y_f} = |β₀|^{1/3}·Ã(β₀)Φ₀`,
`β₀ = G1.repS y_f` the chosen representative of `y_f = y.2.2`. -/
def ThetaG (m : InfinitePlace F → ℤ) (Φ₀ : GSection ι P 𝔪) (x : F) (y : SModel 𝔪 k) : ℂ :=
  (Ccon F)⁻¹ * ThetaM hG hz6 m ((GK.PhiB hG Φ₀ (G1.repS y.2.2)).nT hG (-x)) (emb (-x)) (Yof y)
    (Yof_ne_zero y)

end

end ArtinKP.GR
end

section
-- module Solutions.Artin.KP.GW_One
/-! # WP-GW, file 1: one place

* `Dt m φ`: the Wirtinger derivative of type `m` of `φ : ℂ → ℂ` at `0` (`∂_ζ` for `m = 1`,
  `∂_ζ̄` otherwise), with `Dw_eq_Dt`, `Dt_add`, `Dt_series`.
* `PolyB q`: the weight `q` on the frequencies is polynomially bounded
  (`‖q ν‖ ≤ C·∏_w (1 + |ν|_w)^p`), the class of weights for which `G2a.serA` converges with all
  its first block derivatives.
* `summable_weight`: the coefficients of `serA Φ q` are summable against every power of `1 + ‖ν‖`.
* **`Dt_serA_curveN`**: along `K.curveN` in the place `w` the series `serA Φ q` is a Fourier series
  in `ζ`; its type-`m` derivative at `0` is `serA Φ (q·μ')`, `μ'(ν) = −2πi·(ν_w y²)^{(m)}`.
* **`Dt_serA_curveW`** (the one-place Weyl flip, `m = ±1`): along `K.curveW` the type-`m`
  derivative at `0` is `serA Φ (q·μ)`, `μ(ν) = 2πi·(ν_w y²)^{(−m)}`
  (`G2a.differentiableAt_block` + `K.weyl_flip` + `Dt_serA_curveN` for the type `−m`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GW

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
open ArtinKP.G2a

noncomputable section

/-! ### The type-`m` derivative at `0` -/

/-- The Wirtinger derivative of type `m` at `0`: `∂_ζ` for `m = 1`, `∂_ζ̄` otherwise. -/
def Dt (m : ℤ) (φ : ℂ → ℂ) : ℂ := if m = 1 then dz φ 0 else dzbar φ 0

/-! ### Polynomially bounded weights -/

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- A weight on the nonzero frequencies of polynomial growth. -/
def PolyB (q : {ν : SInt 𝔪 // ν ≠ 0} → ℂ) : Prop :=
  ∃ (p : ℕ) (C : ℝ), ∀ ν : {ν : SInt 𝔪 // ν ≠ 0},
    ‖q ν‖ ≤ C * ∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p

/-! ### One place, along `curveN` -/

/-! ### One place, along `curveW`: the Weyl flip -/

end

end ArtinKP.GW
end

section
-- module Solutions.Artin.KP.GW_Main
/-! # WP-GW, file 2: the multi-place Weyl flip for `θ̃_Ψ`

* `cx c ζ`, `cv c ζ`: the point `(c_w(ζ_w))_w` of `X` in ambient coordinates, for a family of
  curves `c w : ℂ → ℂ × ℝ` (one in each place); `Aterm z c ζ = z·ht^{2/3}` along the curves.
* **`DList_curve`**: induction over a list of places.  If in each place the type-`m_w` derivative
  at `0` of every polynomially weighted series along `c w` is the series with the weight
  multiplied by `μ_w` (hypothesis `H1`), and the heights of the curves are stationary at `0`, then
  `DList m l (ζ ↦ z·ht^{2/3} + serA Ψ q)(ζ) = serA Ψ (q·∏_{w ∈ l} μ_w)` at every `ζ` vanishing on
  `l` (`l` without repetitions, nonempty: the constant term dies at the innermost operator).
* **`Dm_thetaT_curveW`**, **`Dm_thetaT_curveN`**: the mixed derivative of type `m` of `θ̃_Ψ` along
  `K.curveW` (for `m = ±1`), resp. along `K.curveN` (all `m`), as termwise series.
* **`weyl_flip_thetaT`**: stub G2a-2, with the statement of `G2a_Stubs.lean` verbatim.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GW

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
open ArtinKP.G2a

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### Families of curves -/

/-- The `x`-coordinates of the point `(c_w(ζ_w))_w`. -/
def cx (c : InfinitePlace F → ℂ → ℂ × ℝ) (ζ : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun w => (c w (ζ w)).1

/-- The `v`-coordinates of the point `(c_w(ζ_w))_w`. -/
def cv (c : InfinitePlace F → ℂ → ℂ × ℝ) (ζ : InfinitePlace F → ℂ) : InfinitePlace F → ℝ :=
  fun w => (c w (ζ w)).2

/-- The constant term `z·ht^{2/3}` along the curves. -/
def Aterm (z : ℂ) (c : InfinitePlace F → ℂ → ℂ × ℝ) (ζ : InfinitePlace F → ℂ) : ℂ :=
  z * ((∏ w, cv c ζ w : ℝ) : ℂ) ^ (2 / 3 : ℂ)

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-! ### The two curves -/

/-- (Same statement as `G2a.curveW_pos` of `G2a_Stubs.lean`, which cannot be imported.) -/
lemma curveW_pos (x : ℂ) {y : ℂ} (hy : y ≠ 0) (ζ : ℂ) : 0 < (curveW x y ζ).2 := by
  unfold curveW
  have : 0 < ‖y‖ := norm_pos_iff.mpr hy
  positivity

/-- (Same statement as `G2a.curveN_pos` of `G2a_Stubs.lean`.) -/
lemma curveN_pos (x : ℂ) {y : ℂ} (hy : y ≠ 0) (ζ : ℂ) : 0 < (curveN x y ζ).2 := by
  unfold curveN
  have : 0 < ‖y‖ := norm_pos_iff.mpr hy
  positivity

end

end ArtinKP.GW
end

section
-- module Solutions.Artin.KP.HB_Dig
/-! # WP-HB, file 1: the per-digit coefficient at the frequency `ν` itself

MATH3 §3.4, §6.2.  HA's `H.digCoef g (⟨𝔟,h𝔟⟩,1) v (H0.rowOf h𝔪 g ν)` takes the unit parts `t_P`
from the row representative `rowElt (rowOf ν) = ν / u⁶`; the true per-digit coefficient of the
reflected expansion is not `U_S⁶`-invariant (at a nonzero digit with `e = 0` it contains the
additive phase `ladd_P(t_P / ṽ_P)`).  Here:

* `eNu`, `tNu`, `digCoefNu`: the same product with `t_P = (ν / b²) · p_P^{−e₀}` taken from `ν`;
* `Eloc_unit_six`: `Eloc_P(k, e₀, t u⁶) = Eloc_P(k, e₀, t)` for a `P`-unit `t`, `u ∈ U_S`
  (from `L3V.Rsum_monomial`, `L3V.Wsph_eq`, `C3I.sext_unit_six`);
* `sum_maskProd_digLoc`: the mask-weighted digit sum of a product of `digLoc`s is the product of
  the `Eloc`s, for arbitrary exponents and unit parts (HA's `sum_maskProd_digCoef`, generalized);
* `sum_maskProd_digCoefNu`: `∑_v maskProd(v) · digCoefNu(v, ν) = Eprod g (𝔟,1) (rowOf ν)`
  (needs good primes: `12 ∣ n`, `N₀ ≥ cutN`). -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Local: invariance of `Eloc` under sixth powers of `S`-units -/

/-! ### The coefficient at `ν` -/

/-- `e₀ = v_P(ν) − 2 v_P(𝔟)` (with `v_P(ν)` read off the row class of `ν`). -/
def eNu (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (ν : {ν : SInt 𝔪 // ν ≠ 0})
    (P : Ideal (𝓞 F)) : ℤ :=
  ((normalizedFactors (H0.rowOf h𝔪 g ν).1.1).count P : ℤ) -
    2 * ((normalizedFactors 𝔟).count P : ℤ)

/-- `t_P = (ν / b²) · p_P^{−e₀}`: the unit part at `P` of the reflected frequency, from `ν`. -/
def tNu (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (ν : {ν : SInt 𝔪 // ν ≠ 0})
    (P : Ideal (𝓞 F)) : F :=
  (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) * (g.gen P : F) ^ (-(eNu h𝔪 g 𝔟 ν P))

/-- **The reflected exterior coefficient of the digit vector `v` at the frequency `ν`**
(MATH3 §6.2): `H.digCoef` with the unit parts taken from `ν` instead of its row representative. -/
def digCoefNu (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟)
    (ν : {ν : SInt 𝔪 // ν ≠ 0}) : ℂ :=
  ∏ P ∈ (normalizedFactors ((H0.rowOf h𝔪 g ν).1.1 * 𝔟)).toFinset,
    H.digLoc g 𝔟 v P (eNu h𝔪 g 𝔟 ν P) (tNu h𝔪 g 𝔟 ν P)

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_Aut
/-! # WP-HB, file 2: the repaired contract `AutInput2`, and `AutCut2 → KPCutNu`

`H.AutInput.reflected` is false as stated (MATH3 §3.4): its coefficient
`H.digCoef g (⟨𝔟,h𝔟⟩,1) v (H0.rowOf h𝔪 g ν)` is a function of the row class of `ν`, while the true
per-digit coefficient contains `sAddChar(μ a / c)`, which is not `U_S⁶`-invariant.  `AutInput2` is
`H.AutInput` with `reflected` stated with `HB.digCoefNu h𝔪 g 𝔟 v ν` (unit parts from `ν` itself).
All other fields are unchanged; they were re-examined against MATH3 §1–§4 (see `WP-HB.md`):

* `Θ : F → SModel 𝔪 k → ℂ` and the digit points `x = eps · x_v`: MATH3 §1.1, §3.1 (`eps = −1`);
* `forward`: MATH3 §1.3 (character `sAddChar(−ν x)`, coefficient `coefF' g ⊤ (rowOf ν)`, argument
  `sEmb ν + y`);
* `reflected`: frequency `ν / b²`, class argument `[ν / b²]`, `S`-argument `sEmb(ν / b²) − y`:
  MATH3 (2.4), (4.1) with `ν = μ (b / c_v)²`.

`cut_identity2`: summing over the digit vectors against the masks gives the identity of
`H0.KPCutNu` (HA's forward digit sum; `HB.sum_maskProd_digCoefNu` on the reflected side).
`KPCutNu_of_autInput2`: the cut. -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-- **The repaired contract for the automorphic packages** (one `𝔪`, `g`, level `k`, profile `κ`,
type `m`, function `J`). See the module documentation, `MATH3.md` and `WP-HB.md`. -/
structure AutInput2 (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (k : ℕ) (κ : ℝ → ℝ)
    (m : InfinitePlace F → ℤ) (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) where
  /-- `Θ(x, y)`, `x ∈ F`: MATH3 §1.1 (the type-`m` derivative of the theta function of the
  section `nT(−x) Φ_{y_f}` at `(emb(−x), |Y(y)|)`); only its values at digit points are used -/
  Θ : F → SModel 𝔪 k → ℂ
  /-- the orientation of the digit points: the expansions are at `x = eps · x_v`.  With the
  tree's Weyl element `wMat` the value is `−1` (MATH3 §3.3); `1` is the other Weyl element -/
  eps : SInt 𝔪
  eps_eq : eps = 1 ∨ eps = -1
  /-- the Fourier expansion at `a(y)`, at a digit point (MATH3 §1.3) -/
  forward : ∀ (𝔟 : Ideal (𝓞 F)) (_ : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟) (y : SModel 𝔪 k),
    Θ ((eps : F) * H.xdig g 𝔟 v) y =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        sAddChar 𝔪 (-(((ν : SInt 𝔪) : F) * ((eps : F) * H.xdig g 𝔟 v))) *
          (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g ν) * L3X.fpF κ m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y))
  /-- the Fourier expansion at `w · a(y)`, at a digit point, with the per-digit coefficient at
  `ν` itself (MATH3 (2.4), (D), (4.1)) -/
  reflected : ∀ (𝔟 : Ideal (𝓞 F)) (_ : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟) (y : SModel 𝔪 k),
    Θ ((eps : F) * H.xdig g 𝔟 v) y =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
        digCoefNu h𝔪 g 𝔟 v ν *
          H0.FmOf κ m J
            (QuotientAddGroup.mk (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2)).2.2)
            (sEmb 𝔪 k (((ν : SInt 𝔪) : F) / (g.gen 𝔟 : F) ^ 2) - y)

/-- The cut `H0.KPCutNu` with its last clause (the identity of the two sums for every `𝔟`, `y`)
replaced by `Nonempty (AutInput2 …)`: what the automorphic packages must prove. -/
def AutCut2 (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥), SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (c α : ℝ), 0 < c ∧ 0 < α ∧ α ≤ 5 / 6 ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ cl y, ‖J cl y‖ ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      Nonempty (AutInput2 h𝔪 g k (K.kappaB c) m J)

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_C
/-! # WP-HB, file 4: the element `c_v` of a digit vector

MATH3 §3.1.  For a digit vector `v ∈ Dig 𝔪 𝔟`: `D = {P ∣ 𝔟 : v_P ≠ 0}`,
`c_v = ∏_{P ∈ D} gen P = cdig g 𝔟 v` (as a product over all `P ∣ 𝔟` of `cfac P ∈ {1, gen P}`),
`ccof P = c_v / cfac P`.

* `val_cdig`, `vP_cdig`: `v_P(c_v) = 1` for `P ∈ D` and `0` at the other exterior primes;
* `cubicExt_cdig`: `(d / c_v) = ∏_{P ∈ D} χ_P(d)²` (so `κ(γ) = ∏_{P ∈ D} χ_P(d)^{−2}`);
* `exists_pf`: partial fractions, `e(r / c_v) = ∏_{P ∈ D} e(r m_P / p_P)` with
  `m_P · ccof P ≡ 1 mod P`.

(`res_cdig_xdig` is in `HB_Loc`, `exists_gamma` in `HB_Refl`.) -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-- The primes of `𝔟` (the index set of the digits). -/
abbrev PIdx (𝔟 : Ideal (𝓞 F)) : Type _ :=
  {P : Ideal (𝓞 F) // P ∈ (normalizedFactors 𝔟).toFinset}

/-- The factor of `c_v` at `P ∣ 𝔟`: `gen P` at a nonzero digit, `1` at a zero digit. -/
def cfac (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) (P : PIdx 𝔟) : SInt 𝔪 :=
  if v P = 0 then 1 else g.gen P.1

/-- `c_v = ∏_{P ∣ 𝔟, v_P ≠ 0} gen P`. -/
def cdig (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) : SInt 𝔪 :=
  ∏ P : PIdx 𝔟, cfac g 𝔟 v P

/-- `c_v / cfac P`. -/
def ccof (g : AllowedGen ι 𝔪) (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) (P : PIdx 𝔟) : SInt 𝔪 :=
  ∏ Q ∈ ({P}ᶜ : Finset (PIdx 𝔟)), cfac g 𝔟 v Q

/-- `P` carries a nonzero digit of `v`. -/
def Dnz (𝔟 : Ideal (𝓞 F)) (v : H.Dig 𝔪 𝔟) (P : Ideal (𝓞 F)) : Prop :=
  ∃ hP : P ∈ (normalizedFactors 𝔟).toFinset, v ⟨P, hP⟩ ≠ 0

/-! ### The Kubota symbol of `γ_v` -/

/-! ### Partial fractions -/

end

end ArtinKP.HB
end

section
-- module Solutions.Artin.KP.HB_Sec
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
/-! # WP-HB, file 9: the contract at the section level, `SecCut → AutCut2`

`SecCut n F ι` is `AutCut2` with `Nonempty (AutInput2 …)` replaced by what MATH3 §6.1 (6) gives
at the section level: a symbol package `Pk`, a function `Θ`, its forward expansion at every
`−x_v`, and its reflected expansion at the cusp `−x_v` for every `γ ∈ SL₂(R)` with bottom row
`(c_v, −c_v x_v)`, in the variable `μ ∈ R ∖ 0`, with coefficient
`coef^S(μ) · e(μ a / c_v) · κ(γ) · ⟨μ, c_v⟩` and argument `μ / c_v²`.
`autCut2_of_secCut` is the digit conversion (identity (D)); `eps = −1`. -/

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

/-- The cut with the two expansions of `Θ` in section-level form (MATH3 §6.1 (6):
`G.thetaG_forward` at `x = −x_v`, `G.thetaG_reflected` at `x = −x_v`, `γ = γ_v`). -/
def SecCut (n : ℕ)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥), SmallPrimesDvd N₀ 𝔪 →
    ∀ (g : AllowedGen ι 𝔪),
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ (c α : ℝ), 0 < c ∧ 0 < α ∧ α ≤ 5 / 6 ∧
    ∀ m : InfinitePlace F → ℤ, (∀ w, m w = 1 ∨ m w = -1) →
    ∃ (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (bf : SFin 𝔪 k → ℝ),
      (∀ cl y, ‖J cl y‖ ≤ bf y) ∧
      (∀ σ : ℝ, -α ≤ σ → Summable (fun y => bf y * (SFin.norm y) ^ σ)) ∧
      ∃ (Pk : CubicPkg F) (Θ : F → SModel 𝔪 k → ℂ),
        (∀ (𝔟 : Ideal (𝓞 F)) (_ : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟) (y : SModel 𝔪 k),
          Θ (-(H.xdig g 𝔟 v)) y =
            ∑' ν : {ν : SInt 𝔪 // ν ≠ 0},
              sAddChar 𝔪 (((ν : SInt 𝔪) : F) * H.xdig g 𝔟 v) *
                (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g ν) *
                  L3X.fpF (K.kappaB c) m (sEmb 𝔪 k ((ν : SInt 𝔪) : F) + y))) ∧
        (∀ (𝔟 : Ideal (𝓞 F)) (_ : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
          (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)), γ.1 1 0 = cdig g 𝔟 v →
          ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v) → ∀ y : SModel 𝔪 k,
          Θ (-(H.xdig g 𝔟 v)) y = ∑' μ : {x : SInt 𝔪 // x ≠ 0},
            (L3X.coefF' g ⊤ (H0.rowOf h𝔪 g μ) *
              sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / (cdig g 𝔟 v : F)) *
              kappa ι 𝔪 γ * brk ι Pk 𝔪 ((μ : SInt 𝔪) : F) (cdig g 𝔟 v : F)) *
            H0.FmOf (K.kappaB c) m J
              (QuotientAddGroup.mk
                (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / (cdig g 𝔟 v : F) ^ 2)).2.2)
              (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / (cdig g 𝔟 v : F) ^ 2) - y))

end

end ArtinKP.HB
end


