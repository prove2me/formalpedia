-- Prove2me | solution 1 for AlgebraicCurve.map_ne_zero_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4fe1634c-84e8-5e86-a90b-327e598fbda7

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_map_ne_zero_of_tame
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext deg adicValuation adicValuation_ne_zero ord ord_one ord_mul ord_inv ord_coe_unit ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring ramificationIndex ramificationIndex_pos restrict ord_restrict fiber mem_fiber dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg~mem_iff_ord_nonneg"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n
theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)
theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩
end Place
end AlgebraicCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

scoped instance instSumRamificationInertia_port {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [HasPrincipalDivisors K F'] : SumRamificationInertia K F F' :=
  ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg v⟩
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

variable (K F F') in

def CanonicalDifferentDegree (d : ℚ) : Prop :=
  ∀ [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (_ : ω ≠ 0) {ω' : Ω[F'⁄K]} (_ : ω' ≠ 0),
      (Divisor.degree (canonicalDivisorOf (K := K) ‹ω' ≠ 0›
        - Divisor.pullback F' (canonicalDivisorOf (K := K) ‹ω ≠ 0›)) : ℚ) = d

theorem degree_canonicalDivisor_relation_of_canonicalDifferentDegree
    [FundamentalIdentity K F F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {d : ℚ} (h : CanonicalDifferentDegree K F F' d)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0) :
    (Divisor.degree (canonicalDivisorOf (K := K) hω') : ℚ)
      = (Module.finrank F F' : ℚ)
          * (Divisor.degree (canonicalDivisorOf (K := K) hω) : ℚ) + d := by
  have hd := h hω hω'
  rw [map_sub, Divisor.degree_pullback] at hd
  push_cast at hd
  linarith

theorem canonicalDifferentDegree_of_degree_canonicalDivisor_relation
    [FundamentalIdentity K F F'] {d : ℚ}
    (h : ∀ [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
      {ω : Ω[F⁄K]} (_ : ω ≠ 0) {ω' : Ω[F'⁄K]} (_ : ω' ≠ 0),
        (Divisor.degree (canonicalDivisorOf (K := K) ‹ω' ≠ 0›) : ℚ)
          = (Module.finrank F F' : ℚ)
              * (Divisor.degree (canonicalDivisorOf (K := K) ‹ω ≠ 0›) : ℚ) + d) :
    CanonicalDifferentDegree K F F' d := by
  intro _ _ ω hω ω' hω'
  have hrel := h hω hω'
  rw [map_sub, Divisor.degree_pullback]
  push_cast
  linarith

theorem canonicalDifferentDegree_iff_degreeRelation [FundamentalIdentity K F F'] {d : ℚ} :
    CanonicalDifferentDegree K F F' d
      ↔ ∀ [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
          {ω : Ω[F⁄K]} (_ : ω ≠ 0) {ω' : Ω[F'⁄K]} (_ : ω' ≠ 0),
            (Divisor.degree (canonicalDivisorOf (K := K) ‹ω' ≠ 0›) : ℚ)
              = (Module.finrank F F' : ℚ)
                  * (Divisor.degree (canonicalDivisorOf (K := K) ‹ω ≠ 0›) : ℚ) + d :=
  ⟨fun h _ _ _ hω _ hω' =>
    degree_canonicalDivisor_relation_of_canonicalDifferentDegree h hω hω',
   canonicalDifferentDegree_of_degree_canonicalDivisor_relation⟩

theorem canonicalDifferentDegree_unique {d d' : ℚ}
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0)
    (h : CanonicalDifferentDegree K F F' d) (h' : CanonicalDifferentDegree K F F' d') :
    d = d' := by
  have hd := h hω hω'
  have hd' := h' hω hω'
  linarith

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "degree degree_single IsPrincipal principal pushforward pullback pullback_apply isPrincipal_pullback degree_pullback"
p2m_open "AlgebraicCurve.Divisor"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_zero_of_isPrincipal' [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D.IsPrincipal) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨D₀, hD₀, hdeg₀⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
  rw [show D = D₀ from Finsupp.ext fun v => (hDf v).trans (hD₀ v).symm]
  exact hdeg₀

end Divisor
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

variable (K F F') in

def HurwitzCanonicalDecomposition (𝔡 : Divisor K F') : Prop :=
  ∀ [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (_ : ω ≠ 0) {ω' : Ω[F'⁄K]} (_ : ω' ≠ 0),
      (canonicalDivisorOf (K := K) ‹ω' ≠ 0›
        - Divisor.pullback F' (canonicalDivisorOf (K := K) ‹ω ≠ 0›) - 𝔡).IsPrincipal

theorem canonicalDifferentDegree_of_hurwitzCanonicalDecomposition
    {𝔡 : Divisor K F'} (h : HurwitzCanonicalDecomposition K F F' 𝔡) :
    CanonicalDifferentDegree K F F' (Divisor.degree 𝔡 : ℚ) := by
  intro _ _ ω hω ω' hω'
  have hd := Divisor.degree_eq_zero_of_isPrincipal' (h hω hω')
  rw [map_sub, map_sub] at hd
  have : (Divisor.degree (canonicalDivisorOf (K := K) hω'
      - Divisor.pullback F' (canonicalDivisorOf (K := K) hω)) : ℚ)
        - (Divisor.degree 𝔡 : ℚ) = 0 := by
    rw [map_sub]; push_cast; exact_mod_cast hd
  linarith

theorem canonicalDifferentDegree_of_hurwitz_of_degree_eq {𝔡 : Divisor K F'} {d : ℚ}
    (hH : HurwitzCanonicalDecomposition K F F' 𝔡) (hdeg : (Divisor.degree 𝔡 : ℚ) = d) :
    CanonicalDifferentDegree K F F' d :=
  hdeg ▸ canonicalDifferentDegree_of_hurwitzCanonicalDecomposition hH

theorem degree_eq_of_canonicalDifferentDegree_of_hurwitz
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0)
    {𝔡 : Divisor K F'} {d : ℚ}
    (hH : HurwitzCanonicalDecomposition K F F' 𝔡)
    (hCD : CanonicalDifferentDegree K F F' d) :
    (Divisor.degree 𝔡 : ℚ) = d :=
  canonicalDifferentDegree_unique hω hω'
    (canonicalDifferentDegree_of_hurwitzCanonicalDecomposition hH) hCD

theorem canonicalDifferentDegree_iff_degree_eq_of_hurwitz
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0)
    {𝔡 : Divisor K F'} (hH : HurwitzCanonicalDecomposition K F F' 𝔡) {d : ℚ} :
    CanonicalDifferentDegree K F F' d ↔ (Divisor.degree 𝔡 : ℚ) = d :=
  ⟨degree_eq_of_canonicalDifferentDegree_of_hurwitz hω hω' hH,
   canonicalDifferentDegree_of_hurwitz_of_degree_eq hH⟩

theorem degree_eq_of_hurwitzCanonicalDecomposition
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0)
    {𝔡₁ 𝔡₂ : Divisor K F'}
    (h₁ : HurwitzCanonicalDecomposition K F F' 𝔡₁)
    (h₂ : HurwitzCanonicalDecomposition K F F' 𝔡₂) :
    Divisor.degree 𝔡₁ = Divisor.degree 𝔡₂ := by
  have e := canonicalDifferentDegree_unique hω hω'
    (canonicalDifferentDegree_of_hurwitzCanonicalDecomposition h₁)
    (canonicalDifferentDegree_of_hurwitzCanonicalDecomposition h₂)
  exact_mod_cast e

theorem degree_canonicalDivisor_relation_of_hurwitzCanonicalDecomposition
    [FundamentalIdentity K F F']
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {𝔡 : Divisor K F'} (h : HurwitzCanonicalDecomposition K F F' 𝔡)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0) :
    (Divisor.degree (canonicalDivisorOf (K := K) hω') : ℚ)
      = (Module.finrank F F' : ℚ)
          * (Divisor.degree (canonicalDivisorOf (K := K) hω) : ℚ)
        + (Divisor.degree 𝔡 : ℚ) :=
  degree_canonicalDivisor_relation_of_canonicalDifferentDegree
    (canonicalDifferentDegree_of_hurwitzCanonicalDecomposition h) hω hω'

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section TameDifferent

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

variable (K F) in

noncomputable def tameDifferentDivisor (S : Finset (Place K F')) : Divisor K F' :=
  ∑ w ∈ S, Finsupp.single w ((w.ramificationIndex F : ℤ) - 1)

@[scoped simp]
theorem tameDifferentDivisor_empty :
    tameDifferentDivisor K F (∅ : Finset (Place K F')) = 0 := by
  unfold tameDifferentDivisor; exact Finset.sum_empty

theorem degree_tameDifferentDivisor (S : Finset (Place K F')) :
    Divisor.degree (tameDifferentDivisor K F S)
      = ∑ w ∈ S, ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) := by
  unfold tameDifferentDivisor
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => Divisor.degree_single w _

theorem degree_tameDifferentDivisor_of_deg_eq_one {S : Finset (Place K F')}
    (hdeg1 : ∀ w ∈ S, (w.deg : ℤ) = 1) :
    Divisor.degree (tameDifferentDivisor K F S)
      = ∑ w ∈ S, ((w.ramificationIndex F : ℤ) - 1) := by
  rw [degree_tameDifferentDivisor]
  exact Finset.sum_congr rfl fun w hw => by rw [hdeg1 w hw, mul_one]

theorem tameDifferentDivisor_subset_unramified {S T : Finset (Place K F')}
    (hST : S ⊆ T) (hunram : ∀ w ∈ T, w ∉ S → w.ramificationIndex F = 1) :
    tameDifferentDivisor K F T = tameDifferentDivisor K F S := by
  unfold tameDifferentDivisor
  exact (Finset.sum_subset hST fun w hwT hwS => by rw [hunram w hwT hwS]; simp).symm

theorem tameDifferentDivisor_eq_of_unramified_compl {S T : Finset (Place K F')}
    (hS : ∀ w : Place K F', w ∉ S → w.ramificationIndex F = 1)
    (hT : ∀ w : Place K F', w ∉ T → w.ramificationIndex F = 1) :
    tameDifferentDivisor K F S = tameDifferentDivisor K F T := by
  classical
  have h1 : tameDifferentDivisor K F (S ∪ T) = tameDifferentDivisor K F S :=
    tameDifferentDivisor_subset_unramified (Finset.subset_union_left (s₂ := T))
      fun w _ hwS => hS w hwS
  have h2 : tameDifferentDivisor K F (S ∪ T) = tameDifferentDivisor K F T :=
    tameDifferentDivisor_subset_unramified (Finset.subset_union_right (s₁ := S))
      fun w _ hwT => hT w hwT
  exact h1.symm.trans h2

theorem degree_tameDifferentDivisor_disjUnion {S T : Finset (Place K F')}
    (hdisj : Disjoint S T) :
    Divisor.degree (tameDifferentDivisor K F (S.disjUnion T hdisj))
      = Divisor.degree (tameDifferentDivisor K F S)
        + Divisor.degree (tameDifferentDivisor K F T) := by
  simp only [degree_tameDifferentDivisor]
  exact Finset.sum_disjUnion hdisj

end TameDifferent
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

theorem hurwitzDifferentAssembly_of_tameDifferent {S : Finset (Place K F')} {d : ℚ}
    (hH : HurwitzCanonicalDecomposition K F F' (tameDifferentDivisor K F S))
    (hsum : ((∑ w ∈ S, ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) : ℤ) : ℚ) = d) :
    ∃ 𝔡 : Divisor K F',
      HurwitzCanonicalDecomposition K F F' 𝔡 ∧ (Divisor.degree 𝔡 : ℚ) = d :=
  ⟨tameDifferentDivisor K F S, hH, by rw [degree_tameDifferentDivisor]; exact hsum⟩

theorem canonicalDifferentDegree_of_tameDifferent {S : Finset (Place K F')} {d : ℚ}
    (hH : HurwitzCanonicalDecomposition K F F' (tameDifferentDivisor K F S))
    (hsum : ((∑ w ∈ S, ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) : ℤ) : ℚ) = d) :
    CanonicalDifferentDegree K F F' d :=
  canonicalDifferentDegree_of_hurwitz_of_degree_eq hH
    (by rw [degree_tameDifferentDivisor]; exact hsum)

theorem sum_eq_of_canonicalDifferentDegree_of_tameDifferentHurwitz
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0)
    {S : Finset (Place K F')} {d : ℚ}
    (hH : HurwitzCanonicalDecomposition K F F' (tameDifferentDivisor K F S))
    (hCD : CanonicalDifferentDegree K F F' d) :
    ((∑ w ∈ S, ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) : ℤ) : ℚ) = d := by
  have := degree_eq_of_canonicalDifferentDegree_of_hurwitz hω hω' hH hCD
  rwa [degree_tameDifferentDivisor] at this

theorem sum_eq_of_hurwitz_tameDifferent
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {ω' : Ω[F'⁄K]} (hω' : ω' ≠ 0)
    {S₁ S₂ : Finset (Place K F')}
    (h₁ : HurwitzCanonicalDecomposition K F F' (tameDifferentDivisor K F S₁))
    (h₂ : HurwitzCanonicalDecomposition K F F' (tameDifferentDivisor K F S₂)) :
    ∑ w ∈ S₁, ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ)
      = ∑ w ∈ S₂, ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) := by
  have e := degree_eq_of_hurwitzCanonicalDecomposition hω hω' h₁ h₂
  rwa [degree_tameDifferentDivisor, degree_tameDifferentDivisor] at e

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section TameApply

variable (K : Type*) {F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

theorem tameDifferentDivisor_apply_of_mem {S : Finset (Place K F')} {w : Place K F'}
    (hw : w ∈ S) :
    (tameDifferentDivisor K F S) w = (w.ramificationIndex F : ℤ) - 1 := by
  simp only [tameDifferentDivisor, Finset.sum_apply']
  refine (Finset.sum_eq_single_of_mem (f := fun v => (Finsupp.single v
      ((v.ramificationIndex F : ℤ) - 1)) w) w hw ?_).trans Finsupp.single_eq_same
  exact fun v _ hvw => Finsupp.single_eq_of_ne hvw.symm

theorem tameDifferentDivisor_apply_of_notMem {S : Finset (Place K F')} {w : Place K F'}
    (hw : w ∉ S) :
    (tameDifferentDivisor K F S) w = 0 := by
  simp only [tameDifferentDivisor, Finset.sum_apply']
  exact Finset.sum_eq_zero fun v hv =>
    Finsupp.single_eq_of_ne (fun h => hw (h ▸ hv) : w ≠ v)

end TameApply
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section LocalExponent

variable (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

def LocalHurwitzExponent (ω₀ : Ω[F⁄K]) (ω₀' : Ω[F'⁄K]) (𝔡 : Divisor K F') : Prop :=
  ∀ w : Place K F',
    w.ordDifferential ω₀'
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀ + 𝔡 w

variable {K F F'}

theorem canonicalDivisorOf_eq_of_localHurwitzExponent
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {ω₀' : Ω[F'⁄K]} (hω₀' : ω₀' ≠ 0)
    {𝔡 : Divisor K F'} (hL : LocalHurwitzExponent K F F' ω₀ ω₀' 𝔡) :
    canonicalDivisorOf (K := K) hω₀'
      = Divisor.pullback F' (canonicalDivisorOf (K := K) hω₀) + 𝔡 := by
  refine Finsupp.ext fun w => ?_
  rw [Finsupp.add_apply, canonicalDivisorOf_apply, Divisor.pullback_apply,
    canonicalDivisorOf_apply, hL w]

theorem localHurwitzExponent_of_canonicalDivisorOf_eq
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {ω₀' : Ω[F'⁄K]} (hω₀' : ω₀' ≠ 0)
    {𝔡 : Divisor K F'}
    (hexact : canonicalDivisorOf (K := K) hω₀'
      = Divisor.pullback F' (canonicalDivisorOf (K := K) hω₀) + 𝔡) :
    LocalHurwitzExponent K F F' ω₀ ω₀' 𝔡 := fun w => by
  have := DFunLike.congr_fun hexact w
  rwa [Finsupp.add_apply, canonicalDivisorOf_apply, Divisor.pullback_apply,
    canonicalDivisorOf_apply] at this

end LocalExponent
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section VariationPrincipal

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def CanonicalDivisorVariationPrincipal : Prop :=
  ∀ [HasCanonicalDivisor (K := K) (F := F)]
    {ω₁ : Ω[F⁄K]} (_ : ω₁ ≠ 0) {ω₂ : Ω[F⁄K]} (_ : ω₂ ≠ 0),
      (canonicalDivisorOf (K := K) ‹ω₁ ≠ 0›
        - canonicalDivisorOf (K := K) ‹ω₂ ≠ 0›).IsPrincipal

end VariationPrincipal
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section CoreEngine

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

theorem hurwitzCanonicalDecomposition_of_localHurwitzExponent
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {ω₀' : Ω[F'⁄K]} (hω₀' : ω₀' ≠ 0)
    {𝔡 : Divisor K F'} (hL : LocalHurwitzExponent K F F' ω₀ ω₀' 𝔡)
    (hVF : CanonicalDivisorVariationPrincipal K F)
    (hVF' : CanonicalDivisorVariationPrincipal K F') :
    HurwitzCanonicalDecomposition K F F' 𝔡 := by
  intro _ _ ω hω ω' hω'

  have hexact := canonicalDivisorOf_eq_of_localHurwitzExponent hω₀ hω₀' hL

  have hkey : canonicalDivisorOf (K := K) hω'
        - Divisor.pullback F' (canonicalDivisorOf (K := K) hω) - 𝔡
      = (canonicalDivisorOf (K := K) hω' - canonicalDivisorOf (K := K) hω₀')
        - Divisor.pullback F'
            (canonicalDivisorOf (K := K) hω - canonicalDivisorOf (K := K) hω₀) := by
    rw [map_sub, hexact]; abel
  rw [hkey]

  exact Divisor.principal.sub_mem (hVF' hω' hω₀')
    (Divisor.isPrincipal_pullback (hVF hω hω₀))

theorem canonicalDivisorVariationPrincipal_cover_of_hurwitzCanonicalDecomposition
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    {𝔡 : Divisor K F'}
    (hH : HurwitzCanonicalDecomposition K F F' 𝔡)
    {ω₁' : Ω[F'⁄K]} (hω₁' : ω₁' ≠ 0) {ω₂' : Ω[F'⁄K]} (hω₂' : ω₂' ≠ 0) :
    (canonicalDivisorOf (K := K) hω₁' - canonicalDivisorOf (K := K) hω₂').IsPrincipal := by
  have h1 := hH hω₀ hω₁'
  have h2 := hH hω₀ hω₂'
  have hkey : canonicalDivisorOf (K := K) hω₁' - canonicalDivisorOf (K := K) hω₂'
      = (canonicalDivisorOf (K := K) hω₁'
          - Divisor.pullback F' (canonicalDivisorOf (K := K) hω₀) - 𝔡)
        - (canonicalDivisorOf (K := K) hω₂'
          - Divisor.pullback F' (canonicalDivisorOf (K := K) hω₀) - 𝔡) := by abel
  rw [hkey]; exact Divisor.principal.sub_mem h1 h2

end CoreEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section TameSpecialization

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

theorem localHurwitzExponent_tameDifferent_iff {ω₀ : Ω[F⁄K]} {ω₀' : Ω[F'⁄K]}
    {S : Finset (Place K F')} :
    LocalHurwitzExponent K F F' ω₀ ω₀' (tameDifferentDivisor K F S)
      ↔ (∀ w ∈ S, w.ordDifferential ω₀'
            = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
              + ((w.ramificationIndex F : ℤ) - 1))
        ∧ (∀ w ∉ S, w.ordDifferential ω₀'
            = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀) := by
  constructor
  · intro hL
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · have := hL w; rwa [tameDifferentDivisor_apply_of_mem K hw] at this
    · have := hL w; rwa [tameDifferentDivisor_apply_of_notMem K hw, add_zero] at this
  · rintro ⟨hin, hout⟩ w
    by_cases hw : w ∈ S
    · rw [tameDifferentDivisor_apply_of_mem K hw]; exact hin w hw
    · rw [tameDifferentDivisor_apply_of_notMem K hw, add_zero]; exact hout w hw

theorem localHurwitzExponent_tameDifferent_of_universal {ω₀ : Ω[F⁄K]} {ω₀' : Ω[F'⁄K]}
    {S : Finset (Place K F')}
    (hram : ∀ w : Place K F', w ∉ S → w.ramificationIndex F = 1)
    (huniv : ∀ w : Place K F', w.ordDifferential ω₀'
        = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + ((w.ramificationIndex F : ℤ) - 1)) :
    LocalHurwitzExponent K F F' ω₀ ω₀' (tameDifferentDivisor K F S) := by
  refine localHurwitzExponent_tameDifferent_iff.mpr ⟨fun w _ => huniv w, fun w hw => ?_⟩
  have huw := huniv w
  rw [hram w hw, Nat.cast_one, one_mul] at huw ⊢
  linarith

end TameSpecialization
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section Gates

set_option linter.unusedSectionVars false

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

end Gates
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section RankOne

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place p2m_export "AlgebraicCurve.Place" "ext deg adicValuation adicValuation_ne_zero ord ord_one ord_mul ord_inv ord_coe_unit ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring ramificationIndex ramificationIndex_pos restrict ord_restrict fiber mem_fiber dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero sum_ramificationIndex_mul_inertiaDeg" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_ne_zero' (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  have := v.differentialCoeff_smul_dCoord ω
  rw [h, zero_smul] at this
  exact hω this.symm

end Place
p2m_export "AlgebraicCurve" "Place.differentialCoeff_ne_zero'"
namespace IsCurveOver p2m_export "AlgebraicCurve.IsCurveOver" "hasPrincipalDivisors finrank_kaehler kaehler_free_rank_one" end IsCurveOver
p2m_open_scoped "AlgebraicCurve.IsCurveOver" in

theorem IsCurveOver.exists_smul_eq [IsCurveOver K F]
    {ω₁ : Ω[F⁄K]} (hω₁ : ω₁ ≠ 0) {ω₂ : Ω[F⁄K]} (hω₂ : ω₂ ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ ω₂ = c • ω₁ := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one IsCurveOver.finrank_kaehler hω₁ ω₂
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl; exact hω₂ (by rw [← hc, zero_smul])

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ordDifferential_smul_sub (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDifferential (c • ω) - v.ordDifferential ω = v.ord c := by
  rw [v.ordDifferential_smul hc (v.differentialCoeff_ne_zero' hω)]; ring

end Place
p2m_export "AlgebraicCurve" "Place.ordDifferential_smul_sub"
end RankOne
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section VariationDischarge

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem canonicalDivisorOf_smul_sub_isPrincipal
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (canonicalDivisorOf (K := K) (show c • ω ≠ 0 from smul_ne_zero hc hω)
      - canonicalDivisorOf (K := K) hω).IsPrincipal :=
  ⟨c, hc, fun v => by
    rw [Finsupp.sub_apply, canonicalDivisorOf_apply, canonicalDivisorOf_apply,
      v.ordDifferential_smul_sub hc hω]⟩

theorem canonicalDivisorVariationPrincipal_of_isCurveOver
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] :
    CanonicalDivisorVariationPrincipal K F := by
  intro _ ω₁ hω₁ ω₂ hω₂
  obtain ⟨c, hc, rfl⟩ := IsCurveOver.exists_smul_eq hω₂ hω₁
  exact canonicalDivisorOf_smul_sub_isPrincipal hc hω₂

end VariationDischarge
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section VFreeEngine

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

theorem hurwitzCanonicalDecomposition_of_localHurwitzExponent_of_isCurveOver
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {ω₀' : Ω[F'⁄K]} (hω₀' : ω₀' ≠ 0)
    {𝔡 : Divisor K F'} (hL : LocalHurwitzExponent K F F' ω₀ ω₀' 𝔡) :
    HurwitzCanonicalDecomposition K F F' 𝔡 :=
  hurwitzCanonicalDecomposition_of_localHurwitzExponent hω₀ hω₀' hL
    canonicalDivisorVariationPrincipal_of_isCurveOver
    canonicalDivisorVariationPrincipal_of_isCurveOver

end VFreeEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section KaehlerMap

variable (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

noncomputable abbrev kaehlerMap : Ω[F⁄K] →ₗ[F] Ω[F'⁄K] :=
  KaehlerDifferential.map K K F F'

variable {K F F'}

theorem kaehlerMap_dCoord (v : Place K F) :
    kaehlerMap K F F' v.dCoord
      = KaehlerDifferential.D K F' (algebraMap F F' v.uniformizer) := by
  unfold Place.dCoord; exact KaehlerDifferential.map_D K K F F' v.uniformizer

theorem kaehlerMap_eq_smul_dCoordImage (v : Place K F) [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    kaehlerMap K F F' ω
      = (algebraMap F F' (v.differentialCoeff ω))
          • KaehlerDifferential.D K F' (algebraMap F F' v.uniformizer) := by
  conv_lhs => rw [← v.differentialCoeff_smul_dCoord ω]
  rw [LinearMap.map_smul, kaehlerMap_dCoord,
    algebra_compatible_smul F' (v.differentialCoeff ω)]

end KaehlerMap
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section RestrictDCoord

variable {K : Type*} (F : Type*) {F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private noncomputable def _root_.AlgebraicCurve.Place.restrictDCoord (w : Place K F') : Ω[F'⁄K] :=
  KaehlerDifferential.D K F' (algebraMap F F' (w.restrict F).uniformizer)

end Place
p2m_export "AlgebraicCurve" "Place.restrictDCoord"
p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.restrictDCoord_eq_kaehlerMap (w : Place K F') :
    w.restrictDCoord F = kaehlerMap K F F' (w.restrict F).dCoord :=
  (kaehlerMap_dCoord (w.restrict F)).symm

variable (K F')

def TameLocalDifferentExponent : Prop :=
  ∀ w : Place K F',
    w.differentialCoeff (w.restrictDCoord F) ≠ 0
      ∧ w.ord (w.differentialCoeff (w.restrictDCoord F)) = (w.ramificationIndex F : ℤ) - 1

end RestrictDCoord
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section LFromTame

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

theorem differentialCoeff_kaehlerMap_eq (w : Place K F') [w.DCoordGenerates]
    [(w.restrict F).DCoordGenerates] [Nontrivial Ω[F'⁄K]] (ω₀ : Ω[F⁄K]) :
    w.differentialCoeff (kaehlerMap K F F' ω₀)
      = algebraMap F F' ((w.restrict F).differentialCoeff ω₀)
          * w.differentialCoeff (w.restrictDCoord F) := by
  rw [kaehlerMap_eq_smul_dCoordImage (w.restrict F) ω₀, w.differentialCoeff_smul]
  rfl

theorem ordDifferential_kaehlerMap_eq (w : Place K F') [w.DCoordGenerates]
    [(w.restrict F).DCoordGenerates] [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    (htame : w.differentialCoeff (w.restrictDCoord F) ≠ 0) :
    w.ordDifferential (kaehlerMap K F F' ω₀)
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + w.ord (w.differentialCoeff (w.restrictDCoord F)) := by
  set v := w.restrict F
  have hu : v.differentialCoeff ω₀ ≠ 0 := v.differentialCoeff_ne_zero' hω₀
  have hιu : algebraMap F F' (v.differentialCoeff ω₀) ≠ 0 := fun h =>
    hu ((algebraMap F F').injective (h.trans (map_zero _).symm))
  unfold Place.ordDifferential
  rw [differentialCoeff_kaehlerMap_eq w ω₀, w.ord_mul hιu htame,
    w.ord_restrict (F := F) (v.differentialCoeff ω₀)]

theorem kaehlerMap_ne_zero_of_tameAt [Nontrivial Ω[F⁄K]] [Nontrivial Ω[F'⁄K]]
    (w : Place K F') [w.DCoordGenerates] [(w.restrict F).DCoordGenerates]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    (htame : w.differentialCoeff (w.restrictDCoord F) ≠ 0) :
    kaehlerMap K F F' ω₀ ≠ 0 := by
  intro h0
  apply htame
  have hu : (w.restrict F).differentialCoeff ω₀ ≠ 0 :=
    (w.restrict F).differentialCoeff_ne_zero' hω₀
  have hιu : algebraMap F F' ((w.restrict F).differentialCoeff ω₀) ≠ 0 := fun h =>
    hu ((algebraMap F F').injective (h.trans (map_zero _).symm))
  have := differentialCoeff_kaehlerMap_eq w ω₀
  rw [h0, w.differentialCoeff_zero] at this
  exact (mul_eq_zero.mp this.symm).resolve_left hιu

theorem ordDifferential_kaehlerMap_universal
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (htame : TameLocalDifferentExponent K F F')
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (w : Place K F') :
    w.ordDifferential (kaehlerMap K F F' ω₀)
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + ((w.ramificationIndex F : ℤ) - 1) := by
  rw [ordDifferential_kaehlerMap_eq w hω₀ (htame w).1, (htame w).2]

theorem localHurwitzExponent_kaehlerMap_of_tameLocalDifferent
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (htame : TameLocalDifferentExponent K F F')
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    {S : Finset (Place K F')} (hram : ∀ w : Place K F', w ∉ S → w.ramificationIndex F = 1) :
    LocalHurwitzExponent K F F' ω₀ (kaehlerMap K F F' ω₀) (tameDifferentDivisor K F S) :=
  localHurwitzExponent_tameDifferent_of_universal hram
    (ordDifferential_kaehlerMap_universal htame hω₀)

theorem kaehlerMap_ne_zero_of_tameLocalDifferent
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (htame : TameLocalDifferentExponent K F F') (w₀ : Place K F')
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    kaehlerMap K F F' ω₀ ≠ 0 :=
  kaehlerMap_ne_zero_of_tameAt w₀ hω₀ (htame w₀).1

end LFromTame
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section HurwitzFromTame

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

theorem hurwitzCanonicalDecomposition_of_tameLocalDifferent
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
    [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (htame : TameLocalDifferentExponent K F F') (w₀ : Place K F')
    {S : Finset (Place K F')} (hram : ∀ w : Place K F', w ∉ S → w.ramificationIndex F = 1) :
    HurwitzCanonicalDecomposition K F F' (tameDifferentDivisor K F S) := by
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  exact hurwitzCanonicalDecomposition_of_localHurwitzExponent_of_isCurveOver hω₀
    (kaehlerMap_ne_zero_of_tameLocalDifferent htame w₀ hω₀)
    (localHurwitzExponent_kaehlerMap_of_tameLocalDifferent htame hω₀ hram)

end HurwitzFromTame
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section Gates

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

variable [Algebra.IsIntegral F F']

end Gates
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

set_option autoImplicit false

open IsDedekindDomain WithZero

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext deg adicValuation adicValuation_ne_zero ord ord_one ord_mul ord_inv ord_coe_unit ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring ramificationIndex ramificationIndex_pos restrict ord_restrict fiber mem_fiber dCoord DCoordGenerates differentialCoeff differentialCoeff_smul_dCoord differentialCoeff_unique differentialCoeff_zero differentialCoeff_smul ordDifferential ordDifferential_smul uniformizer ord_uniformizer uniformizer_ne_zero sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve.Place~ord_nonneg_of_mem~mem_of_ord_nonneg~mem_iff_ord_nonneg"

section Helpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap' (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have h₁ : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h₂ : 0 ≤ v.ord (algebraMap K F c)⁻¹ := by
    rw [← map_inv₀]; exact v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [v.ord_inv] at h₂; omega

p2m_export "AlgebraicCurve.Place" "ord_algebraMap'"

private theorem _root_.AlgebraicCurve.Place.ord_natCast' (n : ℕ) : v.ord (n : F) = 0 := by
  rw [← map_natCast (algebraMap K F) n]; exact v.ord_algebraMap' (n : K)

p2m_export "AlgebraicCurve.Place" "ord_natCast'"

private theorem _root_.AlgebraicCurve.Place.ord_pow' (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

p2m_export "AlgebraicCurve.Place" "ord_pow'"

private theorem _root_.AlgebraicCurve.Place.ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h : (2 : ℤ) * v.ord (-1 : F) = 0 := by
    have := v.ord_pow' (-1 : F) 2
    simp only [neg_one_sq, v.ord_one] at this
    omega
  rw [show (-f : F) = (-1 : F) * f from (neg_one_mul f).symm,
    v.ord_mul (neg_ne_zero.mpr one_ne_zero) hf]
  omega

p2m_export "AlgebraicCurve.Place" "ord_neg'"

private theorem _root_.AlgebraicCurve.Place.ord_add_eq_min' {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f ≠ v.ord g) : v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon; exact h (by simp only [Place.ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, map_zero] at h1
    rcases max_choice (v.adicValuation f) (v.adicValuation g) with hm | hm
    · exact (v.adicValuation_ne_zero hf) (h1 ▸ hm).symm
    · exact (v.adicValuation_ne_zero hg) (h1 ▸ hm).symm
  simp only [Place.ord, h1]
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    rw [hmax]; omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    rw [hmax]; omega

p2m_export "AlgebraicCurve.Place" "ord_add_eq_min'"

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_add' [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (ω₁ ω₂ : Ω[F⁄K]) :
    v.differentialCoeff (ω₁ + ω₂) = v.differentialCoeff ω₁ + v.differentialCoeff ω₂ :=
  v.differentialCoeff_unique (by
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

p2m_export "AlgebraicCurve.Place" "differentialCoeff_add'"

theorem exists_ord_eq_zero_mul_uniformizer_zpow {f : F} (hf : f ≠ 0) :
    ∃ u : F, u ≠ 0 ∧ v.ord u = 0 ∧ f = u * v.uniformizer ^ (v.ord f) := by
  set π₀ := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose
  have hπ₀ := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ₀
  refine ⟨((u : v.toValuationSubring) : F), ?_, v.ord_coe_unit u, ?_⟩
  · simp [ne_eq, ZeroMemClass.coe_eq_zero]
  · exact hu

end Helpers
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section PowerRule

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow (n : ℕ) :
    v.differentialCoeff (KaehlerDifferential.D K F (v.uniformizer ^ n))
      = (n : F) * v.uniformizer ^ (n - 1) := by
  refine v.differentialCoeff_unique ?_
  have key := (KaehlerDifferential.D K F).leibniz_pow v.uniformizer n
  rw [key, mul_smul, ← Nat.cast_smul_eq_nsmul F n]
  rfl

p2m_export "AlgebraicCurve.Place" "differentialCoeff_D_uniformizer_pow"

private theorem _root_.AlgebraicCurve.Place.ord_differentialCoeff_D_uniformizer_pow {n : ℕ} (hn : (n : F) ≠ 0) :
    v.ord (v.differentialCoeff (KaehlerDifferential.D K F (v.uniformizer ^ n)))
      = (n : ℤ) - 1 := by
  have hn' : n ≠ 0 := by rintro rfl; exact hn (by simp)
  rw [v.differentialCoeff_D_uniformizer_pow,
    v.ord_mul hn (pow_ne_zero _ v.uniformizer_ne_zero),
    v.ord_natCast' n, v.ord_pow', v.ord_uniformizer, zero_add, mul_one]
  omega

p2m_export "AlgebraicCurve.Place" "ord_differentialCoeff_D_uniformizer_pow"

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_D_uniformizer_pow_ne_zero {n : ℕ} (hn : (n : F) ≠ 0) :
    v.differentialCoeff (KaehlerDifferential.D K F (v.uniformizer ^ n)) ≠ 0 := by
  rw [v.differentialCoeff_D_uniformizer_pow]
  exact mul_ne_zero hn (pow_ne_zero _ v.uniformizer_ne_zero)

p2m_export "AlgebraicCurve.Place" "differentialCoeff_D_uniformizer_pow_ne_zero"
end PowerRule
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section LeibnizDecomp

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

private theorem _root_.AlgebraicCurve.Place.differentialCoeff_D_mul (a b : F) :
    v.differentialCoeff (KaehlerDifferential.D K F (a * b))
      = a * v.differentialCoeff (KaehlerDifferential.D K F b)
        + b * v.differentialCoeff (KaehlerDifferential.D K F a) := by
  have key := (KaehlerDifferential.D K F).leibniz a b
  rw [key, v.differentialCoeff_add', v.differentialCoeff_smul, v.differentialCoeff_smul]

p2m_export "AlgebraicCurve.Place" "differentialCoeff_D_mul"

theorem ord_differentialCoeff_D_of_unit_mul_uniformizer_pow {u : F} (hune : u ≠ 0)
    (hu : v.ord u = 0) {n : ℕ} (hn : (n : F) ≠ 0)
    (hreg : v.differentialCoeff (KaehlerDifferential.D K F u) = 0
        ∨ 0 ≤ v.ord (v.differentialCoeff (KaehlerDifferential.D K F u))) :
    v.differentialCoeff (KaehlerDifferential.D K F (u * v.uniformizer ^ n)) ≠ 0
    ∧ v.ord (v.differentialCoeff (KaehlerDifferential.D K F (u * v.uniformizer ^ n)))
        = (n : ℤ) - 1 := by
  set t₁ := u * v.differentialCoeff (KaehlerDifferential.D K F (v.uniformizer ^ n)) with ht₁
  set t₂ := v.uniformizer ^ n * v.differentialCoeff (KaehlerDifferential.D K F u) with ht₂
  have hdecomp :
      v.differentialCoeff (KaehlerDifferential.D K F (u * v.uniformizer ^ n)) = t₁ + t₂ :=
    v.differentialCoeff_D_mul u (v.uniformizer ^ n)

  have ht₁ne : t₁ ≠ 0 := mul_ne_zero hune (v.differentialCoeff_D_uniformizer_pow_ne_zero hn)
  have ht₁ord : v.ord t₁ = (n : ℤ) - 1 := by
    rw [ht₁, v.ord_mul hune (v.differentialCoeff_D_uniformizer_pow_ne_zero hn), hu,
      v.ord_differentialCoeff_D_uniformizer_pow hn, zero_add]

  rcases hreg with h0 | hge
  ·
    have ht₂0 : t₂ = 0 := by rw [ht₂, h0, mul_zero]
    rw [hdecomp, ht₂0, add_zero]
    exact ⟨ht₁ne, ht₁ord⟩
  ·
    rcases eq_or_ne (v.differentialCoeff (KaehlerDifferential.D K F u)) 0 with h0 | hne
    · have ht₂0 : t₂ = 0 := by rw [ht₂, h0, mul_zero]
      rw [hdecomp, ht₂0, add_zero]
      exact ⟨ht₁ne, ht₁ord⟩
    have ht₂ne : t₂ ≠ 0 := mul_ne_zero (pow_ne_zero _ v.uniformizer_ne_zero) hne
    have ht₂ord : (n : ℤ) ≤ v.ord t₂ := by
      rw [ht₂, v.ord_mul (pow_ne_zero _ v.uniformizer_ne_zero) hne,
        v.ord_pow', v.ord_uniformizer, mul_one]
      omega
    have hne12 : v.ord t₁ ≠ v.ord t₂ := by rw [ht₁ord]; omega
    have hsumne : t₁ + t₂ ≠ 0 := by
      intro h0
      have hneg : t₁ = -t₂ := eq_neg_of_add_eq_zero_left h0
      exact hne12 (by rw [hneg, v.ord_neg'])
    have hsum := v.ord_add_eq_min' ht₁ne ht₂ne hne12
    have hmin : min (v.ord t₁) (v.ord t₂) = (n : ℤ) - 1 := by
      rw [ht₁ord]; omega
    rw [hdecomp]
    exact ⟨hsumne, by rw [hsum, hmin]⟩

end LeibnizDecomp
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

section Discharge

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def LocalUnitDerivativeRegular : Prop :=
  ∀ (v : Place K F) (u : F), u ≠ 0 → v.ord u = 0 →
    v.differentialCoeff (KaehlerDifferential.D K F u) = 0
      ∨ 0 ≤ v.ord (v.differentialCoeff (KaehlerDifferential.D K F u))

variable {K F}
variable {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

theorem ord_differentialCoeff_D_of_ord_eq (w : Place K F') [w.DCoordGenerates]
    [Nontrivial Ω[F'⁄K]] (hreg : LocalUnitDerivativeRegular K F')
    {f : F'} (hf : f ≠ 0) {n : ℕ} (hn : (n : F') ≠ 0)
    (hord : w.ord f = (n : ℤ)) :
    w.differentialCoeff (KaehlerDifferential.D K F' f) ≠ 0
    ∧ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' f)) = (n : ℤ) - 1 := by
  obtain ⟨u, hune, hu0, huf⟩ := Place.exists_ord_eq_zero_mul_uniformizer_zpow w hf
  rw [hord] at huf
  have huf' : f = u * w.uniformizer ^ n := by
    rw [huf, zpow_natCast]
  rw [huf']
  exact Place.ord_differentialCoeff_D_of_unit_mul_uniformizer_pow w hune hu0 hn
    (hreg w u hune hu0)

theorem tameLocalDifferentExponent_of_localUnitDerivativeRegular
    [∀ w : Place K F', w.DCoordGenerates] [Nontrivial Ω[F'⁄K]]
    (hreg : LocalUnitDerivativeRegular K F')
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0) :
    TameLocalDifferentExponent K F F' := by
  intro w
  set e := w.ramificationIndex F
  have hf : algebraMap F F' (w.restrict F).uniformizer ≠ 0 := by
    have := (w.restrict F).uniformizer_ne_zero
    exact fun h => this ((algebraMap F F').injective (by simpa using h))
  have hord : w.ord (algebraMap F F' (w.restrict F).uniformizer) = (e : ℤ) := by
    rw [w.ord_restrict (F := F), (w.restrict F).ord_uniformizer, mul_one]
  exact ord_differentialCoeff_D_of_ord_eq w hreg hf (htame w) hord

omit [Algebra K F] [IsScalarTower K F F'] in

theorem ramificationIndex_cast_ne_zero_of_charZero [CharZero K] (w : Place K F') :
    ((w.ramificationIndex F : ℕ) : F') ≠ 0 := by
  have he1 : 0 < w.ramificationIndex F := w.ramificationIndex_pos (F := F)
  have hKne : ((w.ramificationIndex F : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr he1.ne'
  rw [← map_natCast (algebraMap K F')]
  exact fun h => hKne ((algebraMap K F').injective (by simpa using h))

theorem tameLocalDifferentExponent_of_localUnitDerivativeRegular_charZero [CharZero K]
    [∀ w : Place K F', w.DCoordGenerates] [Nontrivial Ω[F'⁄K]]
    (hreg : LocalUnitDerivativeRegular K F') :
    TameLocalDifferentExponent K F F' :=
  tameLocalDifferentExponent_of_localUnitDerivativeRegular hreg
    (ramificationIndex_cast_ne_zero_of_charZero (K := K) (F := F))

end Discharge
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section GatesPlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end GatesPlace
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Divisor Divisor.degree Divisor.degree_single Divisor.principal HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor Place.ord_restrict Place.mem_fiber Divisor.pullback Divisor.pullback_apply Divisor.isPrincipal_pullback FundamentalIdentity Divisor.degree_pullback SumRamificationInertia IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.finrank_kaehler IsCurveOver.kaehler_free_rank_one Place.dCoord Place.ordDifferential Place.uniformizer HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.sum_ramificationIndex_mul_inertiaDeg"
p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg"

section RHEngine

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']

theorem ord_differentialCoeff_D_algebraMap_uniformizer
    [∀ w : Place K F', w.DCoordGenerates] [Nontrivial Ω[F'⁄K]]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (w : Place K F') (hw : ((w.ramificationIndex F : ℕ) : F') ≠ 0) :
    w.differentialCoeff (KaehlerDifferential.D K F' (algebraMap F F' (w.restrict F).uniformizer)) ≠ 0 ∧
      w.ord (w.differentialCoeff
        (KaehlerDifferential.D K F' (algebraMap F F' (w.restrict F).uniformizer)))
          = (w.ramificationIndex F : ℤ) - 1 := by
  have hf : algebraMap F F' (w.restrict F).uniformizer ≠ 0 := by
    have := (w.restrict F).uniformizer_ne_zero
    exact fun h => this ((algebraMap F F').injective (by simpa using h))
  have hord : w.ord (algebraMap F F' (w.restrict F).uniformizer) = ((w.ramificationIndex F : ℕ) : ℤ) := by
    rw [w.ord_restrict (F := F), (w.restrict F).ord_uniformizer, mul_one]
  exact ord_differentialCoeff_D_of_ord_eq w hreg hf hw hord

theorem tameLocalDifferentExponent_of_hreg
    [∀ w : Place K F', w.DCoordGenerates] [Nontrivial Ω[F'⁄K]]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0) :
    TameLocalDifferentExponent K F F' :=
  tameLocalDifferentExponent_of_localUnitDerivativeRegular hreg htame

variable [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates]
  [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]

omit [Algebra.IsIntegral F F'] in
private theorem nontrivial_kaehler_of_isCurveOver' : Nontrivial Ω[F'⁄K] :=
  Module.nontrivial_of_finrank_eq_succ (IsCurveOver.kaehler_free_rank_one (K := K) (F := F')).2

theorem ordDifferential_map_eq
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (w : Place K F') :
    w.ordDifferential (KaehlerDifferential.map K K F F' ω₀)
      = (w.ramificationIndex F : ℤ) * (w.restrict F).ordDifferential ω₀
          + ((w.ramificationIndex F : ℤ) - 1) := by
  haveI : Nontrivial Ω[F'⁄K] := nontrivial_kaehler_of_isCurveOver' (K := K) (F' := F')
  exact ordDifferential_kaehlerMap_universal (tameLocalDifferentExponent_of_hreg hreg htame) hω₀ w

theorem map_ne_zero_of_tame_port
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    (w₀ : Place K F') {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    KaehlerDifferential.map K K F F' ω₀ ≠ 0 := by
  haveI : Nontrivial Ω[F'⁄K] := nontrivial_kaehler_of_isCurveOver' (K := K) (F' := F')
  exact kaehlerMap_ne_zero_of_tameLocalDifferent (tameLocalDifferentExponent_of_hreg hreg htame) w₀ hω₀

theorem exists_finset_unramified_off
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (hω₀' : KaehlerDifferential.map K K F F' ω₀ ≠ 0) :
    ∃ S : Finset (Place K F'), ∀ w : Place K F', w ∉ S → w.ramificationIndex F = 1 := by
  classical
  haveI : HasPrincipalDivisors K F' := IsCurveOver.hasPrincipalDivisors

  let T : Finset (Place K F') := (canonicalDivisorOf (K := K) hω₀').support ∪
    (canonicalDivisorOf (K := K) hω₀).support.biUnion (fun v => v.fiber F')
  refine ⟨T, fun w hw => ?_⟩
  have hwT1 : w ∉ (canonicalDivisorOf (K := K) hω₀').support := fun h => hw (Finset.mem_union_left _ h)
  have hwT2 : (w.restrict F) ∉ (canonicalDivisorOf (K := K) hω₀).support := by
    intro h
    apply hw
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w.restrict F, h, ?_⟩)
    exact Place.mem_fiber.mpr rfl
  have h1 : w.ordDifferential (KaehlerDifferential.map K K F F' ω₀) = 0 := by
    have := Finsupp.notMem_support_iff.mp hwT1
    rwa [canonicalDivisorOf_apply] at this
  have h2 : (w.restrict F).ordDifferential ω₀ = 0 := by
    have := Finsupp.notMem_support_iff.mp hwT2
    rwa [canonicalDivisorOf_apply] at this
  have h3 := ordDifferential_map_eq hreg htame hω₀ w
  rw [h1, h2, mul_zero, zero_add] at h3
  have he : (w.ramificationIndex F : ℤ) = 1 := by linarith
  exact_mod_cast he

theorem canonicalDivisorOf_map_eq
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (hω₀' : KaehlerDifferential.map K K F F' ω₀ ≠ 0)
    {S : Finset (Place K F')} (hS : ∀ w : Place K F', w ∉ S → w.ramificationIndex F = 1) :
    canonicalDivisorOf (K := K) hω₀'
      = Divisor.pullback F' (canonicalDivisorOf (K := K) hω₀) + tameDifferentDivisor K F S := by
  haveI : Nontrivial Ω[F'⁄K] := nontrivial_kaehler_of_isCurveOver' (K := K) (F' := F')
  exact canonicalDivisorOf_eq_of_localHurwitzExponent hω₀ hω₀'
    (localHurwitzExponent_kaehlerMap_of_tameLocalDifferent
      (tameLocalDifferentExponent_of_hreg hreg htame) hω₀ hS)

theorem degree_canonicalDivisorOf_map
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (hω₀' : KaehlerDifferential.map K K F F' ω₀ ≠ 0) :
    Divisor.degree (canonicalDivisorOf (K := K) hω₀')
      = (Module.finrank F F' : ℤ) * Divisor.degree (canonicalDivisorOf (K := K) hω₀)
        + ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) := by
  classical
  haveI : HasPrincipalDivisors K F' := IsCurveOver.hasPrincipalDivisors
  obtain ⟨S, hS⟩ := exists_finset_unramified_off hreg htame hω₀ hω₀'
  have hdiv := canonicalDivisorOf_map_eq hreg htame hω₀ hω₀' hS
  have hfin : ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ)
      = ∑ w ∈ S, ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    rw [Function.mem_support] at hw
    by_contra hwS
    exact hw (by rw [hS w hwS]; simp)
  rw [hdiv, map_add, Divisor.degree_pullback, degree_tameDifferentDivisor, hfin]

theorem two_mul_genus_sub_two_eq_of_degree_canonical
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (hω₀' : KaehlerDifferential.map K K F F' ω₀ ≠ 0)
    (hK : Divisor.degree (canonicalDivisorOf (K := K) hω₀) = 2 * (genus K F : ℤ) - 2)
    (hK' : Divisor.degree (canonicalDivisorOf (K := K) hω₀') = 2 * (genus K F' : ℤ) - 2) :
    2 * (genus K F' : ℤ) - 2
      = (Module.finrank F F' : ℤ) * (2 * (genus K F : ℤ) - 2)
        + ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) := by
  rw [← hK, ← hK']
  exact degree_canonicalDivisorOf_map hreg htame hω₀ hω₀'

end RHEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve"

p2m_open "AlgebraicCurve~Place.ord_nonneg_of_mem~Place.mem_of_ord_nonneg~Place.mem_iff_ord_nonneg" in open _root_.P2MW.S_AlgebraicCurve_map_ne_zero_of_tame.AlgebraicCurve in
theorem solution {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    (w₀ : Place K F') {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    KaehlerDifferential.map K K F F' ω₀ ≠ 0 :=
  AlgebraicCurve.map_ne_zero_of_tame_port (K := K) (F := F) (F' := F') (hreg := hreg) (htame := htame) (w₀ := w₀) (ω₀ := ω₀) (hω₀ := hω₀)

end S_AlgebraicCurve_map_ne_zero_of_tame
end P2MW
export P2MW.S_AlgebraicCurve_map_ne_zero_of_tame (solution)
