-- Prove2me | Definitions.Def_AlgebraicCurve_SerrePairing
-- name    : AlgebraicCurve_SerrePairing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/d8888ae0-38a4-54bc-89b8-c9522ec211df
-- title:
--   Serre duality pairing on a two-chart Čech H¹ of a curve
-- statement:
--   Throughout, $F$ is a field extension of a field $K$, with places $v$ of $F/K$ given by the project's structure `Place K F` (a proper valuation subring of $F$ containing the image of $K$ whose ideals are principal, hence a discrete valuation ring, with normalised valuation `Place.ord`), and with a chosen local residue datum (`HasCanonicalLocalResidueKStar K F`) providing the $K$-valued local term `kaehlerResidueTerm ω α v`; this term depends on $\omega$ only through the coefficient `v.differentialCoeff ω`, the unique $c$ with $\omega = c\,\cdot\,d\pi_v$ once `v.DCoordGenerates` holds, and vanishes as soon as the product $\alpha_v\cdot c$ is zero or has non-negative order at $v$.
--
--   For a set of places $S_0$, `residueSumOffChart S₀ ω f` is the unrestricted sum $\sum^{f}_{v}$ of the local terms of $\omega$ against the répartition `extendOffChart K S₀ f`, which is $0$ at places of $S_0$ and equal to $f$ elsewhere; thus it is the sum of the local residue terms of $f\omega$ over the places off $S_0$. Its support is finite, and it is $K$-bilinear in $(\omega,f)$; `residueSumOffChartLinear S₀ ω` packages the $f$-linearity.
--
--   The main definition, `serrePairing`, takes a proof `hRT` of the predicate `ResidueTheorem K F` (vanishing of the Weil functional `weilOfKaehler` on diagonal répartitions) and a covering condition $S_0\cup S_1 = \text{univ}$, and produces a $K$-linear map from the submodule `regularDifferentials K F` of differentials that are $\mathcal O_v$-multiples of $d\pi_v$ at every place, into the dual of $\check H^1$ for the two-chart cover with $D=0$, namely $L_{S_0\cap S_1}(0)$ modulo the image of $(f_0,f_1)\mapsto f_1-f_0$. On a class represented by $f$ the value is `residueSumOffChart S₀ ω f`. Factorisation through the quotient rests on two vanishing statements also proved here: for $f\in L_{S_1}(0)$ every off-$S_0$ term vanishes by regularity, and for $f\in L_{S_0}(0)$ the off-chart sum equals the full residue sum, which is zero by `hRT`. A closed formula with the $S_0$-terms replaced by $0$ is recorded as well.
--
--   **Relation to Mathlib.** Mathlib supplies the module of Kähler differentials $\Omega[F⁄K]$ and adic valuations of Dedekind domains; the places, $L$-spaces on a set of places, the two-chart Čech complex, répartitions and the residue pairing defined here are the project's own notions.
--
--   **Where it is used.** These definitions supply the duality side of the curve theory used for modular curves: a pairing between regular differentials and the first Čech cohomology of the structure sheaf for a two-chart cover, compatible with the adelic Weil-differential description of $H^1$. Perfectness of this pairing and its behaviour under finite morphisms are what make the cohomological computations on modular curves available to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_SerrePairing.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem ord_nonneg_of_mem_toValuationSubring {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [v.ord_zero]
  · have hle : v.adicValuation f ≤ 1 := by
      rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    have hlog : WithZero.log (v.adicValuation f) ≤ 0 := by
      rw [← WithZero.exp_zero] at hle
      exact (WithZero.log_le_iff_le_exp (v.adicValuation_ne_zero hf0)).mpr hle
    unfold Place.ord
    omega

theorem mul_eq_zero_or_ord_nonneg {f g : F} (hf : f = 0 ∨ 0 ≤ v.ord f) (hg : 0 ≤ v.ord g) :
    f * g = 0 ∨ 0 ≤ v.ord (f * g) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Or.inl (zero_mul _)
  rcases eq_or_ne g 0 with rfl | hg0
  · exact Or.inl (mul_zero _)
  refine Or.inr ?_
  rw [v.ord_mul hf0 hg0]
  have := hf.resolve_left hf0
  omega

variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem differentialCoeff_add (ω η : Ω[F⁄K]) :
    v.differentialCoeff (ω + η) = v.differentialCoeff ω + v.differentialCoeff η :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_smul_algebraMap (c : K) (ω : Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = algebraMap K F c * v.differentialCoeff ω := by
  rw [← v.differentialCoeff_smul, algebraMap_smul]

theorem ord_differentialCoeff_nonneg_of_mem_regularDifferentials {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) : 0 ≤ v.ord (v.differentialCoeff ω) := by
  obtain ⟨g, hg, hωg⟩ := hω v
  rw [v.differentialCoeff_unique hωg]
  exact v.ord_nonneg_of_mem_toValuationSubring hg

end Place

theorem eq_zero_or_ord_nonneg_of_mem_lSpaceOn_zero {S : Set (Place K F)} {f : F}
    (hf : f ∈ lSpaceOn S (0 : Divisor K F)) {v : Place K F} (hv : v ∈ S) :
    f = 0 ∨ 0 ≤ v.ord f := by
  have h := (mem_lSpaceOn_iff_ord.mp hf) v hv
  rwa [Finsupp.coe_zero, Pi.zero_apply, neg_zero] at h

theorem coe_extendOffChart_mem_adeleSpace [HasPrincipalDivisors K F] (S₀ : Set (Place K F)) (f : F) :
    ((extendOffChart K S₀ f : ↥(repartitions K F)) : Place K F → F) ∈ adeleSpace K F := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp (diagonal_mem_adeleSpace (K := K) f)
  refine mem_adeleSpace_iff.mpr ⟨D, fun v => ?_⟩
  by_cases hv : v ∈ S₀
  · rw [coe_extendOffChart_apply_of_mem f hv, Valuation.map_zero]
    exact zero_le'
  · rw [coe_extendOffChart_apply_of_not_mem f hv]
    exact hD v

variable [HasCanonicalLocalResidueKStar K F]

theorem kaehlerResidueTerm_add_right (ω : Ω[F⁄K]) (α β : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm ω (α + β) v = kaehlerResidueTerm ω α v + kaehlerResidueTerm ω β v := by
  unfold kaehlerResidueTerm
  rw [Pi.add_apply, add_mul, map_add, map_add]

theorem kaehlerResidueTerm_smul_right (ω : Ω[F⁄K]) (c : K) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm ω (c • α) v = c * kaehlerResidueTerm ω α v := by
  unfold kaehlerResidueTerm
  rw [Pi.smul_apply, Algebra.smul_def, mul_assoc, ← Algebra.smul_def, map_smul, map_smul,
    smul_eq_mul]

theorem kaehlerResidueTerm_eq_zero_of_apply_eq_zero (ω : Ω[F⁄K]) {α : Place K F → F}
    {v : Place K F} (h : α v = 0) : kaehlerResidueTerm ω α v = 0 :=
  kaehlerResidueTerm_eq_zero_of_ord_nonneg (Or.inl (by rw [h, zero_mul]))

def residueSumOffChart (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) (f : F) : K :=
  ∑ᶠ v, kaehlerResidueTerm ω ((extendOffChart K S₀ f : ↥(repartitions K F)) : Place K F → F) v

theorem residueSumOffChart_def (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) (f : F) :
    residueSumOffChart S₀ ω f
      = ∑ᶠ v, kaehlerResidueTerm ω ((extendOffChart K S₀ f : ↥(repartitions K F)) : Place K F → F) v :=
  rfl

open Classical in

theorem kaehlerResidueTerm_extendOffChart (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) (f : F) (v : Place K F) :
    kaehlerResidueTerm ω ((extendOffChart K S₀ f : ↥(repartitions K F)) : Place K F → F) v
      = if v ∈ S₀ then 0 else kaehlerResidueTerm ω (diagonalHom K F f) v := by
  classical
  split_ifs with hv
  · exact kaehlerResidueTerm_eq_zero_of_apply_eq_zero ω (coe_extendOffChart_apply_of_mem f hv)
  · unfold kaehlerResidueTerm
    rw [coe_extendOffChart_apply_of_not_mem f hv, diagonalHom_apply]

variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem kaehlerResidueTerm_add_left (ω η : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (ω + η) α v = kaehlerResidueTerm ω α v + kaehlerResidueTerm η α v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_add, mul_add, map_add, map_add]

theorem kaehlerResidueTerm_smul_left (c : K) (ω : Ω[F⁄K]) (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (c • ω) α v = c * kaehlerResidueTerm ω α v := by
  unfold kaehlerResidueTerm
  rw [v.differentialCoeff_smul_algebraMap, mul_left_comm, ← Algebra.smul_def, map_smul, map_smul,
    smul_eq_mul]

theorem kaehlerResidueTerm_zero_left (α : Place K F → F) (v : Place K F) :
    kaehlerResidueTerm (0 : Ω[F⁄K]) α v = 0 :=
  kaehlerResidueTerm_eq_zero_of_ord_nonneg (Or.inl (by rw [v.differentialCoeff_zero, mul_zero]))

theorem kaehlerResidueTerm_eq_zero_of_regular {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F)
    {α : Place K F → F} {v : Place K F} (hα : α v = 0 ∨ 0 ≤ v.ord (α v)) :
    kaehlerResidueTerm ω α v = 0 :=
  kaehlerResidueTerm_eq_zero_of_ord_nonneg
    (v.mul_eq_zero_or_ord_nonneg hα (v.ord_differentialCoeff_nonneg_of_mem_regularDifferentials hω))

theorem residueSumOffChart_eq_zero_of_mem_lSpaceOn_right {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) {f : F}
    (hf : f ∈ lSpaceOn S₁ (0 : Divisor K F)) : residueSumOffChart S₀ ω f = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
  rw [kaehlerResidueTerm_extendOffChart]
  split_ifs with hv
  · rfl
  · have hv₁ : v ∈ S₁ := by
      have h : v ∈ S₀ ∪ S₁ := hcover ▸ Set.mem_univ v
      exact h.resolve_left hv
    exact kaehlerResidueTerm_eq_zero_of_regular hω (eq_zero_or_ord_nonneg_of_mem_lSpaceOn_zero hf hv₁)

theorem residueSumOffChart_eq_finsum_of_mem_lSpaceOn_left {S₀ : Set (Place K F)} {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) {f : F} (hf : f ∈ lSpaceOn S₀ (0 : Divisor K F)) :
    residueSumOffChart S₀ ω f = ∑ᶠ v, kaehlerResidueTerm ω (diagonalHom K F f) v := by
  refine finsum_congr fun v => ?_
  rw [kaehlerResidueTerm_extendOffChart]
  split_ifs with hv
  · exact (kaehlerResidueTerm_eq_zero_of_regular hω (eq_zero_or_ord_nonneg_of_mem_lSpaceOn_zero hf hv)).symm
  · rfl

variable [HasCanonicalDivisor (K := K) (F := F)] [HasPrincipalDivisors K F]

theorem residueSumOffChart_support_finite (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) (f : F) :
    (Function.support fun v =>
      kaehlerResidueTerm ω ((extendOffChart K S₀ f : ↥(repartitions K F)) : Place K F → F) v).Finite := by
  rcases eq_or_ne ω 0 with rfl | hω
  · refine Set.Finite.subset Set.finite_empty fun v hv => ?_
    exact hv (kaehlerResidueTerm_zero_left _ v)
  · exact kaehlerResidueTerm_support_finite_of_adeleSpace hω (coe_extendOffChart_mem_adeleSpace S₀ f)

theorem residueSumOffChart_add_right (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) (f g : F) :
    residueSumOffChart S₀ ω (f + g) = residueSumOffChart S₀ ω f + residueSumOffChart S₀ ω g := by
  unfold residueSumOffChart
  rw [← finsum_add_distrib (residueSumOffChart_support_finite S₀ ω f)
    (residueSumOffChart_support_finite S₀ ω g)]
  refine finsum_congr fun v => ?_
  rw [map_add, Subalgebra.coe_add, kaehlerResidueTerm_add_right]

theorem residueSumOffChart_smul_right (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) (c : K) (f : F) :
    residueSumOffChart S₀ ω (c • f) = c * residueSumOffChart S₀ ω f := by
  unfold residueSumOffChart
  rw [mul_finsum' _ _ (residueSumOffChart_support_finite S₀ ω f)]
  refine finsum_congr fun v => ?_
  rw [map_smul, Subalgebra.coe_smul, kaehlerResidueTerm_smul_right]

theorem residueSumOffChart_add_left (S₀ : Set (Place K F)) (ω η : Ω[F⁄K]) (f : F) :
    residueSumOffChart S₀ (ω + η) f = residueSumOffChart S₀ ω f + residueSumOffChart S₀ η f := by
  unfold residueSumOffChart
  rw [← finsum_add_distrib (residueSumOffChart_support_finite S₀ ω f)
    (residueSumOffChart_support_finite S₀ η f)]
  exact finsum_congr fun v => kaehlerResidueTerm_add_left ω η _ v

theorem residueSumOffChart_smul_left (S₀ : Set (Place K F)) (c : K) (ω : Ω[F⁄K]) (f : F) :
    residueSumOffChart S₀ (c • ω) f = c * residueSumOffChart S₀ ω f := by
  unfold residueSumOffChart
  rw [mul_finsum' _ _ (residueSumOffChart_support_finite S₀ ω f)]
  exact finsum_congr fun v => kaehlerResidueTerm_smul_left c ω _ v

def residueSumOffChartLinear (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) : F →ₗ[K] K where
  toFun := residueSumOffChart S₀ ω
  map_add' := residueSumOffChart_add_right S₀ ω
  map_smul' c f := by rw [RingHom.id_apply, smul_eq_mul, residueSumOffChart_smul_right]

@[simp] theorem residueSumOffChartLinear_apply (S₀ : Set (Place K F)) (ω : Ω[F⁄K]) (f : F) :
    residueSumOffChartLinear S₀ ω f = residueSumOffChart S₀ ω f := rfl

theorem residueSumOffChart_eq_zero_of_mem_lSpaceOn_left (hRT : ResidueTheorem K F)
    {S₀ : Set (Place K F)} {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) {f : F}
    (hf : f ∈ lSpaceOn S₀ (0 : Divisor K F)) : residueSumOffChart S₀ ω f = 0 := by
  rw [residueSumOffChart_eq_finsum_of_mem_lSpaceOn_left hω hf]
  rcases eq_or_ne ω 0 with rfl | hω0
  · exact finsum_eq_zero_of_forall_eq_zero fun v => kaehlerResidueTerm_zero_left _ v
  · have h := hRT hω0 f
    rwa [weilOfKaehler_apply] at h

theorem range_cechDiff_le_ker_residueSumOffChart (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) {ω : Ω[F⁄K]}
    (hω : ω ∈ regularDifferentials K F) :
    LinearMap.range (cechDiff S₀ S₁ (0 : Divisor K F))
      ≤ LinearMap.ker ((residueSumOffChartLinear S₀ ω).comp (lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)).subtype) := by
  rintro g ⟨p, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, coe_cechDiff_apply,
    residueSumOffChartLinear_apply, sub_eq_add_neg, residueSumOffChart_add_right,
    ← neg_one_smul K (p.1 : F), residueSumOffChart_smul_right,
    residueSumOffChart_eq_zero_of_mem_lSpaceOn_right hcover hω p.2.2,
    residueSumOffChart_eq_zero_of_mem_lSpaceOn_left hRT hω p.1.2, mul_zero, add_zero]

def serrePairing (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) :
    ↥(regularDifferentials K F) →ₗ[K] cechH1 S₀ S₁ (0 : Divisor K F) →ₗ[K] K where
  toFun ω := (LinearMap.range (cechDiff S₀ S₁ (0 : Divisor K F))).liftQ
      ((residueSumOffChartLinear S₀ (ω : Ω[F⁄K])).comp (lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)).subtype)
      (range_cechDiff_le_ker_residueSumOffChart hRT hcover ω.2)
  map_add' ω η := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
    change residueSumOffChart S₀ ((ω : Ω[F⁄K]) + η) (f : F)
      = residueSumOffChart S₀ ω f + residueSumOffChart S₀ η f
    exact residueSumOffChart_add_left S₀ ω η f
  map_smul' c ω := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
    change residueSumOffChart S₀ (c • (ω : Ω[F⁄K])) (f : F) = c • residueSumOffChart S₀ ω f
    rw [smul_eq_mul]
    exact residueSumOffChart_smul_left S₀ c ω f

@[simp] theorem serrePairing_apply_mk (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (ω : ↥(regularDifferentials K F))
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) :
    serrePairing hRT hcover ω (Submodule.Quotient.mk f) = residueSumOffChart S₀ (ω : Ω[F⁄K]) (f : F) :=
  rfl

open Classical in
theorem serrePairing_apply_mk_eq_finsum_ite (hRT : ResidueTheorem K F) {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (ω : ↥(regularDifferentials K F))
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) :
    serrePairing hRT hcover ω (Submodule.Quotient.mk f)
      = ∑ᶠ v, if v ∈ S₀ then 0 else kaehlerResidueTerm (ω : Ω[F⁄K]) (diagonalHom K F (f : F)) v := by
  rw [serrePairing_apply_mk, residueSumOffChart_def]
  exact finsum_congr fun v => kaehlerResidueTerm_extendOffChart S₀ _ _ v

end AlgebraicCurve

end


