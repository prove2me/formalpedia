-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ad0e48f7-c43b-5b42-ab8b-892f00b05bcc

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.GroupTheory.Abelianization.Defs
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring
import Theorems.Thm_CerednikDrinfeld_Mumford_existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer
import Theorems.Thm_AlgebraicCurve_Pic0_isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one
import Theorems.Thm_AlgebraicCurve_Pic0_exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_isTree
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_ValuationSubring_isAlgClosed_completion_of_liesOverPrime
import Theorems.Thm_CerednikDrinfeld_Omega_exists_adj_min_le_v_apply_le_max_of_isUnit
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_BruhatTits_finite_stabilizer_vertex_of_finite_stabilizer_dart
import Mathlib.GroupTheory.OrderOfElement
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val CerednikDrinfeld.Omega.coordSub_apply CerednikDrinfeld.Omega.coord_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve ModularCurve

noncomputable section

namespace ECOmega
namespace S2P

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_algebraMap_units_eq_one
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : algebraMap K₀ K (algebraMap R K₀ (u : R)) * algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : Γ₀) = Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R))) := by rw [← Valuation.map_mul, h1, Valuation.map_one]
    _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) * 1 := mul_le_mul_right (hint _) _
    _ = _ := mul_one _

theorem algebraMap_ne_zero_of_irreducible (hϖ : Irreducible ϖ) : algebraMap R K₀ ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

theorem v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
    rw [map_inv₀, Valuation.map_inv, inv_le_one₀ (v_algebraMap_pos hϖ)]
    exact h
  obtain ⟨b, hb⟩ := hv _ hle
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hb, map_one, mul_inv_cancel₀ hϖ0]

theorem exists_v_algebraMap_eq_zpow (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨k, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀,
    v_algebraMap_units_eq_one hint, one_mul]

theorem v_algebraMap_le_or_one_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, Valuation.map_zero]; exact zero_le'
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  rw [hk]
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  rcases le_or_gt k 0 with hk0 | hk0
  · exact Or.inr (one_le_zpow_of_nonpos₀ h0 h1 hk0)
  · left
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 h1 (by omega)
      _ = _ := zpow_one _

theorem exists_pow_le_v_algebraMap_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) (ha : a ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))⁻¹ ^ N := by
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  refine ⟨k.natAbs, ?_, ?_⟩
  · rw [hk, ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (Int.le_natAbs)
  · rw [hk, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (by rw [Int.natCast_natAbs]; exact neg_abs_le k)

def treePseudoUniformizer (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    PseudoUniformizer K₀ K where
  ϖ := algebraMap R K₀ ϖ
  pos := v_algebraMap_pos hϖ
  lt_one := v_algebraMap_lt_one hϖ hv
  scale := exists_pow_le_v_algebraMap_le hϖ hint hv

@[scoped simp] theorem treePseudoUniformizer_ϖ (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    (treePseudoUniformizer hϖ hint hv).ϖ = algebraMap R K₀ ϖ := rfl

end PUTree

section Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem mem_affinoid_of_v_sub_lt (ϖ : Omega.PseudoUniformizer K₀ K) {n : ℕ} {z w : K} (hz : z ∈ Omega.affinoid ϖ n)
    (hw : Valued.v (w - z) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n) : w ∈ Omega.affinoid ϖ n := by
  have hrr : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
    (pow_le_one₀ ϖ.pos.le ϖ.lt_one.le).trans (one_le_pow₀ ((one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le))
  rw [Omega.mem_affinoid_iff'] at hz ⊢
  refine ⟨?_, fun x => ?_⟩
  · have : w = z + (w - z) := by ring
    rw [this]
    exact Valuation.map_add_le _ hz.1 (hw.le.trans hrr)
  · have h1 : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K x) := hw.trans_le (hz.2 x)
    have : w - algebraMap K₀ K x = (z - algebraMap K₀ K x) + (w - z) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ h1]
    exact hz.2 x

theorem exists_mem_upperHalfPlane_forall_pmoebius_ne (ϖ : Omega.PseudoUniformizer K₀ K) (hex : Omega.IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hdisc : Omega.IsDiscrete K ρ)
    {x x' : K} (hx : x ∈ Omega.upperHalfPlane K₀ K) (hx' : x' ∈ Omega.upperHalfPlane K₀ K) :
    ∃ z₁ : K, z₁ ∈ Omega.upperHalfPlane K₀ K ∧ (∀ γ : G, Omega.pmoebius K₀ (ρ γ) x ≠ z₁) ∧
      (∀ γ : G, Omega.pmoebius K₀ (ρ γ) x' ≠ z₁) := by
  classical
  obtain ⟨n, hn⟩ := hex x hx
  obtain ⟨n', hn'⟩ := hex x' hx'
  set N := max n n' with hN
  have hxN : x ∈ Omega.affinoid ϖ N := Omega.affinoid_mono ϖ (le_max_left n n') hn
  have hx'N : x' ∈ Omega.affinoid ϖ N := Omega.affinoid_mono ϖ (le_max_right n n') hn'

  set z : ℕ → K := fun k => x + algebraMap K₀ K ϖ.ϖ ^ (k + N + 1) with hz
  have hzN : ∀ k, z k ∈ Omega.affinoid ϖ N := fun k => by
    refine mem_affinoid_of_v_sub_lt ϖ hxN ?_
    rw [hz]; dsimp only
    rw [add_sub_cancel_left, Valuation.map_pow]
    exact pow_lt_pow_right_of_lt_one₀ ϖ.pos ϖ.lt_one (by omega)
  have hzinj : Function.Injective z := by
    intro k k' h
    rw [hz] at h
    have h' : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (k + N + 1) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (k' + N + 1) := by
      rw [← Valuation.map_pow, ← Valuation.map_pow]; exact congrArg _ (add_left_cancel h)
    have := pow_right_injective₀ ϖ.pos ϖ.lt_one.ne h'
    omega

  have hfin : {γ : G | Omega.pmoebius K₀ (ρ γ) x ∈ Omega.affinoid ϖ N}.Finite :=
    CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ ρ hdisc N hxN
  have hfin' : {γ : G | Omega.pmoebius K₀ (ρ γ) x' ∈ Omega.affinoid ϖ N}.Finite :=
    CerednikDrinfeld.Omega.finite_setOf_pmoebius_mem_affinoid ϖ ρ hdisc N hx'N
  have hbad : {k : ℕ | ∃ γ : G, Omega.pmoebius K₀ (ρ γ) x = z k ∨ Omega.pmoebius K₀ (ρ γ) x' = z k}.Finite := by
    refine Set.Finite.subset ((((hfin.image fun γ => Omega.pmoebius K₀ (ρ γ) x).union
      (hfin'.image fun γ => Omega.pmoebius K₀ (ρ γ) x')).preimage (hzinj.injOn))) ?_
    rintro k ⟨γ, h | h⟩
    · exact Or.inl ⟨γ, by rw [Set.mem_setOf_eq, h]; exact hzN k, h⟩
    · exact Or.inr ⟨γ, by rw [Set.mem_setOf_eq, h]; exact hzN k, h⟩
  obtain ⟨k, -, hk⟩ := Set.Infinite.exists_notMem_finite (Set.infinite_univ (α := ℕ)) hbad
  simp only [Set.mem_setOf_eq, not_exists, not_or] at hk
  exact ⟨z k, Omega.affinoid_subset_upperHalfPlane ϖ N (hzN k), fun γ => (hk γ).1, fun γ => (hk γ).2⟩

end Omega

theorem exists_mem_affinoid_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) [Finite (R ⧸ Ideal.span {ϖ₀})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ₀)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ : Omega.PseudoUniformizer K₀ K) (hϖ : algebraMap R K₀ ϖ₀ = ϖ.ϖ) (hex : Omega.IsExhausted ϖ) :
    ∃ w : K, w ∈ Omega.affinoid ϖ 0 := by

  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K₀ K ϖ.ϖ) (show 0 < 2 by norm_num)
  have h2 : Valued.v y ^ 2 = Valued.v (algebraMap K₀ K ϖ.ϖ) := by rw [← Valuation.map_pow, hy]
  have hy0 : 0 < Valued.v y := by
    rw [Valuation.pos_iff]; rintro rfl
    rw [zero_pow two_ne_zero] at hy; exact ϖ.pos.ne' (by rw [← hy, Valuation.map_zero])
  have hy1 : Valued.v y < 1 := by
    by_contra h; rw [not_lt] at h
    have h' : 1 ≤ Valued.v y ^ 2 := one_le_pow₀ h
    rw [h2] at h'
    exact absurd ϖ.lt_one (not_lt.2 h')
  have hyr : Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v y := by
    rw [← h2, pow_two]
    calc Valued.v y * Valued.v y < Valued.v y * 1 := mul_lt_mul_of_pos_left hy1 hy0
      _ = Valued.v y := mul_one _
  have hyΩ : y ∈ Omega.upperHalfPlane K₀ K := by
    rw [Omega.mem_upperHalfPlane_iff]
    rintro a rfl
    rcases v_algebraMap_le_or_one_le hϖ₀ hint hv a with h | h
    · rw [hϖ] at h; exact absurd hyr (not_lt.2 h)
    · exact absurd hy1 (not_lt.2 h)
  obtain ⟨-, -, w, -, -, -, hw, -⟩ :=
    CerednikDrinfeld.Omega.exists_adj_min_le_v_apply_le_max_of_isUnit R K₀ ϖ₀ hϖ₀ K hint hv hq ϖ hrk hex 1 isUnit_one ⟨y, hyΩ⟩
  exact ⟨w, hw⟩

end ECOmega.S2P
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega.S2P"
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega"

namespace ECOmega
namespace S2

section Bookkeeping

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem mk_eq_mk_iff (D₁ D₂ : ↥(Divisor.degZero (K := K) (F := F))) :
    Pic0.mk D₁ = Pic0.mk D₂ ↔ Divisor.IsPrincipal ((D₁ : Divisor K F) - (D₂ : Divisor K F)) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub,
    Divisor.mem_principal]

theorem mk_eq_zero_iff (D₁ : ↥(Divisor.degZero (K := K) (F := F))) :
    Pic0.mk D₁ = 0 ↔ Divisor.IsPrincipal (D₁ : Divisor K F) := by
  rw [← Pic0.mk_zero, mk_eq_mk_iff]
  simp

theorem isPrincipal_zero : Divisor.IsPrincipal (0 : Divisor K F) :=
  ⟨1, one_ne_zero, fun v => by simp⟩

theorem single_sub_single_mem_degZero (hdeg : ∀ v : Place K F, v.deg = 1) (P Q : Place K F) :
    Finsupp.single P 1 - Finsupp.single Q 1 ∈ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]
  simp

theorem sum_single_sub_single_mem_degZero (hdeg : ∀ v : Place K F, v.deg = 1) {n : ℕ}
    (P Q : Fin n → Place K F) :
    (∑ i, (Finsupp.single (P i) 1 - Finsupp.single (Q i) 1) : Divisor K F) ∈ Divisor.degZero (K := K) (F := F) :=
  sum_mem fun i _ => single_sub_single_mem_degZero hdeg (P i) (Q i)

theorem eq_sum_smul_single_sub_single (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F)
    (hD : Divisor.degree D = 0) (Q₀ : Place K F) :
    D = ∑ v ∈ D.support, D v • (Finsupp.single v 1 - Finsupp.single Q₀ 1) := by
  have hdeg' : Divisor.degree D = ∑ v ∈ D.support, D v := by
    unfold Divisor.degree
    rw [Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [hdeg]
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [← hdeg', hD, zero_smul, sub_zero]
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem eq_top_of_forall_mk_single_sub_single_mem (hdeg : ∀ v : Place K F, v.deg = 1)
    (Sg : AddSubgroup (Pic0 K F))
    (hS : ∀ P Q : Place K F,
      Pic0.mk ⟨Finsupp.single P 1 - Finsupp.single Q 1, single_sub_single_mem_degZero hdeg P Q⟩ ∈ Sg) :
    Sg = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨Q₀⟩⟩
  · have h0 : D = 0 := Subtype.ext (Finsupp.ext fun v => hE.elim v)
    rw [h0, Pic0.mk_zero]
    exact Sg.zero_mem
  have hmk : ∀ y : ↥(Divisor.degZero (K := K) (F := F)), Pic0.mk y =
      QuotientAddGroup.mk' ((Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))) y :=
    fun y => rfl
  have hdec : D = ∑ v ∈ (D : Divisor K F).support,
      (D : Divisor K F) v • (⟨Finsupp.single v 1 - Finsupp.single Q₀ 1, single_sub_single_mem_degZero hdeg v Q₀⟩ :
        ↥(Divisor.degZero (K := K) (F := F))) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [AddSubgroupClass.coe_zsmul]
    exact eq_sum_smul_single_sub_single hdeg D (Divisor.mem_degZero.mp D.2) Q₀
  rw [hmk, hdec, map_sum]
  refine sum_mem fun v _ => ?_
  rw [map_zsmul]
  exact Sg.zsmul_mem (by rw [← hmk]; exact hS v Q₀) _

end Bookkeeping
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega.S2P"

section FinAppend

theorem sum_fin_add_eq {M : Type} [AddCommMonoid M] {n m : ℕ} (f : Fin (n + m) → M) (f₁ : Fin n → M) (f₂ : Fin m → M)
    (h₁ : ∀ i, f (Fin.castAdd m i) = f₁ i) (h₂ : ∀ j, f (Fin.natAdd n j) = f₂ j) :
    ∑ i, f i = ∑ i, f₁ i + ∑ j, f₂ j := by
  rw [Fin.sum_univ_add]; simp only [h₁, h₂]

theorem prod_fin_add_eq {M : Type} [CommMonoid M] {n m : ℕ} (f : Fin (n + m) → M) (f₁ : Fin n → M) (f₂ : Fin m → M)
    (h₁ : ∀ i, f (Fin.castAdd m i) = f₁ i) (h₂ : ∀ j, f (Fin.natAdd n j) = f₂ j) :
    ∏ i, f i = (∏ i, f₁ i) * ∏ j, f₂ j := by
  rw [Fin.prod_univ_add]; simp only [h₁, h₂]

theorem forall_append {α : Type} {n m : ℕ} {p : α → Prop} {a : Fin n → α} {a' : Fin m → α}
    (ha : ∀ i, p (a i)) (ha' : ∀ j, p (a' j)) : ∀ i, p (Fin.append a a' i) :=
  Fin.addCases (fun i => by rw [Fin.append_left]; exact ha i) (fun j => by rw [Fin.append_right]; exact ha' j)

theorem forall_append₂ {α β : Type} {n m : ℕ} {p : α → β → Prop} {a : Fin n → α} {a' : Fin m → α}
    {z : Fin n → β} {z' : Fin m → β}
    (h : ∀ i, p (a i) (z i)) (h' : ∀ j, p (a' j) (z' j)) : ∀ i, p (Fin.append a a' i) (Fin.append z z' i) :=
  Fin.addCases (fun i => by rw [Fin.append_left, Fin.append_left]; exact h i)
    (fun j => by rw [Fin.append_right, Fin.append_right]; exact h' j)

end FinAppend
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega.S2P"

section CharOf

variable {H : Type} [Group H] {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
  {L : Type} [CommRing L]

def charOf (Φ : Additive (Abelianization H) →+ ↥(ribbonKernel D)) (u : ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ) :
    H →* Lˣ where
  toFun γ := Additive.toMul (u (Φ (Additive.ofMul (Abelianization.of γ))))
  map_one' := by simp
  map_mul' x y := by simp [ofMul_mul, toMul_add]

@[scoped simp] theorem charOf_apply (Φ : Additive (Abelianization H) →+ ↥(ribbonKernel D))
    (u : ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ) (γ : H) :
    charOf Φ u γ = Additive.toMul (u (Φ (Additive.ofMul (Abelianization.of γ)))) := rfl

theorem charOf_add (Φ : Additive (Abelianization H) →+ ↥(ribbonKernel D))
    (u v : ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ) (γ : H) :
    charOf Φ (u + v) γ = charOf Φ u γ * charOf Φ v γ := by
  simp [toMul_add]

theorem ribbonKernel_eq_zero_of_isOfFinAddOrder (x : ↥(ribbonKernel D)) (hx : IsOfFinAddOrder x) : x = 0 := by
  obtain ⟨n, hn, hnx⟩ := hx.exists_nsmul_eq_zero
  apply Subtype.ext
  funext e
  have h := congrArg (fun y : ↥(ribbonKernel D) => (y : E → ℤ) e) hnx
  simp only [AddSubmonoidClass.coe_nsmul, Pi.smul_apply, nsmul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at h
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (by exact_mod_cast h : n = 0) hn.ne'
  · rw [ZeroMemClass.coe_zero, Pi.zero_apply]; exact h

theorem charOf_eq_one_of_isOfFinOrder (Φ : Additive (Abelianization H) →+ ↥(ribbonKernel D))
    (u : ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ) {γ : H} (hγ : IsOfFinOrder γ) : charOf Φ u γ = 1 := by
  have h1 : IsOfFinAddOrder (Φ (Additive.ofMul (Abelianization.of γ))) :=
    Φ.isOfFinAddOrder ((isOfFinAddOrder_ofMul_iff).mpr (Abelianization.of.isOfFinOrder hγ))
  rw [charOf_apply, ribbonKernel_eq_zero_of_isOfFinAddOrder _ h1, map_zero, toMul_zero]

end CharOf
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega.S2P"

end ECOmega.S2
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega.S2P P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega.S2"
p2m_reactivate "P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one.ECOmega.S2P"

set_option maxHeartbeats 1600000 in
theorem solution

    {r : ℕ} [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (S : Type) [Group S] (scalar : S →* ↥(A.decompositionSubgroup ℚ))
    (ι : ↥(A.decompositionSubgroup ℚ) →* S) (hι : ∀ τ, scalar (ι τ) = τ)

    (K₀ : Type) [Field K₀] [Algebra K₀ A.valuation.Completion] [DecidableEq A.valuation.Completion]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ A.valuation.Completion x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ A.valuation.Completion) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)
    (hϖr : Valued.v (algebraMap K₀ A.valuation.Completion ϖ.ϖ) = Valued.v ((r : ℕ) : A.valuation.Completion))

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]
    [DecidablePred (· ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    (htame : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) w) : ℕ) : A.valuation.Completion) = 1)

    (FC : Type) [Field FC] [Algebra A.valuation.Completion FC] [hcurve : IsCurveOver A.valuation.Completion FC]
    (eFC : FC ≃ₐ[A.valuation.Completion] ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ))
    (hfg : ∃ x : FC, Transcendental A.valuation.Completion x ∧ FiniteDimensional (IntermediateField.adjoin A.valuation.Completion ({x} : Set FC)) FC)

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))
    (hDw : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (MulAction.stabilizer (↥(Γ.map ρ)) e.1.out))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (pt : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → Place A.valuation.Completion FC)
    (hpt_fib : ∀ z z' : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion), pt z = pt z' ↔ ∃ γ : ↥(Γ.map ρ), z' = (γ : PGL(2, K₀)) • z)
    (hpt_onto : Function.Surjective pt)

    (hpt : (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (x : FC),
        x ∈ (pt z).toValuationSubring ↔
          ∃ (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ)),
            (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 ∧ ((eFC x : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = Localization.mk g ⟨h, hh⟩) ∧
      (∀ (z : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) (g h : Omega.HolRingOf ϖ ρ) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
        (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ),
        (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ≠ 0 →
          (pt z).evalAt (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩) = (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z / (show ↥(Omega.holRing ϖ) from h : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z ∧
          (eFC.symm ⟨Localization.mk g ⟨h, hh⟩, hx⟩ ∈ (pt z).toValuationSubring.nonunits ↔ (show ↥(Omega.holRing ϖ) from g : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion) → A.valuation.Completion) z = 0)))

    (galFC : S →* SemilinearAut A.valuation.Completion FC)
    (hgalFC_base : ∀ (σ : S) (c : A.valuation.Completion), SemilinearAut.baseAut (galFC σ) c = (scalar σ) • c)
    (hgal : ∀ σ : S, ∃ (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion),
      n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) ∧ (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))))
    (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hπV : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ v : LT.LatticeTree.Vertex R₀ K₀, πV σ (eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) v)) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (ρ n • v)))
    (hπE : ∀ (σ : S) (n : G) (t : Omega.IsometricAut K₀ A.valuation.Completion), n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G) →
      (∀ y : FC, ((eFC (galFC σ • y) : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ)) = n • Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ ρ t) ((eFC y : ↥(Mumford.invariantFieldOf A.valuation.Completion G (Omega.HolRingOf ϖ ρ) Γ)) : FractionRing (Omega.HolRingOf ϖ ρ))) →
      ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = 1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → sgn σ = -1 ∧ (eE.symm (πE σ (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (hπ_width : ∀ σ e, D.w (πE σ e) = D.w e)
    (hsgn_pos : ∀ σ e, sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hsgn_neg : ∀ σ e, sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e))
    (hπ_inertia : ∀ τ : ↥(A.decompositionSubgroup ℚ),
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ → πV (ι τ) = 1 ∧ πE (ι τ) = 1 ∧ sgn (ι τ) = 1)
    (actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)))
    (hactZ : ∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E), (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e)
    (K : IntermediateField ℚ A.valuation.Completion) (ord : Additive (↥K)ˣ →+ ℤ)
    (hord : ∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
    Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k)))
    (hinK : ∀ σ : ↥(A.decompositionSubgroup ℚ),
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
    ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
      ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion))
    (hhens : ∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k)
    (P : PeriodDatum D (↥K) A.valuation.Completion ord)
    (hQ : (∀ (x y : A.valuation.Completion), x ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → y ∈ Omega.upperHalfPlane K₀ A.valuation.Completion → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ y) →
        ∀ α β : ↥(Γ.map ρ),
          ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥K)ˣ) : ↥K) : A.valuation.Completion) * Omega.period (Γ.map ρ).subtype x y α β = 1)) :
    ∃ eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC,
      Function.Surjective eFull ∧ (∀ u : P.TorusPoints, eFull u = 0 ↔ u ∈ P.periodLattice) ∧
      (∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
        (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) → (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
        ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ), (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
        ∀ (u : P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
        ∀ Dv : Divisor.degZero (K := A.valuation.Completion) (F := FC),
          (Dv : Divisor A.valuation.Completion FC) = Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1 →
          eFull u = Pic0.mk Dv) := by
  classical

  haveI hAC : IsAlgClosed A.valuation.Completion :=
    ValuationSubring.isAlgClosed_completion_of_liesOverPrime r Fact.out A hA
  obtain ⟨-, -, hrk⟩ :=
    ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime r A hA
  have hint : ∀ a : R₀, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ a)) ≤ 1 :=
    fun a => (hR₀ _).1 ⟨a, rfl⟩
  have hv : ∀ a : K₀, Valued.v (algebraMap K₀ A.valuation.Completion a) ≤ 1 → IsLocalization.IsInteger R₀ a := by
    intro a ha
    obtain ⟨b, hb⟩ := (hR₀ a).2 ha
    exact ⟨b, hb⟩
  have hq : ∀ ε : _, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) ^ N ≤ ε := by
    intro ε hε
    obtain ⟨q, hq⟩ := A.valuation_surjective ε
    have hy : Valued.v ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = ε := by
      rw [← hq]; exact Valued.valuedCompletion_apply _
    have hy0 : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) ≠ 0 := fun h => by
      rw [h, Valuation.map_zero] at hy; exact hε hy.symm
    have hlt : Valued.v (algebraMap K₀ A.valuation.Completion (algebraMap R₀ K₀ ϖ₀)) < 1 := by
      rw [hϖ]; exact ϖ.lt_one
    obtain ⟨N, hN⟩ := hrk _ _ hlt hy0
    exact ⟨N, hy ▸ hN⟩
  haveI hfinq : Finite (R₀ ⧸ Ideal.span {ϖ₀}) := by
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mp hϖ₀
    exact Finite.of_equiv (IsLocalRing.ResidueField R₀) (Ideal.quotEquivOfEq hmax).toEquiv
  haveI hdomH : IsDomain ↥(Omega.holRing ϖ) := (inferInstance : IsDomain (Omega.HolRingOf ϖ ρ))
  have hdeg : ∀ w : Place A.valuation.Completion FC, w.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  have hActs : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) (Γ.map ρ).subtype := fun g w => rfl
  obtain ⟨hconn, hcol⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  obtain ⟨hadj1, -, -⟩ := CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) hconn hcol (LT.LatticeTree.stdVertex R₀ K₀)
  have hτ : ∀ (g : ↥(Γ.map ρ)) (w : LT.LatticeTree.Vertex R₀ K₀),
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) (g • w) =
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := fun g w => htp g.2 w
  have hadj : ∀ u w : LT.LatticeTree.Vertex R₀ K₀, (BruhatTits.tree R₀ K₀).Adj u w →
      Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) u ≠
        Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) w := by
    intro u w huw h
    have h1 := hadj1 u w huw
    rw [← h] at h1
    have h2 : (1 : ZMod 2) = 0 := add_left_cancel (h1.symm.trans (add_zero _).symm)
    exact absurd h2 (by decide)
  have hfinV : ∀ w : LT.LatticeTree.Vertex R₀ K₀, Finite (MulAction.stabilizer (↥(Γ.map ρ)) w) :=
    fun w => CerednikDrinfeld.BruhatTits.finite_stabilizer_vertex_of_finite_stabilizer_dart R₀ K₀ ↥(Γ.map ρ) hfin w
  haveI hfinQ : Finite (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) := Finite.of_equiv V eV.symm
  have hdisc : Omega.IsDiscrete A.valuation.Completion (Γ.map ρ).subtype := by
    refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq
      (Γ.map ρ).subtype ?_
    haveI := hfinV (LT.LatticeTree.stdVertex R₀ K₀)
    exact Set.Finite.subset (s := (MulAction.stabilizer (↥(Γ.map ρ)) (LT.LatticeTree.stdVertex R₀ K₀) : Set _))
      (Set.toFinite _) (fun γ hγ => hγ)
  have hfo : ∀ (w : LT.LatticeTree.Vertex R₀ K₀) (γ : ↥(Γ.map ρ)), γ ∈ MulAction.stabilizer (↥(Γ.map ρ)) w →
      IsOfFinOrder γ := by
    intro w γ hγ
    haveI := hfinV w
    exact (MulAction.stabilizer (↥(Γ.map ρ)) w).subtype.isOfFinOrder
      (isOfFinOrder_of_finite (⟨γ, hγ⟩ : ↥(MulAction.stabilizer (↥(Γ.map ρ)) w)))

  have hDa' : ∀ e : E, eV.symm (D.a e) =
      Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eE.symm e).1.out.fst := by
    intro e
    rw [Equiv.symm_apply_eq]
    conv_lhs => rw [← eE.apply_symm_apply e]
    exact hDa (eE.symm e)
  have hDb' : ∀ e : E, eV.symm (D.b e) =
      Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) (eE.symm e).1.out.snd := by
    intro e
    rw [Equiv.symm_apply_eq]
    conv_lhs => rw [← eE.apply_symm_apply e]
    exact hDb (eE.symm e)
  have hΦ' : ∀ g : ↥(Γ.map ρ), ((Φ (Additive.ofMul (Abelianization.of g)) : ↥(ribbonKernel D)) : E → ℤ) =
      Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e => (eE.symm e).1) v₀ g := by
    intro g
    funext e
    have h := hΦ g (eE.symm e)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    unfold Mumford.pathCycle Mumford.walkCycle
    split_ifs <;> rfl
  obtain ⟨hΦsurj, -⟩ :=
    CerednikDrinfeld.Mumford.surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle
      (BruhatTits.tree R₀ K₀) (CerednikDrinfeld.BruhatTits.tree_isTree R₀ K₀)
      (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
      hτ hadj D eE.symm eV.symm hDa' hDb' v₀ Φ hΦ'

  have hQLval : ∀ x y : ↥(ribbonKernel D),
      ((Additive.toMul (P.QL x y) : (A.valuation.Completion)ˣ) : A.valuation.Completion) =
        (((Additive.toMul (P.Q x y) : (↥K)ˣ) : ↥K) : A.valuation.Completion) := fun x y => rfl

  have hJ : ∀ u : P.TorusPoints,
      ∃ (n : ℕ) (a b : Fin n → A.valuation.Completion) (z₀ : A.valuation.Completion),
        (∀ i, a i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) ∧
        (∀ i, b i ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) ∧
        z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion ∧
        (∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a i) ≠ z₀) ∧
        (∀ i (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b i) ≠ z₀) ∧
        ∀ β : ↥(Γ.map ρ), ((ECOmega.S2.charOf Φ u β : (A.valuation.Completion)ˣ) : A.valuation.Completion) =
          ∏ i, Omega.theta (Γ.map ρ).subtype (a i) (b i) z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀) := by
    intro u
    have hJu := CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring R₀ K₀ ϖ₀ hϖ₀
      A.valuation.Completion hint hv hq hrk ϖ hex (Γ.map ρ).subtype hActs hfinV
      (Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) hτ hadj htame (ECOmega.S2.charOf Φ u)
      (fun γ hγ => ECOmega.S2.charOf_eq_one_of_isOfFinOrder Φ u hγ)
    simpa only [Subgroup.coe_subtype] using hJu
  choose nR aR bR zR haR hbR hzR hzaR hzbR hmulR using hJ

  obtain ⟨e0, he0⟩ : ∃ e0 : P.TorusPoints → Pic0 A.valuation.Completion FC, ∀ u, e0 u =
      Pic0.mk ⟨∑ i, (Finsupp.single (pt ⟨aR u i, haR u i⟩) 1 - Finsupp.single (pt ⟨bR u i, hbR u i⟩) 1),
        ECOmega.S2.sum_single_sub_single_mem_degZero hdeg (fun i => pt ⟨aR u i, haR u i⟩) (fun i => pt ⟨bR u i, hbR u i⟩)⟩ :=
    ⟨_, fun u => rfl⟩

  have hL : ∀ (u : P.TorusPoints) (m : ℕ) (a' b' z' : Fin m → A.valuation.Completion)
      (ha' : ∀ j, a' j ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
      (hb' : ∀ j, b' j ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
      (hz' : ∀ j, z' j ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
      (hza' : ∀ j (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (a' j) ≠ z' j)
      (hzb' : ∀ j (γ : ↥(Γ.map ρ)), Omega.pmoebius K₀ (γ : PGL(2, K₀)) (b' j) ≠ z' j)
      (hm : ∀ β : ↥(Γ.map ρ), ((ECOmega.S2.charOf Φ u β : (A.valuation.Completion)ˣ) : A.valuation.Completion) =
        ∏ j, Omega.theta (Γ.map ρ).subtype (a' j) (b' j) (z' j) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (z' j)))
      (h0 : (∑ j, (Finsupp.single (pt ⟨a' j, ha' j⟩) 1 - Finsupp.single (pt ⟨b' j, hb' j⟩) 1) :
        Divisor A.valuation.Completion FC) ∈ Divisor.degZero (K := A.valuation.Completion) (F := FC)),
      e0 u = Pic0.mk ⟨∑ j, (Finsupp.single (pt ⟨a' j, ha' j⟩) 1 - Finsupp.single (pt ⟨b' j, hb' j⟩) 1), h0⟩ := by
    intro u m a' b' z' ha' hb' hz' hza' hzb' hm h0
    rw [he0, ECOmega.S2.mk_eq_mk_iff]
    have hD := AlgebraicCurve.Pic0.isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin htame FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ
      (nR u) m (aR u) (bR u) (fun _ => zR u) a' b' z' (haR u) (hbR u) (fun _ => hzR u) ha' hb' hz'
      (hzaR u) (hzbR u) hza' hzb' (fun β => by rw [← hm β]; exact (hmulR u β).symm)
    exact hD

  have hadd : ∀ u v : P.TorusPoints, e0 (u + v) = e0 u + e0 v := by
    intro u v
    have hmem := ECOmega.S2.sum_single_sub_single_mem_degZero hdeg
      (fun j => pt ⟨Fin.append (aR u) (aR v) j, ECOmega.S2.forall_append (haR u) (haR v) j⟩)
      (fun j => pt ⟨Fin.append (bR u) (bR v) j, ECOmega.S2.forall_append (hbR u) (hbR v) j⟩)
    have h := hL (u + v) (nR u + nR v) (Fin.append (aR u) (aR v)) (Fin.append (bR u) (bR v))
      (Fin.append (fun _ => zR u) (fun _ => zR v))
      (ECOmega.S2.forall_append (haR u) (haR v)) (ECOmega.S2.forall_append (hbR u) (hbR v))
      (ECOmega.S2.forall_append (p := fun z => z ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
        (a := fun _ => zR u) (a' := fun _ => zR v) (fun _ => hzR u) (fun _ => hzR v))
      (ECOmega.S2.forall_append₂ (p := fun x z => ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ z)
        (z := fun _ => zR u) (z' := fun _ => zR v) (hzaR u) (hzaR v))
      (ECOmega.S2.forall_append₂ (p := fun x z => ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ z)
        (z := fun _ => zR u) (z' := fun _ => zR v) (hzbR u) (hzbR v))
      (fun β => by
        rw [ECOmega.S2.charOf_add, Units.val_mul, hmulR u β, hmulR v β]
        exact (ECOmega.S2.prod_fin_add_eq _ _ _
          (fun i => by simp only [Fin.append_left]) (fun j => by simp only [Fin.append_right])).symm)
      hmem
    rw [h, he0 u, he0 v, ← Pic0.mk_add]
    congr 1
    apply Subtype.ext
    rw [AddSubgroup.coe_add]
    exact ECOmega.S2.sum_fin_add_eq _ _ _
      (fun i => by
        have ha : (⟨Fin.append (aR u) (aR v) (Fin.castAdd (nR v) i), ECOmega.S2.forall_append (haR u) (haR v) _⟩ :
            ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) = ⟨aR u i, haR u i⟩ := Subtype.ext (Fin.append_left _ _ i)
        have hb : (⟨Fin.append (bR u) (bR v) (Fin.castAdd (nR v) i), ECOmega.S2.forall_append (hbR u) (hbR v) _⟩ :
            ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) = ⟨bR u i, hbR u i⟩ := Subtype.ext (Fin.append_left _ _ i)
        rw [ha, hb])
      (fun j => by
        have ha : (⟨Fin.append (aR u) (aR v) (Fin.natAdd (nR u) j), ECOmega.S2.forall_append (haR u) (haR v) _⟩ :
            ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) = ⟨aR v j, haR v j⟩ := Subtype.ext (Fin.append_right _ _ j)
        have hb : (⟨Fin.append (bR u) (bR v) (Fin.natAdd (nR u) j), ECOmega.S2.forall_append (hbR u) (hbR v) _⟩ :
            ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) = ⟨bR v j, hbR v j⟩ := Subtype.ext (Fin.append_right _ _ j)
        rw [ha, hb])
  obtain ⟨eFull, heFull⟩ : ∃ eFull : P.TorusPoints →+ Pic0 A.valuation.Completion FC, ∀ u, eFull u = e0 u :=
    ⟨AddMonoidHom.mk' e0 hadd, fun u => rfl⟩

  have hPIN : ∀ (a b z₀ : A.valuation.Completion) (ha : a ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
      (hb : b ∈ Omega.upperHalfPlane K₀ A.valuation.Completion) (hz₀ : z₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion),
      (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) a ≠ z₀) →
      (∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) b ≠ z₀) →
      ∀ (c : ↥(Γ.map ρ) →* (A.valuation.Completion)ˣ),
      (∀ β : ↥(Γ.map ρ), ((c β : (A.valuation.Completion)ˣ) : A.valuation.Completion) =
        Omega.theta (Γ.map ρ).subtype a b z₀ (Omega.pmoebius K₀ (β : PGL(2, K₀)) z₀)) →
      ∀ (u : P.TorusPoints), (∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ)) →
      e0 u = Pic0.mk ⟨Finsupp.single (pt ⟨a, ha⟩) 1 - Finsupp.single (pt ⟨b, hb⟩) 1,
        ECOmega.S2.single_sub_single_mem_degZero hdeg _ _⟩ := by
    intro a b z₀ ha hb hz₀ hz₀a hz₀b c hc u hu
    have h := hL u 1 (fun _ => a) (fun _ => b) (fun _ => z₀) (fun _ => ha) (fun _ => hb) (fun _ => hz₀)
      (fun _ => hz₀a) (fun _ => hz₀b)
      (fun β => by
        rw [Fin.prod_univ_one, ← hc β, ECOmega.S2.charOf_apply, hu, toMul_ofMul])
      (by rw [Fin.sum_univ_one]; exact ECOmega.S2.single_sub_single_mem_degZero hdeg _ _)
    rw [h]
    congr 1
    apply Subtype.ext
    exact Fin.sum_univ_one _
  refine ⟨eFull, ?surj, ?ker, ?pin⟩

  case pin =>
    intro a b z₀ ha hb hz₀ hz₀a hz₀b c hc u hu Dv hDv
    rw [heFull, hPIN a b z₀ ha hb hz₀ hz₀a hz₀b c hc u hu]
    congr 1
    exact Subtype.ext hDv.symm

  case surj =>
    rw [← AddMonoidHom.range_eq_top]
    apply ECOmega.S2.eq_top_of_forall_mk_single_sub_single_mem hdeg
    intro P₁ Q₁
    obtain ⟨za, rfl⟩ := hpt_onto P₁
    obtain ⟨zb, rfl⟩ := hpt_onto Q₁
    obtain ⟨z₀, hz₀, hz₀a, hz₀b⟩ := ECOmega.S2P.exists_mem_upperHalfPlane_forall_pmoebius_ne ϖ hex
      (Γ.map ρ).subtype hdisc za.2 zb.2
    have hcE := CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq K₀ A.valuation.Completion ϖ hex
      (Γ.map ρ).subtype hdisc za.2 zb.2 hz₀ hz₀a hz₀b
    obtain ⟨c, hc, -⟩ := hcE
    have hck : ∀ (w : LT.LatticeTree.Vertex R₀ K₀) (γ : ↥(Γ.map ρ)),
        γ ∈ MulAction.stabilizer (↥(Γ.map ρ)) w → c γ = 1 := by
      intro w γ hγ
      apply Units.ext
      rw [hc, Units.val_one]
      exact CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder K₀ A.valuation.Completion ϖ hex
        (Γ.map ρ).subtype hdisc za.2 zb.2 hz₀ hz₀a hz₀b γ (hfo w γ hγ)
    have hCF := CerednikDrinfeld.Mumford.existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer
      K₀ R₀ G ρ Γ htp E V D eV eE hDa hDb v₀ Φ hΦ A.valuation.Completion c hck
    obtain ⟨u, hu, -⟩ := hCF
    rw [AddMonoidHom.mem_range]
    refine ⟨u, ?_⟩
    rw [heFull]
    exact hPIN (za : A.valuation.Completion) (zb : A.valuation.Completion) z₀ za.2 zb.2 hz₀ hz₀a hz₀b c hc u hu

  case ker =>
    intro u
    rw [heFull]
    constructor
    ·
      intro hu0
      rw [he0, ECOmega.S2.mk_eq_zero_iff] at hu0
      have hAb := AlgebraicCurve.Pic0.exists_prod_theta_eq_period_of_isPrincipal_of_v_card_stabilizer_eq_one A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin htame FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ
        (nR u) (aR u) (bR u) (fun _ => zR u) (haR u) (hbR u) (fun _ => hzR u) (hzaR u) (hzbR u) hu0
      obtain ⟨x, y, hx, hy, hxy, α, hper⟩ := hAb
      have hcu : ∀ β : ↥(Γ.map ρ),
          ((((Additive.toMul (P.Q (Φ (Additive.ofMul (Abelianization.of α))) (Φ (Additive.ofMul (Abelianization.of β))))) :
              (↥K)ˣ) : ↥K) : A.valuation.Completion) *
            ((ECOmega.S2.charOf Φ u β : (A.valuation.Completion)ˣ) : A.valuation.Completion) = 1 := by
        intro β
        have hp := hper β
        beta_reduce at hp
        rw [hmulR u β, hp]
        exact hQ x y hx hy hxy α β
      have hck : ∀ (w : LT.LatticeTree.Vertex R₀ K₀) (γ : ↥(Γ.map ρ)),
          γ ∈ MulAction.stabilizer (↥(Γ.map ρ)) w → ECOmega.S2.charOf Φ u γ = 1 :=
        fun w γ hγ => ECOmega.S2.charOf_eq_one_of_isOfFinOrder Φ u (hfo w γ hγ)
      have hCF := CerednikDrinfeld.Mumford.existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer
        K₀ R₀ G ρ Γ htp E V D eV eE hDa hDb v₀ Φ hΦ A.valuation.Completion (ECOmega.S2.charOf Φ u) hck
      obtain ⟨u₀, -, huniq⟩ := hCF
      have h1 : u = u₀ := huniq u (fun γ => rfl)
      have h2 : P.QL (-(Φ (Additive.ofMul (Abelianization.of α)))) = u₀ := by
        refine huniq _ fun β => ?_
        rw [map_neg, LinearMap.neg_apply, ← ofMul_toMul (P.QL _ _), ← ofMul_inv]
        congr 1
        symm
        apply eq_inv_of_mul_eq_one_right
        apply Units.ext
        rw [Units.val_mul, Units.val_one, hQLval]
        exact hcu β
      show u ∈ P.periodLattice
      rw [h1, ← h2]
      exact LinearMap.mem_range_self _ _
    ·
      intro huΛ
      have huΛ' : u ∈ LinearMap.range P.QL := huΛ
      obtain ⟨xZ, hxZ⟩ := LinearMap.mem_range.mp huΛ'
      obtain ⟨tA, rfl⟩ := hΦsurj xZ
      obtain ⟨α, hα⟩ : ∃ α : ↥(Γ.map ρ), Abelianization.of α = Additive.toMul tA :=
        QuotientGroup.induction_on (C := fun x : Abelianization ↥(Γ.map ρ) => ∃ α : ↥(Γ.map ρ), Abelianization.of α = x)
          (Additive.toMul tA) (fun z => ⟨z, rfl⟩)
      obtain rfl : Additive.ofMul (Abelianization.of α) = tA := by rw [hα, ofMul_toMul]

      obtain ⟨x₀, hx₀0⟩ := ECOmega.S2P.exists_mem_affinoid_zero R₀ K₀ ϖ₀ hϖ₀ A.valuation.Completion hint hv hq hrk ϖ hϖ hex
      have hx₀ : x₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion := Omega.affinoid_subset_upperHalfPlane ϖ 0 hx₀0
      obtain ⟨y₀, hy₀, hxy₀, -⟩ := ECOmega.S2P.exists_mem_upperHalfPlane_forall_pmoebius_ne ϖ hex
        (Γ.map ρ).subtype hdisc hx₀ hx₀
      have hαx₀ : Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀ ∈ Omega.upperHalfPlane K₀ A.valuation.Completion :=
        Omega.pmoebius_mem_upperHalfPlane K₀ hx₀ _
      have hxy₀c : ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x₀ ≠ y₀ := fun γ => hxy₀ γ
      have hxy₀' : ∀ γ : ↥(Γ.map ρ),
          Omega.pmoebius K₀ (γ : PGL(2, K₀)) (Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀) ≠ y₀ := by
        intro γ
        rw [← Omega.pmoebius_mul K₀ hx₀, ← Subgroup.coe_mul]
        exact hxy₀ (γ * α)

      have hm : ∀ β : ↥(Γ.map ρ),
          ∏ i, Omega.theta (Γ.map ρ).subtype (Fin.append (aR u) (fun _ : Fin 1 => x₀) i)
              (Fin.append (bR u) (fun _ : Fin 1 => Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀) i)
              (Fin.append (fun _ => zR u) (fun _ : Fin 1 => y₀) i)
              (Omega.pmoebius K₀ (β : PGL(2, K₀)) (Fin.append (fun _ => zR u) (fun _ : Fin 1 => y₀) i)) =
            ∏ j : Fin 0, Omega.theta (Γ.map ρ).subtype ((Fin.elim0 : Fin 0 → A.valuation.Completion) j)
              ((Fin.elim0 : Fin 0 → A.valuation.Completion) j) ((Fin.elim0 : Fin 0 → A.valuation.Completion) j)
              (Omega.pmoebius K₀ (β : PGL(2, K₀)) ((Fin.elim0 : Fin 0 → A.valuation.Completion) j)) := by
        intro β
        rw [Fin.prod_univ_zero]
        refine (ECOmega.S2.prod_fin_add_eq _
          (fun i => Omega.theta (Γ.map ρ).subtype (aR u i) (bR u i) (zR u) (Omega.pmoebius K₀ (β : PGL(2, K₀)) (zR u)))
          (fun _ : Fin 1 => Omega.theta (Γ.map ρ).subtype x₀ (Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀) y₀
            (Omega.pmoebius K₀ (β : PGL(2, K₀)) y₀))
          (fun i => ?_) (fun j => ?_)).trans ?_
        · simp only [Fin.append_left]
        · simp only [Fin.append_right]
        · rw [Fin.prod_univ_one, ← hmulR u β, ← hxZ, ECOmega.S2.charOf_apply, hQLval]
          exact hQ x₀ y₀ hx₀ hy₀ hxy₀c α β
      have hD := AlgebraicCurve.Pic0.isPrincipal_sum_sub_sum_of_prod_theta_eq_of_v_card_stabilizer_eq_one A hA S scalar ι hι K₀ R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex hϖr G ρ Γ htp hfin htame FC eFC hfg E V D eV eE hDa hDb hDw v₀ Φ hΦ pt hpt_fib hpt_onto hpt galFC hgalFC_base hgal πV πE sgn hπV hπE hπ_width hsgn_pos hsgn_neg hπ_inertia actZ hactZ
        (nR u + 1) 0
        (Fin.append (aR u) (fun _ : Fin 1 => x₀))
        (Fin.append (bR u) (fun _ : Fin 1 => Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀))
        (Fin.append (fun _ => zR u) (fun _ : Fin 1 => y₀))
        Fin.elim0 Fin.elim0 Fin.elim0
        (ECOmega.S2.forall_append (haR u) (fun _ => hx₀)) (ECOmega.S2.forall_append (hbR u) (fun _ => hαx₀))
        (ECOmega.S2.forall_append (p := fun z => z ∈ Omega.upperHalfPlane K₀ A.valuation.Completion)
          (a := fun _ => zR u) (a' := fun _ : Fin 1 => y₀) (fun _ => hzR u) (fun _ => hy₀))
        (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
        (ECOmega.S2.forall_append₂ (p := fun x z => ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ z)
          (z := fun _ => zR u) (z' := fun _ : Fin 1 => y₀) (hzaR u) (fun _ => hxy₀c))
        (ECOmega.S2.forall_append₂ (p := fun x z => ∀ γ : ↥(Γ.map ρ), Omega.pmoebius K₀ (γ : PGL(2, K₀)) x ≠ z)
          (z := fun _ => zR u) (z' := fun _ : Fin 1 => y₀) (hzbR u) (fun _ => hxy₀'))
        (fun j => j.elim0) (fun j => j.elim0)
        hm
      rw [he0, ECOmega.S2.mk_eq_zero_iff]

      have hpt0 : pt ⟨x₀, hx₀⟩ = pt ⟨Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀, hαx₀⟩ :=
        (hpt_fib _ _).mpr ⟨α, rfl⟩
      rw [Fin.sum_univ_zero, sub_zero] at hD
      rw [ECOmega.S2.sum_fin_add_eq _
        (fun i => Finsupp.single (pt ⟨aR u i, haR u i⟩) 1 - Finsupp.single (pt ⟨bR u i, hbR u i⟩) 1)
        (fun _ : Fin 1 => (0 : Divisor A.valuation.Completion FC))
        (fun i => by
          have ha : (⟨Fin.append (aR u) (fun _ : Fin 1 => x₀) (Fin.castAdd 1 i),
              ECOmega.S2.forall_append (haR u) (fun _ => hx₀) _⟩ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) =
              ⟨aR u i, haR u i⟩ := Subtype.ext (Fin.append_left (aR u) (fun _ : Fin 1 => x₀) i)
          have hb : (⟨Fin.append (bR u) (fun _ : Fin 1 => Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀) (Fin.castAdd 1 i),
              ECOmega.S2.forall_append (hbR u) (fun _ => hαx₀) _⟩ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) =
              ⟨bR u i, hbR u i⟩ := Subtype.ext (Fin.append_left (bR u) (fun _ : Fin 1 => Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀) i)
          rw [ha, hb])
        (fun j => by
          have ha : (⟨Fin.append (aR u) (fun _ : Fin 1 => x₀) (Fin.natAdd (nR u) j),
              ECOmega.S2.forall_append (haR u) (fun _ => hx₀) _⟩ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) =
              ⟨x₀, hx₀⟩ := Subtype.ext (Fin.append_right (aR u) (fun _ : Fin 1 => x₀) j)
          have hb : (⟨Fin.append (bR u) (fun _ : Fin 1 => Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀) (Fin.natAdd (nR u) j),
              ECOmega.S2.forall_append (hbR u) (fun _ => hαx₀) _⟩ : ↥(Omega.upperHalfPlane K₀ A.valuation.Completion)) =
              ⟨Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀, hαx₀⟩ := Subtype.ext (Fin.append_right (bR u) (fun _ : Fin 1 => Omega.pmoebius K₀ ((α : ↥(Γ.map ρ)) : PGL(2, K₀)) x₀) j)
          rw [ha, hb, hpt0, sub_self]),
        Fin.sum_univ_one, add_zero] at hD
      exact hD

end
end S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_torusPoints_uniformization_of_periodDatum_of_mumfordQuotient_of_v_card_stabilizer_eq_one (solution)
