-- Prove2me | solution 1 for AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1e513adf-ddab-5f0f-be11-1fc50a602cef

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_LocalGL2_existsUnique_algHom_heckeIndicator_eq
import Theorems.Thm_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_central_isUnit
import Theorems.Thm_LocalGL2_localHeckeMul_comm
import Theorems.Thm_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists
import Theorems.Thm_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Definitions.Def_LatticeTreeOrbital
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_LocalGL2_heckeIndicator_diagPi_mul_self
import Theorems.Thm_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_pow
import Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
import Theorems.Thm_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_unitOrbitalCount_ne_zero_of_anisotropic
import Theorems.Thm_LT_LatticeTree_unitOrbitalCount_ne_zero_of_eisenstein
import Theorems.Thm_LT_LatticeTree_nonempty_fixedVertexSet_or_exists_swap_of_iterate_act
import Theorems.Thm_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
import Theorems.Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_anisotropic
import Theorems.Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein
import Theorems.Thm_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
import Theorems.Thm_LT_LatticeTree_even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow
import Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
import Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_act_swap_of_isWithin_one
import Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
import Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
import Theorems.Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton
import Theorems.Thm_LocalGL2_exists_basis_heckeIndicator_zpow
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Mathlib.Algebra.Module.Lattice
import Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
import Theorems.Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
import Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists
import Theorems.Thm_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Theorems.Thm_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
import Theorems.Thm_AutomorphicForm_exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one
import Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal
import Theorems.Thm_AutomorphicForm_sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
import Theorems.Thm_AutomorphicForm_exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot
import Theorems.Thm_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly
import Theorems.Thm_AutomorphicForm_twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open scoped Pointwise

namespace SatakeValues

section Generic

open HeckePair

variable {G : Type*} [Group G] {U : Subgroup G} {R₀ : Type*} [CommRing R₀]

private theorem doubleCoset_mul_mul {u v : G} (hu : u ∈ U) (hv : v ∈ U) (g : G) :
    doubleCoset U (u * g * v) = doubleCoset U g := by
  ext x
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a * u, mul_mem ha hu, v * b, mul_mem hv hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a * u⁻¹, mul_mem ha (inv_mem hu), v⁻¹ * b, mul_mem (inv_mem hv) hb, by group⟩

private theorem heckeIndicator_mul_mul {u v : G} (hu : u ∈ U) (hv : v ∈ U) (g : G) (h₁ h₂) :
    (heckeIndicator R₀ (u * g * v) h₁ : HeckeAlgebra U R₀) = heckeIndicator R₀ g h₂ :=
  Subtype.ext (congrArg (fun s : Set G => Set.indicator s (1 : G → R₀)) (doubleCoset_mul_mul hu hv g))

private theorem mem_doubleCoset_central_mul_iff {z : G} (hz : ∀ x : G, z * x = x * z) {g x : G} :
    x ∈ doubleCoset U (z * g) ↔ z⁻¹ * x ∈ doubleCoset U g := by
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [show a * (z * g) * b = z * (a * g * b) by rw [← mul_assoc a z g, ← hz a]; group]
    group
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨a, ha, b, hb, ?_⟩
    have h' : z * (a * g * b) = x := by rw [h]; group
    rw [← h', ← mul_assoc a z g, ← hz a]
    group

private theorem image_mk_support_heckeIndicator_central {z : G} (hz : ∀ x : G, z * x = x * z) (hfz) :
    QuotientGroup.mk '' Function.support ((heckeIndicator R₀ z hfz : HeckeAlgebra U R₀) : G → R₀) ⊆
      ((({QuotientGroup.mk z} : Finset (G ⧸ U)) : Set (G ⧸ U))) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Finset.coe_singleton, Set.mem_singleton_iff]
  have hyD : y ∈ doubleCoset U z := by
    by_contra hyD
    exact hy (heckeIndicator_apply_of_notMem hfz hyD)
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hyD
  refine (QuotientGroup.eq.mpr ?_).symm
  rw [show z⁻¹ * (a * z * b) = a * b by rw [← hz a]; group]
  exact mul_mem ha hb

private theorem heckeIndicator_central_mul {z : G} (hz : ∀ x : G, z * x = x * z) (g : G) (hfz hfg hfzg) :
    (heckeIndicator R₀ z hfz : HeckeAlgebra U R₀) * heckeIndicator R₀ g hfg = heckeIndicator R₀ (z * g) hfzg := by
  apply Subtype.ext
  funext x
  rw [coe_mul, conv_eq_sum _ _ x (image_mk_support_heckeIndicator_central hz hfz), Finset.sum_singleton,
    convTerm_mk, heckeIndicator_apply_of_mem hfz (self_mem_doubleCoset z), one_mul]
  by_cases hx : z⁻¹ * x ∈ doubleCoset U g
  · rw [heckeIndicator_apply_of_mem hfg hx,
      heckeIndicator_apply_of_mem hfzg ((mem_doubleCoset_central_mul_iff hz).mpr hx)]
  · rw [heckeIndicator_apply_of_notMem hfg hx,
      heckeIndicator_apply_of_notMem hfzg (fun h => hx ((mem_doubleCoset_central_mul_iff hz).mp h))]

private theorem heckeIndicator_one (hf) : (heckeIndicator R₀ (1 : G) hf : HeckeAlgebra U R₀) = 1 :=
  heckeIndicator_of_mem (one_mem U) hf

end Generic

section ClosedForm

open AddMonoidAlgebra

variable {R₀ : Type*} [CommRing R₀]

private def satCoeff (q : R₀) (m k : ℕ) : R₀ :=
  if k = 0 then 1 else if k = m then q ^ m else (q - 1) * q ^ (k - 1)

private noncomputable def sat (q : R₀) (m : ℕ) : AddMonoidAlgebra R₀ (ℤ × ℤ) :=
  ∑ k ∈ Finset.range (m + 1), satCoeff q m k • single ((k : ℤ), ((m - k : ℕ) : ℤ)) (1 : R₀)

private theorem satCoeff_zero_left (q : R₀) (m : ℕ) : satCoeff q m 0 = 1 := by simp [satCoeff]

private theorem satCoeff_self (q : R₀) {m : ℕ} (hm : m ≠ 0) : satCoeff q m m = q ^ m := by simp [satCoeff, hm]

private theorem satCoeff_of_lt (q : R₀) {m k : ℕ} (hk0 : k ≠ 0) (hkm : k ≠ m) :
    satCoeff q m k = (q - 1) * q ^ (k - 1) := by
  simp [satCoeff, hk0, hkm]

private theorem satCoeff_middle (q : R₀) {e : ℕ} (he : e ≠ 0) : satCoeff q (2 * e) e = (q - 1) * q ^ (e - 1) :=
  satCoeff_of_lt q he (by omega)

private theorem two_mul_lt_iff_lt_half (m k : ℕ) : 2 * k < m ↔ k < (m + 1) / 2 := by omega

private theorem sum_satCoeff_range (q : R₀) {m : ℕ} (hm : m ≠ 0) :
    ∑ k ∈ Finset.range ((m + 1) / 2), satCoeff q m k = q ^ ((m - 1) / 2) := by
  obtain ⟨N, hN⟩ : ∃ N, (m + 1) / 2 = N + 1 := ⟨(m + 1) / 2 - 1, by omega⟩
  have hN' : (m - 1) / 2 = N := by omega
  rw [hN, hN', Finset.sum_range_succ', satCoeff_zero_left]
  have hmid : ∀ j ∈ Finset.range N, satCoeff q m (j + 1) = (q - 1) * q ^ j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [satCoeff_of_lt q (m := m) (k := j + 1) (by omega) (by omega), Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hmid, ← Finset.mul_sum, mul_comm (q - 1), geom_sum_mul]
  ring

private theorem single_zero_zero : (single ((0 : ℤ), (0 : ℤ)) (1 : R₀) : AddMonoidAlgebra R₀ (ℤ × ℤ)) = 1 :=
  one_def.symm

private theorem sat_apply (q : R₀) {m k : ℕ} (hk : k ≤ m) :
    (sat q m).coeff ((k : ℤ), ((m - k : ℕ) : ℤ)) = satCoeff q m k := by
  classical
  change (sat q m).coeff ((k : ℤ), ((m - k : ℕ) : ℤ)) = satCoeff q m k
  simp only [sat, coeff_sum, Finsupp.finsetSum_apply, coeff_smul, Finsupp.smul_apply]
  rw [Finset.sum_eq_single k]
  · change satCoeff q m k • (Finsupp.single ((k : ℤ), ((m - k : ℕ) : ℤ)) (1 : R₀)) ((k : ℤ), ((m - k : ℕ) : ℤ)) =
      satCoeff q m k
    rw [Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro j _ hjk
    change satCoeff q m j • (Finsupp.single ((j : ℤ), ((m - j : ℕ) : ℤ)) (1 : R₀)) ((k : ℤ), ((m - k : ℕ) : ℤ)) = 0
    rw [Finsupp.single_apply, if_neg, smul_zero]
    intro h
    exact hjk (by exact_mod_cast (Prod.mk.inj h).1)
  · intro hk'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hk'

private theorem sat_apply_of_add_ne (q : R₀) {m : ℕ} {i j : ℤ} (h : i + j ≠ m) : (sat q m).coeff (i, j) = 0 := by
  classical
  change (sat q m).coeff (i, j) = 0
  simp only [sat, coeff_sum, Finsupp.finsetSum_apply, coeff_smul, Finsupp.smul_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  change satCoeff q m k • (Finsupp.single ((k : ℤ), ((m - k : ℕ) : ℤ)) (1 : R₀)) (i, j) = 0
  rw [Finsupp.single_apply, if_neg, smul_zero]
  rintro ⟨⟩
  apply h
  push_cast [Nat.cast_sub (Nat.lt_succ_iff.mp hk)]
  ring

private noncomputable def X : AddMonoidAlgebra R₀ (ℤ × ℤ) := single ((1 : ℤ), (0 : ℤ)) 1

private noncomputable def Y : AddMonoidAlgebra R₀ (ℤ × ℤ) := single ((0 : ℤ), (1 : ℤ)) 1

private noncomputable def Q (q : R₀) : AddMonoidAlgebra R₀ (ℤ × ℤ) := algebraMap R₀ (AddMonoidAlgebra R₀ (ℤ × ℤ)) q

private noncomputable def geom (q : R₀) (n : ℕ) : AddMonoidAlgebra R₀ (ℤ × ℤ) :=
  ∑ j ∈ Finset.range n, (Q q * X) ^ j * Y ^ (n - 1 - j)

private theorem Q_mul (q : R₀) (f : AddMonoidAlgebra R₀ (ℤ × ℤ)) : Q q * f = q • f := (Algebra.smul_def q f).symm

private theorem Q_pow (q : R₀) (a : ℕ) : Q q ^ a = Q (q ^ a) := by rw [Q, Q, map_pow]

private theorem Q_sub_one (q : R₀) : Q q - 1 = Q (q - 1) := by rw [Q, Q, map_sub, map_one]

private theorem Q_add_one (q : R₀) : Q q + 1 = Q (q + 1) := by rw [Q, Q, map_add, map_one]

private theorem X_pow (a : ℕ) : (X : AddMonoidAlgebra R₀ (ℤ × ℤ)) ^ a = single ((a : ℤ), (0 : ℤ)) 1 := by
  rw [X, single_pow, one_pow, Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero]

private theorem Y_pow (b : ℕ) : (Y : AddMonoidAlgebra R₀ (ℤ × ℤ)) ^ b = single ((0 : ℤ), (b : ℤ)) 1 := by
  rw [Y, single_pow, one_pow, Prod.smul_mk, smul_zero, nsmul_eq_mul, mul_one]

private theorem QX_pow (q : R₀) (a : ℕ) : (Q q * X) ^ a = q ^ a • single ((a : ℤ), (0 : ℤ)) (1 : R₀) := by
  rw [mul_pow, Q_pow, Q_mul, X_pow]

private theorem X_mul_Y : (X : AddMonoidAlgebra R₀ (ℤ × ℤ)) * Y = single ((1 : ℤ), (1 : ℤ)) 1 := by
  rw [X, Y, single_mul_single, one_mul, Prod.mk_add_mk, add_zero, zero_add]

private theorem middle_term (q : R₀) (j n : ℕ) :
    (Q q - 1) * (X * Y) * ((Q q * X) ^ j * Y ^ n) =
      ((q - 1) * q ^ j) • single (((j + 1 : ℕ) : ℤ), ((n + 1 : ℕ) : ℤ)) (1 : R₀) := by
  rw [QX_pow, Y_pow, X_mul_Y, Q_sub_one, Q_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    single_mul_single, single_mul_single, one_mul, one_mul, Prod.mk_add_mk, Prod.mk_add_mk]
  push_cast
  ring_nf

private theorem geom_zero (q : R₀) : geom q 0 = 0 := by simp [geom]

private theorem geom_succ (q : R₀) (n : ℕ) : geom q (n + 1) = Q q * X * geom q n + Y ^ n := by
  unfold geom
  rw [Finset.sum_range_succ', pow_zero, one_mul, Finset.mul_sum, show n + 1 - 1 - 0 = n by omega]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show n + 1 - 1 - (j + 1) = n - 1 - j by omega, pow_succ]
  ring

private theorem sat_succ_eq (q : R₀) (m : ℕ) :
    sat q (m + 1) = (Q q * X) ^ (m + 1) + Y ^ (m + 1) + (Q q - 1) * (X * Y) * geom q m := by
  unfold sat geom
  rw [Finset.sum_range_succ, Finset.sum_range_succ', Finset.mul_sum, satCoeff_zero_left,
    satCoeff_self q (m := m + 1) (by omega), Nat.sub_self, Nat.sub_zero, Nat.cast_zero, one_smul, ← Y_pow, ← QX_pow]
  have hmid : ∀ j ∈ Finset.range m,
      satCoeff q (m + 1) (j + 1) • single (((j + 1 : ℕ) : ℤ), ((m + 1 - (j + 1) : ℕ) : ℤ)) (1 : R₀) =
        (Q q - 1) * (X * Y) * ((Q q * X) ^ j * Y ^ (m - 1 - j)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [middle_term, satCoeff_of_lt q (m := m + 1) (k := j + 1) (by omega) (by omega), Nat.add_sub_cancel,
      show m + 1 - (j + 1) = m - 1 - j + 1 by omega]
  rw [Finset.sum_congr rfl hmid]
  ring

end ClosedForm

section Values

open LocalGL2 HeckePair AddMonoidAlgebra

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
  {R₀ : Type*} [CommRing R₀]
  (hfin : ∀ g : GL (Fin 2) K,
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)

private def central : GL (Fin 2) K := diagPi ϖ hϖ0 * localRepInf ϖ hϖ0

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in
private theorem coe_central :
    (central ϖ hϖ0 : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [central, Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in
private theorem central_mul_comm (x : GL (Fin 2) K) : central ϖ hϖ0 * x = x * central ϖ hϖ0 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_central, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in
private theorem central_zpow_mul_comm (a : ℤ) (x : GL (Fin 2) K) : central ϖ hϖ0 ^ a * x = x * central ϖ hϖ0 ^ a :=
  ((show Commute (central ϖ hϖ0) x from central_mul_comm ϖ hϖ0 x).zpow_left a).eq

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in
private theorem diagPi_comm_localRepInf : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in

private theorem heckeIndicator_localRepInf (h₁ h₂) :
    (heckeIndicator R₀ (localRepInf ϖ hϖ0) h₁ : HeckeAlgebra (integralSubgroup R K) R₀) =
      heckeIndicator R₀ (diagPi ϖ hϖ0) h₂ :=
  heckeIndicator_mul_mul weylInt_mem weylInt_mem (diagPi ϖ hϖ0) h₁ h₂

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in
private theorem diagPi_zpow_mul_localRepInf_zpow (a : ℤ) (m : ℕ) :
    diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ (a + m) = central ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ m := by
  rw [central, (diagPi_comm_localRepInf ϖ hϖ0).mul_zpow, zpow_add, zpow_natCast, mul_assoc]

variable (S : HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ))
  (hST : S (heckeIndicator R₀ (diagPi ϖ hϖ0) (hfin _)) =
    (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) • single ((1 : ℤ), (0 : ℤ)) 1 + single ((0 : ℤ), (1 : ℤ)) 1)
  (hSc : S (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) (hfin _)) = single ((1 : ℤ), (1 : ℤ)) 1)

include hfin hSc in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in
private theorem S_central_pow (n : ℕ) :
    S (heckeIndicator R₀ (central ϖ hϖ0 ^ n) (hfin _)) = single ((n : ℤ), (n : ℤ)) 1 := by
  induction n with
  | zero => rw [pow_zero, heckeIndicator_one, map_one, Nat.cast_zero, single_zero_zero]
  | succ n ih =>
      rw [pow_succ', ← heckeIndicator_central_mul (central_mul_comm ϖ hϖ0) _ (hfin _) (hfin _), map_mul, ih]
      rw [central, hSc, single_mul_single, one_mul, Prod.mk_add_mk]
      push_cast
      ring_nf

include hfin hSc in
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Finite (R ⧸ Ideal.span {ϖ})] in
private theorem S_central_zpow (a : ℤ) :
    S (heckeIndicator R₀ (central ϖ hϖ0 ^ a) (hfin _)) = single (a, a) 1 := by
  obtain ⟨n, rfl | rfl⟩ := a.eq_nat_or_neg
  · rw [zpow_natCast]
    exact S_central_pow ϖ hϖ0 hfin S hSc n
  · have hone : S (heckeIndicator R₀ (central ϖ hϖ0 ^ (-(n : ℤ))) (hfin _)) * single ((n : ℤ), (n : ℤ)) 1 = 1 := by
      rw [← S_central_pow ϖ hϖ0 hfin S hSc n, ← map_mul, ← zpow_natCast,
        heckeIndicator_central_mul (central_zpow_mul_comm ϖ hϖ0 _) _ (hfin _) (hfin _) (hfin _), ← zpow_add,
        neg_add_cancel, zpow_zero, heckeIndicator_one, map_one]
    have hunit : (single ((n : ℤ), (n : ℤ)) (1 : R₀) : AddMonoidAlgebra R₀ (ℤ × ℤ)) *
        single (-(n : ℤ), -(n : ℤ)) 1 = 1 := by
      rw [single_mul_single, one_mul, Prod.mk_add_mk, add_neg_cancel, single_zero_zero]
    calc S (heckeIndicator R₀ (central ϖ hϖ0 ^ (-(n : ℤ))) (hfin _))
        = S (heckeIndicator R₀ (central ϖ hϖ0 ^ (-(n : ℤ))) (hfin _)) *
            (single ((n : ℤ), (n : ℤ)) 1 * single (-(n : ℤ), -(n : ℤ)) 1) := by rw [hunit, mul_one]
      _ = single (-(n : ℤ), -(n : ℤ)) 1 := by rw [← mul_assoc, hone, one_mul]

include hϖ hfin hST hSc in

private theorem S_localRepInf_pow (m : ℕ) :
    S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ m) (hfin _)) = sat (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) m := by
  set q : R₀ := (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) with hq
  have hT : S (heckeIndicator R₀ (diagPi ϖ hϖ0) (hfin _)) = Q q * X + Y := by
    rw [hST, Q_mul, X, Y]
  have hc : S (heckeIndicator R₀ (central ϖ hϖ0) (hfin _)) = X * Y := by
    rw [X_mul_Y]; exact hSc

  have h1 : S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ 1) (hfin _)) = Q q * X + Y := by
    rw [pow_one, heckeIndicator_localRepInf ϖ hϖ0 _ (hfin _), hT]

  have h2 : S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ 2) (hfin _)) =
      (Q q * X + Y) * (Q q * X + Y) - (Q q + 1) * (X * Y) := by
    have hrec := congrArg S (heckeIndicator_diagPi_mul_self ϖ hϖ0 hϖ (R₀ := R₀) (hfin _) (hfin _))
    rw [map_mul, map_add, map_smul, hT,
      show diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = central ϖ hϖ0 from rfl, hc, ← Q_mul, ← Q_add_one] at hrec
    rw [eq_sub_iff_add_eq]
    exact hrec.symm

  have hstep : ∀ k : ℕ, S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 3)) (hfin _)) =
      (Q q * X + Y) * S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 2)) (hfin _)) -
        Q q * (X * Y) * S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 1)) (hfin _)) := by
    intro k
    have hrec := congrArg S
      (heckeIndicator_diagPi_mul_localRepInf_pow ϖ hϖ0 hϖ (R₀ := R₀) k (hfin _) (hfin _) (hfin _))
    rw [map_mul, map_add, map_smul, hT] at hrec
    have hshift : (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ^ (k + 2)) (hfin _) :
        HeckeAlgebra (integralSubgroup R K) R₀) =
          heckeIndicator R₀ (central ϖ hϖ0) (hfin _) * heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (k + 1)) (hfin _) := by
      rw [heckeIndicator_central_mul (central_mul_comm ϖ hϖ0) _ (hfin _) (hfin _) (hfin _), central, mul_assoc,
        ← pow_succ']
    rw [hshift, map_mul, hc, ← Q_mul] at hrec
    rw [eq_sub_iff_add_eq, hrec]
    ring

  have key : ∀ n : ℕ,
      S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (n + 1)) (hfin _)) = sat q (n + 1) ∧
        S (heckeIndicator R₀ (localRepInf ϖ hϖ0 ^ (n + 2)) (hfin _)) = sat q (n + 2) := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [zero_add, h1, sat_succ_eq, geom_zero]; ring
        · rw [zero_add, h2, sat_succ_eq, geom_succ, geom_zero]; ring
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        rw [show n + 1 + 2 = n + 3 by omega, hstep, ih.1, ih.2, sat_succ_eq, sat_succ_eq, sat_succ_eq,
          geom_succ q (n + 1), geom_succ q n]
        ring
  rcases m with _ | n
  · rw [pow_zero, heckeIndicator_one, map_one]
    unfold sat
    rw [Finset.sum_range_one, satCoeff_zero_left, one_smul, Nat.sub_zero, Nat.cast_zero, single_zero_zero]
  · exact (key n).1

include hϖ hfin hST hSc in

private theorem S_basis (a : ℤ) (m : ℕ) :
    S (heckeIndicator R₀ (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ (a + m)) (hfin _)) =
      single (a, a) 1 * sat (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) m := by
  rw [show (heckeIndicator R₀ (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ (a + m)) (hfin _) :
      HeckeAlgebra (integralSubgroup R K) R₀) =
        heckeIndicator R₀ (central ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ m) (hfin _) by
      congr 1; exact diagPi_zpow_mul_localRepInf_zpow ϖ hϖ0 a m,
    ← heckeIndicator_central_mul (central_zpow_mul_comm ϖ hϖ0 a) _ (hfin _) (hfin _), map_mul,
    S_central_zpow ϖ hϖ0 hfin S hSc, S_localRepInf_pow ϖ hϖ0 hϖ hfin S hST hSc]

include hϖ hfin hST hSc in

private theorem S_basis_of_le {a b : ℤ} (hab : a ≤ b) :
    S (heckeIndicator R₀ (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ b) (hfin _)) =
      single (a, a) 1 * sat (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) (b - a).toNat := by
  have hb : b = a + ((b - a).toNat : ℤ) := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]; ring
  conv_lhs => rw [hb]
  exact S_basis ϖ hϖ0 hϖ hfin S hST hSc a _

end Values

#print axioms heckeIndicator_central_mul
#print axioms sum_satCoeff_range
#print axioms satCoeff_middle
#print axioms sat_apply
#print axioms sat_succ_eq
#print axioms S_localRepInf_pow
#print axioms S_basis
#print axioms S_basis_of_le

end SatakeValues

open NumberField IsDedekindDomain AutomorphicForm
open scoped ENNReal

namespace TorusIndices

section Measure

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

private theorem _root_.TorusIndices.measure_coe_eq_relIndex_mul (μ : Measure G) [μ.IsMulLeftInvariant] {H H' : Subgroup G}
    (hle : H ≤ H') (hfin : H.relIndex H' ≠ 0) (hH : MeasurableSet (H : Set G)) :
    μ (H' : Set G) = (H.relIndex H' : ℝ≥0∞) * μ (H : Set G) := by
  classical
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hfin⟩
  let rep : H' ⧸ H.subgroupOf H' → G := fun q => ((Quotient.out q : H') : G)
  let piece : H' ⧸ H.subgroupOf H' → Set G := fun q => (fun x => (rep q)⁻¹ * x) ⁻¹' (H : Set G)
  have hrep : ∀ q, rep q ∈ H' := fun q => (Quotient.out q : H').2
  have hmk : ∀ (y : H') (q : H' ⧸ H.subgroupOf H'), (y : H' ⧸ H.subgroupOf H') = q ↔ (rep q)⁻¹ * y ∈ H := by
    intro y q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hcover : (H' : Set G) = ⋃ q, piece q := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      exact ⟨(⟨x, hx⟩ : H'), (hmk ⟨x, hx⟩ _).1 rfl⟩
    · rintro ⟨q, hq⟩
      have := H'.mul_mem (hrep q) (hle hq)
      rwa [mul_inv_cancel_left] at this
  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro q₁ q₂ hne
    refine Set.disjoint_left.2 fun x h₁ h₂ => hne ?_
    have hx₁ : (rep q₁)⁻¹ * x ∈ H := h₁
    have hx₂ : (rep q₂)⁻¹ * x ∈ H := h₂
    have hy : (rep q₁)⁻¹ * rep q₂ ∈ H := by
      have := H.mul_mem hx₁ (H.inv_mem hx₂)
      rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
    rw [← QuotientGroup.out_eq' q₂, eq_comm, hmk]
    exact hy
  have hmeas : ∀ q, MeasurableSet (piece q) := fun q => measurable_const_mul _ hH
  have hpiece : ∀ q, μ (piece q) = μ (H : Set G) := fun q => measure_preimage_mul μ _ _
  rw [hcover, measure_iUnion hdisj hmeas]
  simp only [hpiece, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  rfl

p2m_export "TorusIndices" "measure_coe_eq_relIndex_mul"
end Measure

section Transitive

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq Module"
open scoped Matrix

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem _root_.TorusIndices.act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g v) = v := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

p2m_export "TorusIndices" "act_inv_act"
private theorem _root_.TorusIndices.act_act_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g (Vertex.act g⁻¹ v) = v := by
  rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

p2m_export "TorusIndices" "act_act_inv"

private theorem act_eq_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) (x y : Vertex R K) :
    Vertex.act g x = y ↔ x = Vertex.act g⁻¹ y :=
  ⟨fun h => by rw [← h, act_inv_act], fun h => by rw [h, act_act_inv]⟩

variable (R K) in

private theorem isTorsionFree_of_isFractionRing [IsDomain R] [IsFractionRing R K] : Module.IsTorsionFree R K :=
  Module.isTorsionFree_iff_smul_eq_zero.2 fun r x h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h0 => (map_eq_zero_iff _ (IsFractionRing.injective R K)).1 h0) id

private theorem exists_latticeMap_stdLattice_eq [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, latticeMap g (stdLattice R K) = L := by
  classical
  haveI : Module.IsTorsionFree R K := isTorsionFree_of_isFractionRing R K
  haveI : Submodule.IsLattice K L := ⟨hL.1, hL.2⟩
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R L) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Submodule.IsLattice.finrank_of_pi K L, Fintype.card_fin]
  let b : Basis (Fin 2) R L := (Module.Free.chooseBasis R L).reindex (Fintype.equivFinOfCardEq hcard)
  let bK : Basis (Fin 2) K (Fin 2 → K) := b.extendOfIsLattice K
  let e : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  refine ⟨⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK, bK.toMatrix_mul_toMatrix_flip e⟩,
    ?_⟩
  have hcol : ∀ j : Fin 2, (e.toMatrix bK) *ᵥ (Pi.single j 1 : Fin 2 → K) = (b j : Fin 2 → K) := by
    intro j
    ext i
    rw [Matrix.mulVec_single_one]
    change e.toMatrix bK i j = _
    simp only [e, bK, Basis.toMatrix_apply, Pi.basisFun_repr, Basis.extendOfIsLattice_apply]
  have himg : (mulVecLinR (R := R) (⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK,
      bK.toMatrix_mul_toMatrix_flip e⟩ : Matrix.GeneralLinearGroup (Fin 2) K)) ''
        Set.range (fun j : Fin 2 => (Pi.single j 1 : Fin 2 → K)) =
      L.subtype '' Set.range b := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext j
    exact hcol j
  rw [latticeMap, stdLattice_eq_span, Submodule.map_span, himg, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

private theorem exists_act_stdVertex_eq [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] (x : Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = x := by
  induction x using Quotient.inductionOn with
  | h L =>
    obtain ⟨g, hg⟩ := exists_latticeMap_stdLattice_eq L.2
    refine ⟨g, ?_⟩
    change Vertex.mk R K (latticeMap g (stdLattice R K)) _ = Vertex.mk R K L.1 L.2
    rw [Vertex.mk_eq_mk_iff, hg]
    exact Homothetic.refl L.1

end Transitive

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem coe_map_apply {A F : Type} [CommRing A] [CommRing F] (φ : A →+* F) (y : GL (Fin 2) A) :
    ((Matrix.GeneralLinearGroup.map φ y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) A).map φ := rfl

private theorem integralUnitsSet_eq_integralSubgroup (F : Type) [Field F] (O : ValuationSubring F) :
    integralUnitsSet (O : Set F) = (LocalGL2.integralSubgroup O F : Set (GL (Fin 2) F)) := by
  ext g
  rw [mem_integralUnitsSet, SetLike.mem_coe, LocalGL2.mem_integralSubgroup_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hinj : Function.Injective (algebraMap O F) := Subtype.val_injective
    let A : Matrix (Fin 2) (Fin 2) O := fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) F) i j, h₁ i j⟩
    let B : Matrix (Fin 2) (Fin 2) O :=
      fun i j => ⟨((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j, h₂ i j⟩
    have hA : A.map (algebraMap O F) = (g : Matrix (Fin 2) (Fin 2) F) := by ext i j; rfl
    have hB : B.map (algebraMap O F) = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; rfl
    have hAB : A * B = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hA, hB, Matrix.map_one (algebraMap O F) (map_zero _) (map_one _)]
      exact g.mul_inv
    have hBA : B * A = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hB, hA, Matrix.map_one (algebraMap O F) (map_zero _) (map_one _)]
      exact g.inv_mul
    refine ⟨⟨A, B, hAB, hBA⟩, Units.ext ?_⟩
    rw [coe_map_apply]
    exact hA
  · rintro ⟨y, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [coe_map_apply]
      exact (y i j).2
    · rw [← map_inv, coe_map_apply]
      exact (y⁻¹ i j).2

private theorem coe_integralSubgroup :
    ((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) =
      localIntegralSet K v := by
  unfold localIntegralSet
  exact (integralUnitsSet_eq_integralSubgroup (v.adicCompletion K) (v.adicCompletionIntegers K)).symm

private theorem mem_integralSubgroup_iff_mem_localIntegralSet (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) ↔
      g ∈ localIntegralSet K v := by
  rw [← SetLike.mem_coe, coe_integralSubgroup]

private theorem det_map (y : GL (Fin 2) (v.adicCompletionIntegers K)) :
    Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) y) =
      Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom
        (Matrix.GeneralLinearGroup.det y) := by
  ext : 1
  change Matrix.det ((y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map _) =
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (Matrix.det _)
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

private theorem exists_det_eq_of_mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)}
    (hg : g ∈ localIntegralSet K v) :
    ∃ w : (v.adicCompletionIntegers K)ˣ,
      Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w := by
  obtain ⟨y, rfl⟩ := (mem_integralSubgroup_iff_mem_localIntegralSet K v g).2 hg
  exact ⟨Matrix.GeneralLinearGroup.det y, congrArg Units.val (det_map K v y)⟩

private theorem det_conj (s t : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.det (s⁻¹ * t * s) = Matrix.GeneralLinearGroup.det t := by
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]

private theorem det_coe_conj (s t : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.det ((s⁻¹ * t * s : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  have h1 : Matrix.det ((s⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
      Matrix.det (s : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, h1, one_mul]

variable (γ : GL (Fin 2) (v.adicCompletion K))

private noncomputable def unitCentralizer : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
    Subgroup.comap
      (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
      (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range

private theorem mem_unitCentralizer_iff (t : GL (Fin 2) (v.adicCompletion K)) :
    t ∈ unitCentralizer K v γ ↔
      t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        ∃ w : (v.adicCompletionIntegers K)ˣ,
          Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w := by
  rw [unitCentralizer, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_range]
  refine and_congr Iff.rfl (exists_congr fun w => ?_)
  exact ⟨fun h => (congrArg Units.val h).symm, fun h => Units.ext h.symm⟩

private noncomputable def conjStabilizer (s : GL (Fin 2) (v.adicCompletion K)) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
    (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)).map
      (MulAut.conj s).toMonoidHom

private theorem mem_conjStabilizer_iff (s t : GL (Fin 2) (v.adicCompletion K)) :
    t ∈ conjStabilizer K v γ s ↔
      t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        s⁻¹ * t * s ∈ localIntegralSet K v := by
  rw [conjStabilizer, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    mem_integralSubgroup_iff_mem_localIntegralSet]

private theorem conjStabilizer_le_unitCentralizer (s : GL (Fin 2) (v.adicCompletion K)) :
    conjStabilizer K v γ s ≤ unitCentralizer K v γ := by
  intro t ht
  rw [mem_conjStabilizer_iff] at ht
  rw [mem_unitCentralizer_iff]
  refine ⟨ht.1, ?_⟩
  obtain ⟨w, hw⟩ := exists_det_eq_of_mem_localIntegralSet K v ht.2
  exact ⟨w, (det_coe_conj K v s t).symm.trans hw⟩

private theorem coe_conjStabilizer (s : GL (Fin 2) (v.adicCompletion K)) :
    (conjStabilizer K v γ s : Set (GL (Fin 2) (v.adicCompletion K))) =
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) :
          Set (GL (Fin 2) (v.adicCompletion K))) ∩
        (fun u => s * u * s⁻¹) '' localIntegralSet K v := by
  rw [conjStabilizer, Subgroup.coe_inf, Subgroup.coe_map, coe_integralSubgroup]
  rfl

private theorem isClosed_centralizer :
    IsClosed (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) :
      Set (GL (Fin 2) (v.adicCompletion K))) := by
  have : (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) :
      Set (GL (Fin 2) (v.adicCompletion K))) = {t | γ * t = t * γ} := by
    ext t
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
      Set.mem_setOf_eq]
  rw [this]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

private theorem isCompact_conjStabilizer (s : GL (Fin 2) (v.adicCompletion K)) :
    IsCompact (conjStabilizer K v γ s : Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [coe_conjStabilizer]
  exact ((isCompact_localIntegralSet K v).image
    ((continuous_const.mul continuous_id).mul continuous_const)).inter_left (isClosed_centralizer K v γ)

private theorem measure_unitCentralizer_eq [MeasurableSpace (GL (Fin 2) (v.adicCompletion K))]
    [MeasurableMul (GL (Fin 2) (v.adicCompletion K))] (μ : MeasureTheory.Measure (GL (Fin 2) (v.adicCompletion K)))
    [μ.IsMulLeftInvariant] (s : GL (Fin 2) (v.adicCompletion K))
    (hfin : (conjStabilizer K v γ s).relIndex (unitCentralizer K v γ) ≠ 0)
    (hmeas : MeasurableSet (conjStabilizer K v γ s : Set (GL (Fin 2) (v.adicCompletion K)))) :
    μ (unitCentralizer K v γ : Set (GL (Fin 2) (v.adicCompletion K))) =
      ((conjStabilizer K v γ s).relIndex (unitCentralizer K v γ) : ℝ≥0∞) *
        μ (conjStabilizer K v γ s : Set (GL (Fin 2) (v.adicCompletion K))) :=
  measure_coe_eq_relIndex_mul μ (conjStabilizer_le_unitCentralizer K v γ s) hfin hmeas

private theorem unitCentralizer_le_centralizer :
    unitCentralizer K v γ ≤ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) :=
  fun _ ht => ((mem_unitCentralizer_iff K v γ _).1 ht).1

private theorem measure_unitCentralizer_subgroupOf_eq
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))]
    [MeasurableMul (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))]
    (μ : MeasureTheory.Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))
    [μ.IsMulLeftInvariant] (s : GL (Fin 2) (v.adicCompletion K))
    (hfin : (conjStabilizer K v γ s).relIndex (unitCentralizer K v γ) ≠ 0)
    (hmeas : MeasurableSet
      ((conjStabilizer K v γ s).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))) :
    μ ((unitCentralizer K v γ).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))) =
      ((conjStabilizer K v γ s).relIndex (unitCentralizer K v γ) : ℝ≥0∞) *
        μ ((conjStabilizer K v γ s).subgroupOf
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
          Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))) := by
  have hTc := unitCentralizer_le_centralizer K v γ
  have hle : (conjStabilizer K v γ s).subgroupOf
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≤
        (unitCentralizer K v γ).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :=
    fun _ hx => Subgroup.mem_subgroupOf.2
      (conjStabilizer_le_unitCentralizer K v γ s (Subgroup.mem_subgroupOf.1 hx))
  rw [measure_coe_eq_relIndex_mul μ hle (by rwa [Subgroup.relIndex_subgroupOf hTc]) hmeas,
    Subgroup.relIndex_subgroupOf hTc]

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq"

private theorem algebraMap_self_mem (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := x.2

private theorem scalarGL_mem_integralSubgroup_of_sq {c : (v.adicCompletion K)ˣ} {u : (v.adicCompletionIntegers K)ˣ}
    (hc : (c : v.adicCompletion K) ^ 2 = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u) :
    scalarGL c ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  have hc0 : (c : v.adicCompletion K) ≠ 0 := c.ne_zero
  have hu : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (u⁻¹ : (v.adicCompletionIntegers K)ˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : (c : v.adicCompletion K)⁻¹ =
      (c : v.adicCompletion K) * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (u⁻¹ : (v.adicCompletionIntegers K)ˣ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← sq, hc, hu]
  have hself : (c : v.adicCompletion K) = (c : v.adicCompletion K)⁻¹ *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u := by
    rw [← hc, sq, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hmem : (c : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      (c : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
    rcases (v.adicCompletionIntegers K).mem_or_inv_mem (c : v.adicCompletion K) with h | h
    · refine ⟨h, ?_⟩
      rw [hinv]
      exact mul_mem h (algebraMap_self_mem K v _)
    · refine ⟨?_, h⟩
      rw [hself]
      exact mul_mem h (algebraMap_self_mem K v _)
  let c₀ : (v.adicCompletionIntegers K)ˣ :=
    ⟨⟨c, hmem.1⟩, ⟨(c : v.adicCompletion K)⁻¹, hmem.2⟩, Subtype.ext (mul_inv_cancel₀ hc0),
      Subtype.ext (inv_mul_cancel₀ hc0)⟩
  rw [LocalGL2.mem_integralSubgroup_iff]
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) c₀, Units.ext ?_⟩
  rw [coe_map_apply]
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.one_apply, c₀]
  split_ifs <;> simp

private theorem mem_integralSubgroup_of_scalarGL_mul {m : GL (Fin 2) (v.adicCompletion K)}
    {w : (v.adicCompletionIntegers K)ˣ}
    (hm : Matrix.det (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w)
    {c : (v.adicCompletion K)ˣ}
    (hc : scalarGL c * m ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) :
    m ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  obtain ⟨w', hw'⟩ := exists_det_eq_of_mem_localIntegralSet K v
    ((mem_integralSubgroup_iff_mem_localIntegralSet K v _).1 hc)
  have hdet : Matrix.det ((scalarGL c * m : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = (c : v.adicCompletion K) ^ 2 *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w := by
    rw [Units.val_mul, Matrix.det_mul, scalarGL_coe, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
      mul_one, hm]
  have hsq : (c : v.adicCompletion K) ^ 2 =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (w' * w⁻¹ : (v.adicCompletionIntegers K)ˣ) := by
    rw [Units.val_mul, map_mul, ← hw', hdet, mul_assoc, ← map_mul]
    rw [show ((w : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) *
      ((w⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) = 1 from Units.mul_inv w, map_one,
      mul_one]
  have hs := scalarGL_mem_integralSubgroup_of_sq K v hsq
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hc
  rwa [inv_mul_cancel_left] at this

private theorem mem_conjStabilizer_iff_act_eq {t : GL (Fin 2) (v.adicCompletion K)} (ht : t ∈ unitCentralizer K v γ)
    (s : GL (Fin 2) (v.adicCompletion K)) :
    t ∈ conjStabilizer K v γ s ↔
      Vertex.act t (Vertex.act s (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K))) =
        Vertex.act s (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
  obtain ⟨hT, w, hw⟩ := (mem_unitCentralizer_iff K v γ t).1 ht
  have hdet : Matrix.det ((s⁻¹ * t * s : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w :=
    (det_coe_conj K v s t).trans hw
  have hact : Vertex.act t (Vertex.act s (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K))) =
      Vertex.act s (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K)) ↔
        Vertex.act (s⁻¹ * t * s) (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K)) =
          stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K) := by
    rw [Vertex.act_mul, Vertex.act_mul, act_eq_iff s⁻¹, inv_inv]
  rw [mem_conjStabilizer_iff, hact, Vertex.act_stdVertex_eq_iff, ← mem_integralSubgroup_iff_mem_localIntegralSet]
  constructor
  · rintro ⟨-, hm⟩
    exact ⟨1, by rw [scalarGL_one, one_mul]; exact hm⟩
  · rintro ⟨c, hc⟩
    exact ⟨hT, mem_integralSubgroup_of_scalarGL_mul K v hdet hc⟩

private theorem relIndex_conjStabilizer_ne_zero_of_stable {F : Set (Vertex (v.adicCompletionIntegers K) (v.adicCompletion K))}
    (hF : F.Finite) (hne : F.Nonempty)
    (hstab : ∀ t ∈ unitCentralizer K v γ, ∀ x ∈ F, Vertex.act t x ∈ F) (s : GL (Fin 2) (v.adicCompletion K)) :
    (conjStabilizer K v γ s).relIndex (unitCentralizer K v γ) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨g₀, rfl⟩ := exists_act_stdVertex_eq x₀

  have h₁ : (conjStabilizer K v γ g₀).relIndex (unitCentralizer K v γ) ≠ 0 := by
    letI : MulAction (GL (Fin 2) (v.adicCompletion K))
        (Vertex (v.adicCompletionIntegers K) (v.adicCompletion K)) :=
      { smul := Vertex.act
        one_smul := Vertex.act_one
        mul_smul := Vertex.act_mul }
    set x₀ := Vertex.act g₀ (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K))
    have horbit : MulAction.orbit (unitCentralizer K v γ) x₀ ⊆ F := by
      rintro _ ⟨t, rfl⟩
      change Vertex.act (t : GL (Fin 2) (v.adicCompletion K)) x₀ ∈ F
      exact hstab t t.2 x₀ hx₀
    have hidx : (MulAction.stabilizer (unitCentralizer K v γ) x₀).index ≠ 0 := by
      rw [MulAction.index_stabilizer]
      exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self x₀) (hF.subset horbit)
    have hstab' : MulAction.stabilizer (unitCentralizer K v γ) x₀ =
        (conjStabilizer K v γ g₀).subgroupOf (unitCentralizer K v γ) := by
      ext t
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_conjStabilizer_iff_act_eq K v γ t.2]
      exact Iff.rfl
    rw [hstab'] at hidx
    exact hidx

  have h₂ : (conjStabilizer K v γ s).relIndex (conjStabilizer K v γ g₀) ≠ 0 := by
    haveI : CompactSpace (conjStabilizer K v γ g₀) :=
      isCompact_iff_compactSpace.1 (isCompact_conjStabilizer K v γ g₀)
    have hopen : IsOpen (((conjStabilizer K v γ s).subgroupOf (conjStabilizer K v γ g₀) :
        Subgroup (conjStabilizer K v γ g₀)) : Set (conjStabilizer K v γ g₀)) := by
      have hset : (((conjStabilizer K v γ s).subgroupOf (conjStabilizer K v γ g₀) :
          Subgroup (conjStabilizer K v γ g₀)) : Set (conjStabilizer K v γ g₀)) =
            (fun t : conjStabilizer K v γ g₀ => s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s) ⁻¹'
              localIntegralSet K v := by
        ext t
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjStabilizer_iff, Set.mem_preimage]
        exact ⟨fun h => h.2, fun h => ⟨((mem_conjStabilizer_iff K v γ g₀ _).1 t.2).1, h⟩⟩
      rw [hset]
      exact (isOpen_localIntegralSet K v).preimage
        ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    haveI := Subgroup.quotient_finite_of_isOpen _ hopen
    show ((conjStabilizer K v γ s).subgroupOf (conjStabilizer K v γ g₀)).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_ne_zero_trans (hHK := h₂) (hKL := h₁)

private theorem relIndex_conjStabilizer_ne_zero (hfix : unitOrbitalCount (v.adicCompletionIntegers K) γ ≠ 0)
    (s : GL (Fin 2) (v.adicCompletion K)) :
    (conjStabilizer K v γ s).relIndex (unitCentralizer K v γ) ≠ 0 := by
  have hfix' : Nat.card (fixedVertexSet (R := v.adicCompletionIntegers K) γ) ≠ 0 := hfix
  obtain ⟨⟨⟨x₀, hx₀⟩⟩, hfin⟩ := Nat.card_ne_zero.1 hfix'
  haveI := hfin
  refine relIndex_conjStabilizer_ne_zero_of_stable K v γ (Set.toFinite _) ⟨x₀, hx₀⟩ ?_ s
  intro t ht x hx
  have hcomm : γ * t = t * γ := (Subgroup.mem_centralizer_iff.1 (unitCentralizer_le_centralizer K v γ ht)) γ rfl
  rw [mem_fixedVertexSet] at hx ⊢
  rw [← Vertex.act_mul, hcomm, Vertex.act_mul, hx]

#print axioms exists_act_stdVertex_eq
#print axioms mem_conjStabilizer_iff_act_eq
#print axioms relIndex_conjStabilizer_ne_zero_of_stable
#print axioms relIndex_conjStabilizer_ne_zero

#print axioms measure_coe_eq_relIndex_mul
#print axioms conjStabilizer_le_unitCentralizer
#print axioms mem_unitCentralizer_iff
#print axioms mem_conjStabilizer_iff
#print axioms isCompact_conjStabilizer
#print axioms measure_unitCentralizer_eq
#print axioms measure_unitCentralizer_subgroupOf_eq

end Local

end TorusIndices

namespace TwistedTreeTransport

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem galAct_act (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.galAct σ (Vertex.act g v) = Vertex.act (σ.mapGL g) (Vertex.galAct σ v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeGal_latticeMap σ g L.1))

private theorem twistedAct_twistedAct (δ δ' : Matrix.GeneralLinearGroup (Fin 2) K) (σ τ : IntegralAut R K)
    (v : Vertex R K) :
    Vertex.twistedAct δ σ (Vertex.twistedAct δ' τ v) = Vertex.twistedAct (δ * σ.mapGL δ') (σ.comp τ) v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (twistedLatticeMap_twistedLatticeMap δ δ' σ τ L.1))

private theorem _root_.TwistedTreeTransport.act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g v) = v := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

p2m_export "TwistedTreeTransport" "act_inv_act"
private theorem act_act_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g (Vertex.act g⁻¹ v) = v := by
  rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

private theorem act_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (Vertex.act (R := R) g) := fun v w hvw => by
  have h := congrArg (Vertex.act g⁻¹) hvw
  rwa [act_inv_act, act_inv_act] at h

private theorem twistedAct_twistedConj (δ g : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (v : Vertex R K) :
    Vertex.twistedAct (g⁻¹ * δ * σ.mapGL g) σ v = Vertex.act g⁻¹ (Vertex.twistedAct δ σ (Vertex.act g v)) := by
  unfold Vertex.twistedAct
  rw [galAct_act, Vertex.act_mul, Vertex.act_mul]

private theorem twistedFixedVertexSet_twistedConj (δ g : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    twistedFixedVertexSet (g⁻¹ * δ * σ.mapGL g) σ = Vertex.act g⁻¹ '' twistedFixedVertexSet δ σ := by
  ext v
  rw [mem_twistedFixedVertexSet, twistedAct_twistedConj]
  constructor
  · intro hv
    refine ⟨Vertex.act g v, ?_, act_inv_act g v⟩
    rw [mem_twistedFixedVertexSet]
    have h := congrArg (Vertex.act g) hv
    rwa [act_act_inv] at h
  · rintro ⟨w, hw, rfl⟩
    rw [mem_twistedFixedVertexSet] at hw
    rw [act_act_inv, hw]

private theorem twistedUnitOrbitalCount_twistedConj (δ g : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    twistedUnitOrbitalCount (g⁻¹ * δ * σ.mapGL g) σ = twistedUnitOrbitalCount δ σ := by
  rw [twistedUnitOrbitalCount, twistedUnitOrbitalCount, twistedFixedVertexSet_twistedConj]
  exact Nat.card_congr (Equiv.Set.image _ _ (act_injective g⁻¹)).symm

private theorem act_scalarGL_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act (scalarGL c * g) v = Vertex.act g v := by
  rw [Vertex.act_mul]
  exact isFixedVertex_scalarGL c _

private theorem fixedVertexSet_scalarGL_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    fixedVertexSet (R := R) (scalarGL c * g) = fixedVertexSet (R := R) g := by
  ext v
  rw [mem_fixedVertexSet, mem_fixedVertexSet, act_scalarGL_mul]

private theorem unitOrbitalCount_scalarGL_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    unitOrbitalCount R (scalarGL c * g) = unitOrbitalCount R g := by
  rw [unitOrbitalCount, unitOrbitalCount, fixedVertexSet_scalarGL_mul]

private theorem twistedFixedVertexSet_scalarGL_mul (c : Kˣ) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : twistedFixedVertexSet (scalarGL c * δ) σ = twistedFixedVertexSet δ σ := by
  ext v
  rw [mem_twistedFixedVertexSet, mem_twistedFixedVertexSet]
  unfold Vertex.twistedAct
  rw [act_scalarGL_mul]

private theorem twistedUnitOrbitalCount_scalarGL_mul (c : Kˣ) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : twistedUnitOrbitalCount (scalarGL c * δ) σ = twistedUnitOrbitalCount δ σ := by
  rw [twistedUnitOrbitalCount, twistedUnitOrbitalCount, twistedFixedVertexSet_scalarGL_mul]

private def autPow (σ : IntegralAut R K) : ℕ → IntegralAut R K
  | 0 => IntegralAut.refl R K
  | r + 1 => σ.comp (autPow σ r)

private theorem autPow_toField_apply (σ : IntegralAut R K) (r : ℕ) (x : K) :
    (autPow σ r).toField x = (⇑σ.toField)^[r] x := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', ← ih]
      rfl

private theorem twistedAct_iterate (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) (r : ℕ)
    (v : Vertex R K) :
    (Vertex.twistedAct δ σ)^[r] v =
      Vertex.twistedAct (LT.TwistedNorm.sigmaPartialNorm σ.mapGL δ r) (autPow σ r) v := by
  induction r with
  | zero =>
      rw [Function.iterate_zero_apply, LT.TwistedNorm.sigmaPartialNorm_zero]
      unfold Vertex.twistedAct
      rw [autPow, Vertex.galAct_refl, Vertex.act_one]
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, twistedAct_twistedAct, LT.TwistedNorm.sigmaPartialNorm_succ']
      rfl

private theorem latticeGal_eq_self_of_forall (τ : IntegralAut R K) (hτ : ∀ x : K, τ.toField x = x)
    (L : Submodule R (Fin 2 → K)) : latticeGal τ L = L := by
  have hvec : ∀ u : Fin 2 → K, galVec τ u = u := fun u => funext fun i => by rw [galVec_apply, hτ]
  ext u
  rw [mem_latticeGal]
  constructor
  · rintro ⟨u', hu', rfl⟩
    rwa [hvec]
  · intro hu
    exact ⟨u, hu, hvec u⟩

private theorem galAct_eq_self_of_forall (τ : IntegralAut R K) (hτ : ∀ x : K, τ.toField x = x) (v : Vertex R K) :
    Vertex.galAct τ v = v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeGal_eq_self_of_forall τ hτ L.1))

private theorem twistedAct_iterate_eq_act_sigmaNormPow (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (n : ℕ) (hσ : ∀ x : K, (⇑σ.toField)^[n] x = x) (v : Vertex R K) :
    (Vertex.twistedAct δ σ)^[n] v = Vertex.act (LT.TwistedNorm.sigmaNormPow σ.mapGL n δ) v := by
  rw [twistedAct_iterate, LT.TwistedNorm.sigmaNormPow_def]
  unfold Vertex.twistedAct
  rw [galAct_eq_self_of_forall (autPow σ n) fun x => by rw [autPow_toField_apply, hσ]]

end TwistedTreeTransport

namespace QuadraticIrreducibility

open Polynomial

section Generic

variable {F : Type} [Field F] [NeZero (2 : F)]

private theorem exists_root_iff_isSquare (t d : F) : (∃ x : F, x * x - t * x + d = 0) ↔ IsSquare (t ^ 2 - 4 * d) := by
  have hdisc : discrim (1 : F) (-t) d = t ^ 2 - 4 * d := by rw [discrim]; ring
  constructor
  · rintro ⟨x, hx⟩
    have h : (1 : F) * (x * x) + -t * x + d = 0 := by linear_combination hx
    refine ⟨(2 * 1 * x + -t), ?_⟩
    rw [← hdisc, discrim_eq_sq_of_quadratic_eq_zero h, sq]
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (one_ne_zero : (1 : F) ≠ 0) ⟨s, by rw [hdisc, hs]⟩
    exact ⟨x, by linear_combination hx⟩

private theorem irreducible_charpoly_iff_not_isSquare (M : Matrix (Fin 2) (Fin 2) F) :
    Irreducible M.charpoly ↔ ¬ IsSquare (M.trace ^ 2 - 4 * M.det) := by
  have hdeg : M.charpoly.natDegree = 2 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg]) (by rw [hdeg]; norm_num),
    ← exists_root_iff_isSquare, Multiset.eq_zero_iff_forall_notMem]
  have hne : M.charpoly ≠ 0 := Matrix.charpoly_monic M |>.ne_zero
  have hroot : ∀ x : F, M.charpoly.IsRoot x ↔ x * x - M.trace * x + M.det = 0 := by
    intro x
    rw [Matrix.charpoly_fin_two, Polynomial.IsRoot.def]
    simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X]
    constructor <;> intro h <;> linear_combination h
  constructor
  · intro h ⟨x, hx⟩
    exact h x ((Polynomial.mem_roots hne).2 ((hroot x).2 hx))
  · intro h x hx
    exact h ⟨x, (hroot x).1 ((Polynomial.mem_roots hne).1 hx)⟩

end Generic

section Completion

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem irreducible_charpoly_iff (γ : GL (Fin 2) (v.adicCompletion K)) :
    Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ↔
      ¬ IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : NeZero (2 : v.adicCompletion K) := ⟨by norm_num⟩
  exact irreducible_charpoly_iff_not_isSquare _

end Completion

end QuadraticIrreducibility

namespace FixedOrInversion

open NumberField IsDedekindDomain
open scoped Matrix

section Valuation

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem _root_.FixedOrInversion.valued_coe_unit (x : (u.adicCompletionIntegers F)ˣ) :
    Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) = 1 := by
  have hmul : ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
      ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) = 1 :=
    congrArg Subtype.val (Units.mul_inv x)
  have hx : Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) ≤ 1 := by
    have h := (x : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hxi : Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
      u.adicCompletion F) ≤ 1 := by
    have h := ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  refine le_antisymm hx ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F)) := by rw [hmul, map_one]
    _ = Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
          u.adicCompletion F) := map_mul _ _ _
    _ ≤ Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) := mul_le_of_le_one_right' hxi

p2m_export "FixedOrInversion" "valued_coe_unit"

private theorem _root_.FixedOrInversion.valued_coe_eq_of_irreducible {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : u.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer F u
  have hspan : Ideal.span {ϖ} = Ideal.span {π} :=
    hϖ.maximalIdeal_eq.symm.trans (HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer F u hπ)
  obtain ⟨c, hc⟩ := Ideal.span_singleton_eq_span_singleton.1 hspan
  rw [← hπ, ← hc]
  change _ = Valued.v ((ϖ : u.adicCompletion F) * ((c : u.adicCompletionIntegers F) : u.adicCompletion F))
  rw [map_mul, valued_coe_unit F u c, mul_one]

p2m_export "FixedOrInversion" "valued_coe_eq_of_irreducible"

private theorem zpow_exponent_unique {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (w w' : (u.adicCompletionIntegers F)ˣ) (D D' : ℤ)
    (h : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) w *
        algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ^ D =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) w' *
        algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ^ D') : D = D' := by
  have hv := congrArg Valued.v h
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀] at hv
  change Valued.v ((w : u.adicCompletionIntegers F) : u.adicCompletion F) *
      Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ D =
    Valued.v ((w' : u.adicCompletionIntegers F) : u.adicCompletion F) *
      Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ D' at hv
  rw [valued_coe_unit, valued_coe_unit, one_mul, one_mul, valued_coe_eq_of_irreducible F u hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_zpow, WithZero.coe_inj, ← ofAdd_zsmul, ← ofAdd_zsmul, Multiplicative.ofAdd.injective.eq_iff,
    smul_neg, smul_neg, neg_inj, zsmul_one, zsmul_one, Int.cast_inj] at hv
  exact hv

end Valuation

section Tree

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g v) = v := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

private theorem act_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (Vertex.act (R := R) g) := fun v w hvw => by
  have h := congrArg (Vertex.act g⁻¹) hvw
  rwa [act_inv_act, act_inv_act] at h

private theorem act_scalarGL_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act (scalarGL c * g) v = Vertex.act g v := by
  rw [Vertex.act_mul]
  exact isFixedVertex_scalarGL c _

private theorem fixedVertexSet_scalarGL_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    fixedVertexSet (R := R) (scalarGL c * g) = fixedVertexSet (R := R) g := by
  ext v
  rw [mem_fixedVertexSet, mem_fixedVertexSet, act_scalarGL_mul]

private theorem unitOrbitalCount_scalarGL_mul (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    unitOrbitalCount R (scalarGL c * g) = unitOrbitalCount R g := by
  rw [unitOrbitalCount, unitOrbitalCount, fixedVertexSet_scalarGL_mul]

private theorem coe_map_apply (y : Matrix.GeneralLinearGroup (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      (y : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := rfl

private theorem _root_.FixedOrInversion.det_coe_conj (s t : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.det ((s⁻¹ * t * s : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.det (t : Matrix (Fin 2) (Fin 2) K) := by
  have h1 : Matrix.det ((s⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      Matrix.det (s : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, h1, one_mul]

p2m_export "FixedOrInversion" "det_coe_conj"

private theorem eq_scalarGL_mul_of_coe_eq {g h : Matrix.GeneralLinearGroup (Fin 2) K} {c : Kˣ}
    (hgh : (g : Matrix (Fin 2) (Fin 2) K) = (c : K) • (h : Matrix (Fin 2) (Fin 2) K)) : g = scalarGL c * h := by
  apply Units.ext
  rw [Units.val_mul, scalarGL_coe, smul_mul_assoc, one_mul]
  exact hgh

private theorem unitOrbitalCount_eq_of_conj_coe_eq_smul (x γ h : Matrix.GeneralLinearGroup (Fin 2) K) {c : Kˣ}
    (hx : ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • (h : Matrix (Fin 2) (Fin 2) K)) :
    unitOrbitalCount R γ = unitOrbitalCount R h := by
  have hconj := unitOrbitalCount_conj (R := R) (x⁻¹ * γ * x) x
  have hγ : x * (x⁻¹ * γ * x) * x⁻¹ = γ := by group
  rw [hγ, eq_scalarGL_mul_of_coe_eq hx, unitOrbitalCount_scalarGL_mul] at hconj
  exact hconj

private theorem isWithin_act {c : Kˣ} {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin 2) K) {v w : Vertex R K}
    (h : Vertex.IsWithin c n v w) : Vertex.IsWithin c n (Vertex.act g v) (Vertex.act g w) := by
  obtain ⟨L, M, hL, hM, rfl, rfl, hLM⟩ := h
  exact ⟨latticeMap g L, latticeMap g M, hL.map g, hM.map g, rfl, rfl, (latticeWithin_latticeMap_iff c n g L M).2 hLM⟩

private theorem exists_swap_of_conj {c : Kˣ} {x g γ : Matrix.GeneralLinearGroup (Fin 2) K} (hγx : γ * x = x * g)
    {x₀ x₁ : Vertex R K} (hadj : Vertex.IsWithin c 1 x₀ x₁) (hne : x₀ ≠ x₁) (h₀ : Vertex.act g x₀ = x₁)
    (h₁ : Vertex.act g x₁ = x₀) :
    ∃ y₀ y₁ : Vertex R K,
      Vertex.IsWithin c 1 y₀ y₁ ∧ y₀ ≠ y₁ ∧ Vertex.act γ y₀ = y₁ ∧ Vertex.act γ y₁ = y₀ :=
  ⟨Vertex.act x x₀, Vertex.act x x₁, isWithin_act x hadj, fun h => hne (act_injective x h),
    by rw [← Vertex.act_mul, hγx, Vertex.act_mul, h₀], by rw [← Vertex.act_mul, hγx, Vertex.act_mul, h₁]⟩

private theorem finite_and_nonempty_fixedVertexSet_of_unitOrbitalCount_ne_zero {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : unitOrbitalCount R g ≠ 0) :
    (fixedVertexSet (R := R) g).Finite ∧ (fixedVertexSet (R := R) g).Nonempty := by
  obtain ⟨⟨⟨y, hy⟩⟩, hfin⟩ := Nat.card_ne_zero.1 hg
  exact ⟨Set.toFinite _, ⟨y, hy⟩⟩

end Tree

section CayleyHamilton

variable {A : Type*} [CommRing A]

private theorem fin_two_mul_self (Y : Matrix (Fin 2) (Fin 2) A) :
    Y * Y = (Y 0 0 + Y 1 1) • Y - (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0) • (1 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem det_smul_sub_smul_one {Y : Matrix (Fin 2) (Fin 2) A} {ϖ w t : A} (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w)
    (htr : Y 0 0 + Y 1 1 = ϖ * t) : (t • Y - w • (1 : Matrix (Fin 2) (Fin 2) A)).det = w * w := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul,
    mul_zero, sub_zero]
  linear_combination (t * t) * hdet - (t * w) * htr

private theorem mul_self_eq_smul {Y : Matrix (Fin 2) (Fin 2) A} {ϖ w t : A} (hdet : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * w)
    (htr : Y 0 0 + Y 1 1 = ϖ * t) : Y * Y = ϖ • (t • Y - w • (1 : Matrix (Fin 2) (Fin 2) A)) := by
  rw [fin_two_mul_self, hdet, htr, smul_sub, mul_smul, mul_smul]

end CayleyHamilton

section Place

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem exists_conj_eq_scalarGL_mul (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D) :
    ∃ (x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) (k : ℤ) (c : (v.adicCompletion K)ˣ),
      (c : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k ∧
      ((∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
          (∀ i j, (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
          (∀ (a : v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})
              (w : Fin 2 → v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}),
            (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) :
              v.adicCompletionIntegers K →+* v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})) *ᵥ w = a • w → w = 0) ∧
          x⁻¹ * γ * x =
            scalarGL c *
              Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ' ∧
          D = 2 * k) ∨
        (∃ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
          (mu : (v.adicCompletionIntegers K)ˣ) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))
          (w : (v.adicCompletionIntegers K)ˣ),
          (∀ i j, (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
            (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
              ϖ ^ d * Y i j) ∧
          Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = ϖ * (w : v.adicCompletionIntegers K) ∧ ϖ ∣ Y 0 0 + Y 1 1 ∧
          x⁻¹ * γ * x =
            scalarGL c *
              Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ' ∧
          D = 2 * k) ∨
        (∃ (e : (v.adicCompletion K)ˣ) (A : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)),
          (x⁻¹ * γ * x) * (x⁻¹ * γ * x) =
            scalarGL e *
              Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) A ∧
          D = 2 * k + 1)) := by
  have hne : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0 :=
    (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero).ne_zero
  obtain ⟨x, k, h⟩ := exists_conj_eq_zpow_smul_of_not_isSquare_discr K v ϖ hϖ γ
    ((QuadraticIrreducibility.irreducible_charpoly_iff K v γ).1 hγ)
  set c₀ : (v.adicCompletion K)ˣ :=
    Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k) (zpow_ne_zero k hne) with hc₀
  refine ⟨x, k, c₀, rfl, ?_⟩
  have hdetx : Matrix.det ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D := by
    rw [det_coe_conj, hdet]

  have hD₂ : ∀ γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K),
      ((x⁻¹ * γ * x : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k) •
          ((Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ' :
            Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) →
        D = 2 * k := by
    intro γ' hx
    apply zpow_exponent_unique K v hϖ u (Matrix.GeneralLinearGroup.det γ') D (2 * k)
    have hdm : ((γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).det =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).det :=
      (RingHom.map_det _ _).symm
    rw [← hdetx, hx, Matrix.det_smul, Fintype.card_fin, coe_map_apply, hdm, two_mul, zpow_add₀ hne,
      Matrix.GeneralLinearGroup.val_det_apply]
    ring
  rcases h with ⟨γ', d, mu, Y, hY, hanis, hx⟩ | ⟨γ', d, mu, Y, w, hY, hdetY, htr, hx⟩ | ⟨Y, w, hdetY, htr, hx⟩
  · exact Or.inl ⟨γ', d, mu, Y, hY, hanis, eq_scalarGL_mul_of_coe_eq (c := c₀) hx, hD₂ γ' hx⟩
  · exact Or.inr (Or.inl ⟨γ', d, mu, Y, w, hY, hdetY, htr, eq_scalarGL_mul_of_coe_eq (c := c₀) hx, hD₂ γ' hx⟩)
  · right; right
    obtain ⟨t, ht⟩ := htr
    have hAunit : IsUnit (t • Y -
        (w : v.adicCompletionIntegers K) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))) := by
      rw [Matrix.isUnit_iff_isUnit_det, det_smul_sub_smul_one hdetY ht, ← Units.val_mul]
      exact Units.isUnit _
    refine ⟨Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k *
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ)
        (mul_ne_zero (mul_ne_zero (zpow_ne_zero k hne) (zpow_ne_zero k hne)) hne), hAunit.unit, ?_, ?_⟩
    · apply eq_scalarGL_mul_of_coe_eq
      rw [Units.val_mul, hx, coe_map_apply, IsUnit.unit_spec, smul_mul_smul_comm, ← Matrix.map_mul,
        mul_self_eq_smul hdetY ht, Units.val_mk0]
      ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
      ring
    · apply zpow_exponent_unique K v hϖ u w D (2 * k + 1)
      rw [← hdetx, hx, Matrix.det_smul, Fintype.card_fin, Matrix.det_fin_two]
      simp only [Matrix.map_apply]
      rw [← map_mul, ← map_mul, ← map_sub, hdetY, map_mul, zpow_add_one₀ hne, two_mul, zpow_add₀ hne]
      ring

private theorem unitOrbitalCount_eq_of_conj_eq_scalarGL_mul {x γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K)}
    {c : (v.adicCompletion K)ˣ} {γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)}
    (hx : x⁻¹ * γ * x =
      scalarGL c * Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ') :
    unitOrbitalCount (v.adicCompletionIntegers K) γ =
      unitOrbitalCount (v.adicCompletionIntegers K)
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ') := by
  refine unitOrbitalCount_eq_of_conj_coe_eq_smul x γ _ (c := c) ?_
  rw [hx, Units.val_mul, scalarGL_coe, smul_mul_assoc, one_mul]

private theorem unitOrbitalCount_ne_zero_or_exists_swap (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D) :
    unitOrbitalCount (v.adicCompletionIntegers K) γ ≠ 0 ∨
      (¬ Even D ∧ ∃ x₀ x₁ : Vertex (v.adicCompletionIntegers K) (v.adicCompletion K),
        Vertex.IsWithin (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          Vertex.act γ x₀ = x₁ ∧ Vertex.act γ x₁ = x₀) := by
  obtain ⟨x, k, c, -, h⟩ := exists_conj_eq_scalarGL_mul K v ϖ hϖ γ hγ D u hdet
  rcases h with ⟨γ', d, mu, Y, hY, hanis, hx, -⟩ | ⟨γ', d, mu, Y, w, hY, hdetY, htr, hx, -⟩ | ⟨e, A, hgg, hD⟩
  · left
    rw [unitOrbitalCount_eq_of_conj_eq_scalarGL_mul K v hx]
    exact unitOrbitalCount_ne_zero_of_anisotropic (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ hϖ d γ' mu Y hY
      hanis
  · left
    rw [unitOrbitalCount_eq_of_conj_eq_scalarGL_mul K v hx]
    exact unitOrbitalCount_ne_zero_of_eisenstein (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ hϖ d γ' mu Y hY w
      hdetY htr
  · right
    have hodd : ¬ Even D := by
      rw [hD]
      exact Int.not_even_iff_odd.2 ⟨k, rfl⟩
    refine ⟨hodd, ?_⟩
    set g : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K) := x⁻¹ * γ * x with hg
    have hγx : γ * x = x * g := by
      rw [hg]
      group
    have hfix : (Vertex.act g)^[2] (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K) := by
      show Vertex.act g (Vertex.act g (stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K))) =
        stdVertex (v.adicCompletionIntegers K) (v.adicCompletion K)
      rw [← Vertex.act_mul, hgg, act_scalarGL_mul]
      exact isFixedVertex_stdVertex_of_mem_range ⟨A, rfl⟩
    rcases nonempty_fixedVertexSet_or_exists_swap_of_iterate_act (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ hϖ
        g 2 (by norm_num) (Or.inl ⟨_, hfix⟩) with ⟨y, hy⟩ | ⟨x₀, x₁, hadj, hne', h₀, h₁⟩
    · exfalso
      have hdetg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D := by
        rw [hg, det_coe_conj, hdet]
      exact hodd ((even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
        (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ hϖ g D u hdetg).1 y hy)
    · exact exists_swap_of_conj hγx hadj hne' h₀ h₁

private theorem unitOrbitalCount_ne_zero_of_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : Even D) : unitOrbitalCount (v.adicCompletionIntegers K) γ ≠ 0 := by
  rcases unitOrbitalCount_ne_zero_or_exists_swap K v ϖ hϖ γ hγ D u hdet with h | ⟨hodd, -⟩
  · exact h
  · exact absurd hD hodd

private theorem finite_and_nonempty_fixedVertexSet_of_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : Even D) :
    (fixedVertexSet (R := v.adicCompletionIntegers K) γ).Finite ∧
      (fixedVertexSet (R := v.adicCompletionIntegers K) γ).Nonempty :=
  finite_and_nonempty_fixedVertexSet_of_unitOrbitalCount_ne_zero
    (unitOrbitalCount_ne_zero_of_even K v ϖ hϖ γ hγ D u hdet hD)

private theorem exists_swap_of_not_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : ¬ Even D) :
    ∃ x₀ x₁ : Vertex (v.adicCompletionIntegers K) (v.adicCompletion K),
      Vertex.IsWithin (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
        Vertex.act γ x₀ = x₁ ∧ Vertex.act γ x₁ = x₀ := by
  rcases unitOrbitalCount_ne_zero_or_exists_swap K v ϖ hϖ γ hγ D u hdet with h | ⟨-, hswap⟩
  · exfalso
    obtain ⟨-, y, hy⟩ := finite_and_nonempty_fixedVertexSet_of_unitOrbitalCount_ne_zero h
    exact hD ((even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
      (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ hϖ γ D u hdet).1 y hy)
  · exact hswap

end Place

section NormScalars

open LT.TwistedNorm

variable {G : Type*} [Group G]

private theorem sigmaPartialNorm_mul_of_central (σ : G →* G) {s : G} (hs : ∀ g : G, Commute s g) (hσs : σ s = s) (x : G) :
    ∀ r : ℕ, sigmaPartialNorm σ (s * x) r = s ^ r * sigmaPartialNorm σ x r
  | 0 => by rw [sigmaPartialNorm_zero, sigmaPartialNorm_zero, pow_zero, one_mul]
  | r + 1 => by
    rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_mul_of_central σ hs hσs x r, map_mul,
      map_pow, hσs, pow_succ']
    have hc : Commute (s ^ r) x := (hs x).pow_left r
    calc s * x * (s ^ r * σ (sigmaPartialNorm σ x r))
        = s * (x * s ^ r) * σ (sigmaPartialNorm σ x r) := by simp only [mul_assoc]
      _ = s * (s ^ r * x) * σ (sigmaPartialNorm σ x r) := by rw [hc.eq]
      _ = s * s ^ r * (x * σ (sigmaPartialNorm σ x r)) := by simp only [mul_assoc]

private theorem sigmaNormPow_mul_of_central (σ : G →* G) {s : G} (hs : ∀ g : G, Commute s g) (hσs : σ s = s) (n : ℕ)
    (x : G) : sigmaNormPow σ n (s * x) = s ^ n * sigmaNormPow σ n x :=
  sigmaPartialNorm_mul_of_central σ hs hσs x n

end NormScalars

section ScalarPowers

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq"

variable {K : Type*} [Field K]

private theorem scalarGL_pow (c : Kˣ) : ∀ m : ℕ, (scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) ^ m = scalarGL (c ^ m)
  | 0 => by rw [pow_zero, pow_zero, scalarGL_one]
  | m + 1 => by rw [pow_succ, scalarGL_pow c m, pow_succ, scalarGL_mul]

end ScalarPowers

section Transport

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq LT.TwistedNorm"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {RE : Type*} [CommRing RE] {E : Type*} [Field E] [Algebra RE E]
variable (ι : IntegralHom R K RE E) (σ : IntegralAut RE E)

private theorem toField_toField_eq_of_forall (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r) (y : K) :
    σ.toField (ι.toField y) = ι.toField y := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) y
  rw [map_div₀, map_div₀, ι.commutes, ι.commutes, σ.commutes, σ.commutes, hσ, hσ]

private theorem mapGL_mapGL_eq_of_forall (hσ : ∀ r : R, σ.toBase (ι.toBase r) = ι.toBase r)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : σ.mapGL (ι.mapGL g) = ι.mapGL g := by
  ext i j
  rw [IntegralAut.mapGL_apply, Matrix.GeneralLinearGroup.map_apply, toField_toField_eq_of_forall ι σ hσ]

omit [IsFractionRing R K] in

private theorem mapGL_map_eq_map_map (A : Matrix.GeneralLinearGroup (Fin 2) R) :
    ι.mapGL (Matrix.GeneralLinearGroup.map (algebraMap R K) A) =
      Matrix.GeneralLinearGroup.map (algebraMap RE E) (Matrix.GeneralLinearGroup.map ι.toBase A) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply, ι.commutes]

private theorem iterate_toField_algebraMap (r : RE) : ∀ m : ℕ, (⇑σ.toField)^[m] (algebraMap RE E r) =
    algebraMap RE E ((⇑σ.toBase)^[m] r)
  | 0 => rfl
  | m + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_toField_algebraMap r m, σ.commutes]

private theorem iterate_toField_div (p q : E) : ∀ m : ℕ, (⇑σ.toField)^[m] (p / q) = (⇑σ.toField)^[m] p / (⇑σ.toField)^[m] q
  | 0 => rfl
  | m + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      iterate_toField_div p q m, map_div₀]

private theorem iterate_toField_eq_self [IsFractionRing RE E] {n : ℕ} (hσn : ∀ x : RE, (⇑σ.toBase)^[n] x = x) (y : E) :
    (⇑σ.toField)^[n] y = y := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := RE) y
  rw [iterate_toField_div, iterate_toField_algebraMap, iterate_toField_algebraMap, hσn, hσn]

end Transport

section TwistedPlace

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq LT.TwistedNorm"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem twistedUnitOrbitalCount_eq_or_exists_swap (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : IntegralHom (v.adicCompletionIntegers K) (v.adicCompletion K) RE E)
    (hϖE : Irreducible (ι.toBase ϖ)) (n : ℕ) (hn : 1 ≤ n)
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ n)
    (σ : IntegralAut RE E) (hσ : ∀ r : v.adicCompletionIntegers K, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E) (hnorm : sigmaNormPow σ.mapGL n δ = ι.mapGL γ)
    (kδ : ℤ) (uδ : REˣ)
    (hdetδ : Matrix.det (δ : Matrix (Fin 2) (Fin 2) E) = algebraMap RE E uδ * algebraMap RE E (ι.toBase ϖ) ^ kδ)
    (hD : D = n * kδ) :
    (Even kδ ∧ twistedUnitOrbitalCount δ σ = unitOrbitalCount (v.adicCompletionIntegers K) γ) ∨
      (¬ Even kδ ∧ ∃ x₀ x₁ : Vertex RE E,
        Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          Vertex.twistedAct δ σ x₀ = x₁ ∧ Vertex.twistedAct δ σ x₁ = x₀) := by
  obtain ⟨x, k, c, hc, h⟩ := exists_conj_eq_scalarGL_mul K v ϖ hϖ γ hγ D u hdet

  set g : Matrix.GeneralLinearGroup (Fin 2) E := ι.mapGL x with hg
  have hσg : σ.mapGL g = g := mapGL_mapGL_eq_of_forall ι σ hσ x
  have hσg' : (⇑σ.mapGL)^[n] g = g := Function.iterate_fixed hσg n
  set δ₁ : Matrix.GeneralLinearGroup (Fin 2) E := g⁻¹ * δ * σ.mapGL g with hδ₁
  have hcount₁ : twistedUnitOrbitalCount δ₁ σ = twistedUnitOrbitalCount δ σ :=
    TwistedTreeTransport.twistedUnitOrbitalCount_twistedConj δ g σ
  have hnorm₁ : sigmaNormPow σ.mapGL n δ₁ = ι.mapGL (x⁻¹ * γ * x) := by
    rw [hδ₁, sigmaNormPow_sigmaConjElt σ.mapGL n hσg', hnorm, map_mul, map_mul, map_inv, hg]

  set πE : Eˣ := unitOfNeZero (K := E) hϖE.ne_zero with hπE
  have hcE : Units.map (ι.toField : v.adicCompletion K →* E) c = πE ^ k := by
    ext
    rw [Units.coe_map, MonoidHom.coe_coe, hc, map_zpow₀, ι.commutes, Units.val_zpow_eq_zpow_val, hπE,
      unitOfNeZero_coe]
  have hσπE : σ.unitMap πE = πE := by
    ext
    rw [IntegralAut.unitMap_coe, hπE, unitOfNeZero_coe, σ.commutes, hσ]
  have hσE : ∀ y : E, (⇑σ.toField)^[n] y = y := iterate_toField_eq_self σ hσn
  have hiter : (Vertex.twistedAct δ₁ σ)^[n] = Vertex.act (sigmaNormPow σ.mapGL n δ₁) :=
    funext fun y => TwistedTreeTransport.twistedAct_iterate_eq_act_sigmaNormPow δ₁ σ n hσE y

  have hswap : ∀ m : ℕ, 1 ≤ m → (Vertex.twistedAct δ₁ σ)^[m] (stdVertex RE E) = stdVertex RE E → ¬ Even kδ →
      ∃ x₀ x₁ : Vertex RE E,
        Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          Vertex.twistedAct δ σ x₀ = x₁ ∧ Vertex.twistedAct δ σ x₁ = x₀ := by
    intro m hm hstd hkδ
    rcases nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct RE E (ι.toBase ϖ) hϖE σ δ₁ m hm
        (Or.inl ⟨_, hstd⟩) with ⟨y, hy⟩ | ⟨x₀, x₁, hadj, hne, h₀, h₁⟩
    · exfalso
      rw [hδ₁, TwistedTreeTransport.twistedFixedVertexSet_twistedConj] at hy
      obtain ⟨y', hy', -⟩ := hy
      exact hkδ ((even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow
        RE E (ι.toBase ϖ) hϖE σ δ kδ uδ hdetδ).1 y' hy')
    · have hback : ∀ y : Vertex RE E,
          Vertex.twistedAct δ σ (Vertex.act g y) = Vertex.act g (Vertex.twistedAct δ₁ σ y) := by
        intro y
        rw [hδ₁, TwistedTreeTransport.twistedAct_twistedConj, TwistedTreeTransport.act_act_inv]
      exact ⟨Vertex.act g x₀, Vertex.act g x₁, isWithin_act g hadj, fun hxy => hne (act_injective g hxy),
        by rw [hback, h₀], by rw [hback, h₁]⟩

  have hintegral : ∀ γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K),
      x⁻¹ * γ * x =
          scalarGL c *
            Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ' →
        D = 2 * k →
        (∀ δ₂ : Matrix.GeneralLinearGroup (Fin 2) E,
            sigmaNormPow σ.mapGL n δ₂ =
                ι.mapGL
                  (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ') →
              twistedUnitOrbitalCount δ₂ σ =
                unitOrbitalCount (v.adicCompletionIntegers K)
                  (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ')) →
        (Even kδ ∧ twistedUnitOrbitalCount δ σ = unitOrbitalCount (v.adicCompletionIntegers K) γ) ∨
          (¬ Even kδ ∧ ∃ x₀ x₁ : Vertex RE E,
            Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
              Vertex.twistedAct δ σ x₀ = x₁ ∧ Vertex.twistedAct δ σ x₁ = x₀) := by
    intro γ' hx hDk hTU
    by_cases hkδ : Even kδ
    · left
      refine ⟨hkδ, ?_⟩
      obtain ⟨j, hj⟩ := hkδ
      have hk : k = n * j := by
        have h2 : (2 : ℤ) * k = 2 * (n * j) := by rw [← hDk, hD, hj]; ring
        exact mul_left_cancel₀ two_ne_zero h2

      set e : Eˣ := πE ^ (-j) with he
      have hen : e ^ n * πE ^ k = 1 := by
        rw [he, hk, ← zpow_natCast, ← zpow_mul, ← zpow_add]
        simp only [neg_mul, mul_comm (n : ℤ) j]
        rw [neg_add_cancel, zpow_zero]
      have hσe : σ.mapGL (scalarGL e) = scalarGL e := by
        rw [mapGL_scalarGL]
        congr 1
        ext
        rw [IntegralAut.unitMap_coe, he, Units.val_zpow_eq_zpow_val, map_zpow₀]
        congr 1
        exact congrArg Units.val hσπE
      have hnorm₂ : sigmaNormPow σ.mapGL n (scalarGL e * δ₁) =
          ι.mapGL
            (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) γ') := by
        rw [sigmaNormPow_mul_of_central σ.mapGL (fun h => scalarGL_mul_comm e h) hσe, hnorm₁, hx, map_mul,
          IntegralHom.mapGL_scalarGL, hcE, scalarGL_pow, ← mul_assoc, ← scalarGL_mul, hen, scalarGL_one, one_mul]
      rw [← hcount₁, ← TwistedTreeTransport.twistedUnitOrbitalCount_scalarGL_mul e δ₁ σ, hTU _ hnorm₂,
        unitOrbitalCount_eq_of_conj_eq_scalarGL_mul K v hx]
    · right
      refine ⟨hkδ, hswap n hn ?_ hkδ⟩
      rw [hiter, hnorm₁, hx, map_mul, IntegralHom.mapGL_scalarGL, act_scalarGL_mul, mapGL_map_eq_map_map]
      exact isFixedVertex_stdVertex_of_mem_range ⟨_, rfl⟩
  rcases h with ⟨γ', d, mu, Y, hY, hanis, hx, hDk⟩ | ⟨γ', d, mu, Y, w, hY, hdetY, htr, hx, hDk⟩ | ⟨e', A, hgg, hDk⟩
  · exact hintegral γ' hx hDk fun δ₂ hnorm₂ =>
      twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_anisotropic (v.adicCompletionIntegers K)
        (v.adicCompletion K) ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix d γ' mu Y hY hanis δ₂ hnorm₂
  · exact hintegral γ' hx hDk fun δ₂ hnorm₂ =>
      twistedUnitOrbitalCount_eq_unitOrbitalCount_of_sigmaNormPow_eq_of_eisenstein (v.adicCompletionIntegers K)
        (v.adicCompletion K) ϖ hϖ RE E ι hϖE n hres σ hσ hσn hfix d γ' mu Y hY w hdetY htr δ₂ hnorm₂
  · right

    have hkδ : ¬ Even kδ := by
      intro heven
      have h1 : Even D := by rw [hD]; exact heven.mul_left _
      rw [hDk] at h1
      exact (Int.not_even_iff_odd.2 ⟨k, rfl⟩) h1
    refine ⟨hkδ, hswap (n * 2) (by omega) ?_ hkδ⟩
    rw [Function.iterate_mul, hiter]
    show Vertex.act (sigmaNormPow σ.mapGL n δ₁) (Vertex.act (sigmaNormPow σ.mapGL n δ₁) (stdVertex RE E)) =
      stdVertex RE E
    rw [← Vertex.act_mul, hnorm₁, ← map_mul, hgg, map_mul, IntegralHom.mapGL_scalarGL, act_scalarGL_mul,
      mapGL_map_eq_map_map]
    exact isFixedVertex_stdVertex_of_mem_range ⟨_, rfl⟩

private theorem twistedUnitOrbitalCount_eq_unitOrbitalCount_of_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : IntegralHom (v.adicCompletionIntegers K) (v.adicCompletion K) RE E)
    (hϖE : Irreducible (ι.toBase ϖ)) (n : ℕ) (hn : 1 ≤ n)
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ n)
    (σ : IntegralAut RE E) (hσ : ∀ r : v.adicCompletionIntegers K, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E) (hnorm : sigmaNormPow σ.mapGL n δ = ι.mapGL γ)
    (kδ : ℤ) (uδ : REˣ)
    (hdetδ : Matrix.det (δ : Matrix (Fin 2) (Fin 2) E) = algebraMap RE E uδ * algebraMap RE E (ι.toBase ϖ) ^ kδ)
    (hD : D = n * kδ) (hk : Even kδ) :
    twistedUnitOrbitalCount δ σ = unitOrbitalCount (v.adicCompletionIntegers K) γ := by
  rcases twistedUnitOrbitalCount_eq_or_exists_swap K v ϖ hϖ RE E ι hϖE n hn hres σ hσ hσn hfix γ hγ D u hdet δ
      hnorm kδ uδ hdetδ hD with ⟨-, h⟩ | ⟨hodd, -⟩
  · exact h
  · exact absurd hk hodd

private theorem twistedUnitOrbitalCount_ne_zero_of_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : IntegralHom (v.adicCompletionIntegers K) (v.adicCompletion K) RE E)
    (hϖE : Irreducible (ι.toBase ϖ)) (n : ℕ) (hn : 1 ≤ n)
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ n)
    (σ : IntegralAut RE E) (hσ : ∀ r : v.adicCompletionIntegers K, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E) (hnorm : sigmaNormPow σ.mapGL n δ = ι.mapGL γ)
    (kδ : ℤ) (uδ : REˣ)
    (hdetδ : Matrix.det (δ : Matrix (Fin 2) (Fin 2) E) = algebraMap RE E uδ * algebraMap RE E (ι.toBase ϖ) ^ kδ)
    (hD : D = n * kδ) (hk : Even kδ) : twistedUnitOrbitalCount δ σ ≠ 0 := by
  rw [twistedUnitOrbitalCount_eq_unitOrbitalCount_of_even K v ϖ hϖ RE E ι hϖE n hn hres σ hσ hσn hfix γ hγ D u hdet δ
    hnorm kδ uδ hdetδ hD hk]
  exact unitOrbitalCount_ne_zero_of_even K v ϖ hϖ γ hγ D u hdet (by rw [hD]; exact hk.mul_left _)

private theorem exists_twisted_swap_of_not_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    (RE E : Type) [CommRing RE] [IsDomain RE] [IsDiscreteValuationRing RE] [Field E] [Algebra RE E]
    [IsFractionRing RE E] (ι : IntegralHom (v.adicCompletionIntegers K) (v.adicCompletion K) RE E)
    (hϖE : Irreducible (ι.toBase ϖ)) (n : ℕ) (hn : 1 ≤ n)
    (hres : Nat.card (RE ⧸ Ideal.span {ι.toBase ϖ}) = Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ n)
    (σ : IntegralAut RE E) (hσ : ∀ r : v.adicCompletionIntegers K, σ.toBase (ι.toBase r) = ι.toBase r)
    (hσn : ∀ x : RE, (σ.toBase : RE → RE)^[n] x = x)
    (hfix : ∀ x : RE, σ.toBase x = x → x ∈ Set.range ι.toBase)
    (γ : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : Matrix.GeneralLinearGroup (Fin 2) E) (hnorm : sigmaNormPow σ.mapGL n δ = ι.mapGL γ)
    (kδ : ℤ) (uδ : REˣ)
    (hdetδ : Matrix.det (δ : Matrix (Fin 2) (Fin 2) E) = algebraMap RE E uδ * algebraMap RE E (ι.toBase ϖ) ^ kδ)
    (hD : D = n * kδ) (hk : ¬ Even kδ) :
    ∃ x₀ x₁ : Vertex RE E,
      Vertex.IsWithin (unitOfNeZero (K := E) hϖE.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
        Vertex.twistedAct δ σ x₀ = x₁ ∧ Vertex.twistedAct δ σ x₁ = x₀ := by
  rcases twistedUnitOrbitalCount_eq_or_exists_swap K v ϖ hϖ RE E ι hϖE n hn hres σ hσ hσn hfix γ hγ D u hdet δ
      hnorm kδ uδ hdetδ hD with ⟨heven, -⟩ | ⟨-, hswap⟩
  · exact absurd heven hk
  · exact hswap

end TwistedPlace

end FixedOrInversion

namespace InertTransport

open NumberField IsDedekindDomain
open scoped TensorProduct

section CompactSubring

variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ₀] [TopologicalSpace E]
  [IsTopologicalRing E]

private theorem val_le_one_of_mem_of_isCompact (w : Valuation E Γ₀) (hball : IsOpen {a : E | w a ≤ 1})
    (S : Subring E) (hS : IsCompact (S : Set E)) {x : E} (hx : x ∈ S) : w x ≤ 1 := by
  by_contra hcon
  have hlt : 1 < w x := lt_of_not_ge hcon
  have hcover : (S : Set E) ⊆ ⋃ s ∈ (S : Set E), (fun a : E => s + a) '' {a : E | w a ≤ 1} := by
    intro s hs
    refine Set.mem_iUnion₂.2 ⟨s, hs, 0, ?_, add_zero s⟩
    show w 0 ≤ 1
    rw [map_zero]
    exact zero_le_one
  obtain ⟨t, -, htfin, hsub⟩ := hS.elim_finite_subcover_image
    (fun s _ => (Homeomorph.addLeft s).isOpenMap _ hball) hcover
  have hmem : ∀ k : ℕ, x ^ (k + 1) ∈ (S : Set E) := fun k => S.pow_mem hx _
  choose f hft hf using fun k => Set.mem_iUnion₂.1 (hsub (hmem k))
  haveI : Finite t := htfin.to_subtype
  obtain ⟨i, j, hij, hfij⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun k : ℕ => (⟨f k, hft k⟩ : t)
  have hfij' : f i = f j := congrArg Subtype.val hfij
  obtain ⟨a, ha, hxa⟩ := hf i
  obtain ⟨b, hb, hxb⟩ := hf j

  have hdiff : w (x ^ (i + 1) - x ^ (j + 1)) ≤ 1 := by
    have : x ^ (i + 1) - x ^ (j + 1) = a - b := by
      rw [← hxa, ← hxb, hfij']
      exact add_sub_add_left_eq_sub a b (f j)
    rw [this]
    exact (w.map_sub a b).trans (max_le ha hb)

  rcases lt_or_gt_of_ne hij with h | h
  · have hpow : w (x ^ (i + 1)) < w (x ^ (j + 1)) := by
      rw [map_pow, map_pow]
      exact pow_lt_pow_right₀ hlt (by omega)
    rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ hpow, map_pow] at hdiff
    exact absurd hdiff (not_le.2 (one_lt_pow₀ hlt (Nat.succ_ne_zero j)))
  · have hpow : w (x ^ (j + 1)) < w (x ^ (i + 1)) := by
      rw [map_pow, map_pow]
      exact pow_lt_pow_right₀ hlt (by omega)
    rw [Valuation.map_sub_eq_of_lt_left _ hpow, map_pow] at hdiff
    exact absurd hdiff (not_le.2 (one_lt_pow₀ hlt (Nat.succ_ne_zero i)))

end CompactSubring

section Completion

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem mem_adicCompletionIntegers_of_mem_of_isCompact (S : Subring (u.adicCompletion F))
    (hS : IsCompact (S : Set (u.adicCompletion F))) {x : u.adicCompletion F} (hx : x ∈ S) :
    x ∈ u.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine val_le_one_of_mem_of_isCompact (Valued.v : Valuation (u.adicCompletion F) _) ?_ S hS hx
  have h := (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 F) F).out u
  convert h using 1
  all_goals first | rfl | (ext; simp [HeightOneSpectrum.mem_adicCompletionIntegers])

end Completion

section ContinuousMap

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
variable (F' : Type) [Field F'] [NumberField F'] (u' : HeightOneSpectrum (𝓞 F'))

private theorem map_mem_adicCompletionIntegers_of_continuous (f : u.adicCompletion F →+* u'.adicCompletion F')
    (hf : Continuous f) {y : u.adicCompletion F} (hy : y ∈ u.adicCompletionIntegers F) :
    f y ∈ u'.adicCompletionIntegers F' := by
  refine mem_adicCompletionIntegers_of_mem_of_isCompact F' u'
    ((u.adicCompletionIntegers F).toSubring.map f) ?_ ⟨y, hy, rfl⟩
  rw [Subring.coe_map]
  exact (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 F) F u)).image hf

private theorem valued_coe_unit (x : (u.adicCompletionIntegers F)ˣ) :
    Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) = 1 := by
  have hmul : ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
      ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) = 1 :=
    congrArg Subtype.val (Units.mul_inv x)
  have hx : Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) ≤ 1 := by
    have h := (x : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hxi : Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
      u.adicCompletion F) ≤ 1 := by
    have h := ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  refine le_antisymm hx ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F)) := by rw [hmul, map_one]
    _ = Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
          u.adicCompletion F) := map_mul _ _ _
    _ ≤ Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) := mul_le_of_le_one_right' hxi

private theorem valued_coe_eq_of_irreducible {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : u.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer F u
  have hspan : Ideal.span {ϖ} = Ideal.span {π} :=
    hϖ.maximalIdeal_eq.symm.trans (HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer F u hπ)
  obtain ⟨c, hc⟩ := Ideal.span_singleton_eq_span_singleton.1 hspan
  rw [← hπ, ← hc]
  change _ = Valued.v ((ϖ : u.adicCompletion F) * ((c : u.adicCompletionIntegers F) : u.adicCompletion F))
  rw [map_mul, valued_coe_unit F u c, mul_one]

end ContinuousMap

section InertPair

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

open AutomorphicForm

private theorem algebraMap_mem_adicCompletionIntegers {c : v.adicCompletion K} (hc : c ∈ v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c ∈ w.1.adicCompletionIntegers L :=
  map_mem_adicCompletionIntegers_of_continuous K v L w.1 (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))
    (w.adicCompletionSemialgHom_continuous K L) hc

private noncomputable def iota :
    LT.LatticeTree.IntegralHom (v.adicCompletionIntegers K) (v.adicCompletion K) (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) where
  toField := algebraMap (v.adicCompletion K) (w.1.adicCompletion L)
  toBase :=
    { toFun := fun x => ⟨algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x,
        algebraMap_mem_adicCompletionIntegers K L v w x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  commutes _ := rfl

private theorem iota_toBase_coe (x : v.adicCompletionIntegers K) :
    ((iota K L v w).toBase x : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x :=
  rfl

private theorem irreducible_iota_toBase
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    {ϖK : v.adicCompletionIntegers K} (hϖK : Irreducible ϖK) : Irreducible ((iota K L v w).toBase ϖK) := by
  have hval : Valued.v (((iota K L v w).toBase ϖK : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      Multiplicative.ofAdd (-1 : ℤ) := by
    rw [iota_toBase_coe]
    change Valued.v (w.adicCompletionSemialgHom K L (ϖK : v.adicCompletion K)) = _
    rw [w.valued_adicCompletionSemialgHom K L, hw, pow_one, valued_coe_eq_of_irreducible K v hϖK]
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hval)
    (HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer L w.1 hval)

open scoped TensorProduct.RightActions in

private noncomputable def theta (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    w.1.adicCompletion L ≃+* w.1.adicCompletion L :=
  e.symm.toRingEquiv.trans
    ((Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := K) (A₁ := v.adicCompletion K))).toRingEquiv.trans
      e.toRingEquiv)

open scoped TensorProduct.RightActions in
private theorem theta_apply (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (y : w.1.adicCompletion L) :
    theta K L σ v w e y = e (sigmaTensor K L (v.adicCompletion K) σ (e.symm y)) := by
  simp only [theta, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
  rfl

open scoped TensorProduct.RightActions in

private noncomputable def glEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) ≃* GL (Fin 2) (w.1.adicCompletion L) :=
  MonoidHom.toMulEquiv (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom)
    (Matrix.GeneralLinearGroup.map e.symm.toAlgHom.toRingHom)
    (by
      ext g i j
      simp [Matrix.GeneralLinearGroup.map])
    (by
      ext g i j
      simp [Matrix.GeneralLinearGroup.map])

open scoped TensorProduct.RightActions in
private theorem glEquiv_apply (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e g = Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g := rfl

open scoped TensorProduct.RightActions in

private theorem glEquiv_sigmaGL (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e (sigmaGL K L (v.adicCompletion K) σ x) =
      Matrix.GeneralLinearGroup.map (theta K L σ v w e).toRingHom (glEquiv K L v w e x) := by
  apply Units.ext
  ext i j : 1
  change e (sigmaTensor K L (v.adicCompletion K) σ ((x : Matrix (Fin 2) (Fin 2) _) i j)) =
    theta K L σ v w e (e ((x : Matrix (Fin 2) (Fin 2) _) i j))
  rw [theta_apply, AlgEquiv.symm_apply_apply]

open scoped TensorProduct.RightActions in
private theorem theta_apply_apply (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (z : L ⊗[K] v.adicCompletion K) :
    theta K L σ v w e (e z) =
      e (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := K) (A₁ := v.adicCompletion K)) z) := by
  simp only [theta, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply]

open scoped TensorProduct.RightActions in

private theorem theta_algebraMap (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (c : v.adicCompletion K) :
    theta K L σ v w e (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) c := by
  rw [← e.commutes c, theta_apply_apply]
  congr 1
  rw [TensorProduct.RightActions.algebraMap_eval K (v.adicCompletion K) L c, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  rfl

open scoped TensorProduct.RightActions in

private noncomputable def thetaAlg (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := theta K L σ v w e) (theta_algebraMap K L σ v w e)

open scoped TensorProduct.RightActions in
private theorem thetaAlg_apply (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (y : w.1.adicCompletion L) : thetaAlg K L σ v w e y = theta K L σ v w e y := rfl

open scoped TensorProduct.RightActions in
private theorem continuous_theta (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Continuous (theta K L σ v w e) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  exact IsModuleTopology.continuous_of_linearMap (thetaAlg K L σ v w e).toLinearMap

open scoped TensorProduct.RightActions in
private theorem continuous_theta_symm (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Continuous (theta K L σ v w e).symm := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  exact IsModuleTopology.continuous_of_linearMap (thetaAlg K L σ v w e).symm.toLinearMap

open scoped TensorProduct.RightActions in
private theorem theta_mem (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) {y : w.1.adicCompletion L}
    (hy : y ∈ w.1.adicCompletionIntegers L) : theta K L σ v w e y ∈ w.1.adicCompletionIntegers L :=
  map_mem_adicCompletionIntegers_of_continuous L w.1 L w.1 (theta K L σ v w e).toRingHom
    (continuous_theta K L σ v w hdeg e) hy

open scoped TensorProduct.RightActions in
private theorem theta_symm_mem (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) {y : w.1.adicCompletion L}
    (hy : y ∈ w.1.adicCompletionIntegers L) : (theta K L σ v w e).symm y ∈ w.1.adicCompletionIntegers L :=
  map_mem_adicCompletionIntegers_of_continuous L w.1 L w.1 (theta K L σ v w e).symm.toRingHom
    (continuous_theta_symm K L σ v w hdeg e) hy

open scoped TensorProduct.RightActions in

private noncomputable def thetaAut (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    LT.LatticeTree.IntegralAut (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) where
  toField := theta K L σ v w e
  toBase :=
    { toFun := fun x => ⟨theta K L σ v w e (x : w.1.adicCompletion L), theta_mem K L σ v w hdeg e x.2⟩
      invFun := fun x =>
        ⟨(theta K L σ v w e).symm (x : w.1.adicCompletion L), theta_symm_mem K L σ v w hdeg e x.2⟩
      left_inv := fun x => Subtype.ext ((theta K L σ v w e).symm_apply_apply (x : w.1.adicCompletion L))
      right_inv := fun x => Subtype.ext ((theta K L σ v w e).apply_symm_apply (x : w.1.adicCompletion L))
      map_mul' := fun x y =>
        Subtype.ext (map_mul (theta K L σ v w e) (x : w.1.adicCompletion L) (y : w.1.adicCompletion L))
      map_add' := fun x y =>
        Subtype.ext (map_add (theta K L σ v w e) (x : w.1.adicCompletion L) (y : w.1.adicCompletion L)) }
  commutes _ := rfl

open scoped TensorProduct.RightActions in
private theorem thetaAut_toBase_coe (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x : w.1.adicCompletionIntegers L) :
    ((thetaAut K L σ v w hdeg e).toBase x : w.1.adicCompletion L) = theta K L σ v w e x := rfl

open scoped TensorProduct.RightActions in

private theorem thetaAut_toBase_iota (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (r : v.adicCompletionIntegers K) :
    (thetaAut K L σ v w hdeg e).toBase ((iota K L v w).toBase r) = (iota K L v w).toBase r :=
  Subtype.ext (theta_algebraMap K L σ v w e r)

open scoped TensorProduct.RightActions in

private theorem finrank_adicCompletion_eq (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  rw [← e.toLinearEquiv.finrank_eq, TensorProduct.finrank_rightAlgebra L]

private theorem pow_finrank_eq_one (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (θ : E ≃ₐ[F] E) : θ ^ Module.finrank F E = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank F (IntermediateField.fixedField (Subgroup.zpowers θ)) E)

private theorem fixedField_zpowers_eq_bot (F E : Type) [Field F] [Field E] [Algebra F E]
    (hdeg : (Module.finrank F E).Prime) (θ : E ≃ₐ[F] E) (hθ : θ ≠ 1) :
    IntermediateField.fixedField (Subgroup.zpowers θ) = ⊥ := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hdeg.pos
  have htower :=
    Module.finrank_mul_finrank F (IntermediateField.fixedField (Subgroup.zpowers θ)) E
  rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers] at htower
  have hdvd : orderOf θ ∣ Module.finrank F E := Dvd.intro_left _ htower
  rcases hdeg.eq_one_or_self_of_dvd _ hdvd with h₁ | hp
  · exact absurd (orderOf_eq_one_iff.1 h₁) hθ
  · rw [← IntermediateField.finrank_eq_one_iff]
    rw [hp] at htower
    exact Nat.eq_of_mul_eq_mul_right hdeg.pos (htower.trans (one_mul _).symm)

private theorem mem_fixedField_zpowers (F E : Type) [Field F] [Field E] [Algebra F E] (θ : E ≃ₐ[F] E) {x : E}
    (hx : θ x = x) : x ∈ IntermediateField.fixedField (Subgroup.zpowers θ) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro f hf
  have hle : Subgroup.zpowers θ ≤ MulAction.stabilizer (E ≃ₐ[F] E) x :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def]; exact hx))
  have := MulAction.mem_stabilizer_iff.1 (hle hf)
  rwa [AlgEquiv.smul_def] at this

open scoped TensorProduct.RightActions in

private theorem thetaAlg_ne_one (hσ : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    thetaAlg K L σ v w e ≠ 1 := by
  obtain ⟨l, hl⟩ : ∃ l : L, σ l ≠ l :=
    not_forall.1 fun h => hσ (AlgEquiv.ext fun l => (h l).trans (AlgEquiv.one_apply l).symm)
  let φ : L →+* w.1.adicCompletion L :=
    e.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom
  have hφ : ∀ l : L, thetaAlg K L σ v w e (φ l) = φ (σ l) := by
    intro l
    simp only [φ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_algHom, Algebra.TensorProduct.includeLeft_apply, thetaAlg_apply,
      theta_apply_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    rfl
  intro h1
  have h2 := hφ l
  rw [h1, AlgEquiv.one_apply] at h2
  exact hl (φ.injective h2).symm

open scoped TensorProduct.RightActions in
private theorem theta_iterate (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (k : ℕ)
    (y : w.1.adicCompletion L) : (⇑(theta K L σ v w e))^[k] y = (thetaAlg K L σ v w e ^ k) y := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, pow_zero, AlgEquiv.one_apply]
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply]; rfl

open scoped TensorProduct.RightActions in
private theorem thetaAut_toBase_iterate_coe (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (k : ℕ)
    (x : w.1.adicCompletionIntegers L) :
    (((⇑(thetaAut K L σ v w hdeg e).toBase)^[k] x : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      (⇑(theta K L σ v w e))^[k] (x : w.1.adicCompletion L) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

open scoped TensorProduct.RightActions in

private theorem thetaAut_toBase_iterate_finrank (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x : w.1.adicCompletionIntegers L) :
    (⇑(thetaAut K L σ v w hdeg e).toBase)^[Module.finrank K L] x = x := by
  haveI : FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion L) :=
    Module.finite_of_finrank_pos (by rw [finrank_adicCompletion_eq K L v w hdeg e]; exact hdeg.pos)
  apply Subtype.ext
  rw [thetaAut_toBase_iterate_coe, theta_iterate, ← finrank_adicCompletion_eq K L v w hdeg e,
    pow_finrank_eq_one, AlgEquiv.one_apply]

open scoped TensorProduct.RightActions in

private theorem theta_iterate_finrank (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (y : w.1.adicCompletion L) :
    (⇑(thetaAut K L σ v w hdeg e).toField)^[Module.finrank K L] y = y := by
  haveI : FiniteDimensional (v.adicCompletion K) (w.1.adicCompletion L) :=
    Module.finite_of_finrank_pos (by rw [finrank_adicCompletion_eq K L v w hdeg e]; exact hdeg.pos)
  change (⇑(theta K L σ v w e))^[Module.finrank K L] y = y
  rw [theta_iterate, ← finrank_adicCompletion_eq K L v w hdeg e, pow_finrank_eq_one, AlgEquiv.one_apply]

open scoped TensorProduct.RightActions in

private theorem thetaAlg_apply_eq_self_iff (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (x : w.1.adicCompletion L) :
    thetaAlg K L σ v w e x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) := by
  constructor
  · intro hx
    have hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime := by
      rw [finrank_adicCompletion_eq K L v w hdeg e]; exact hdeg
    have hbot := mem_fixedField_zpowers (v.adicCompletion K) (w.1.adicCompletion L) (thetaAlg K L σ v w e) hx
    rwa [fixedField_zpowers_eq_bot (v.adicCompletion K) (w.1.adicCompletion L) hprime _
      (thetaAlg_ne_one K L σ v w hσ e), IntermediateField.mem_bot] at hbot
  · rintro ⟨c, rfl⟩
    exact theta_algebraMap K L σ v w e c

open scoped TensorProduct.RightActions in

private theorem mem_range_iota_toBase_of_fixed (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x : w.1.adicCompletionIntegers L) (hx : (thetaAut K L σ v w hdeg e).toBase x = x) :
    x ∈ Set.range (iota K L v w).toBase := by
  have hfield : thetaAlg K L σ v w e (x : w.1.adicCompletion L) = x := congrArg Subtype.val hx
  obtain ⟨c, hc⟩ := (thetaAlg_apply_eq_self_iff K L σ v w hdeg hσ e _).1 hfield
  have hcint : c ∈ v.adicCompletionIntegers K := by
    have hxint := x.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hxint ⊢
    rw [← hc] at hxint
    change Valued.v (w.adicCompletionSemialgHom K L c) ≤ 1 at hxint
    rwa [w.valued_adicCompletionSemialgHom K L, hw, pow_one] at hxint
  exact ⟨⟨c, hcint⟩, Subtype.ext hc⟩

open scoped TensorProduct.RightActions in
private theorem thetaAut_toField (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    (thetaAut K L σ v w hdeg e).toField = theta K L σ v w e := rfl

private theorem generalLinearGroup_map_coe_apply {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (y : GL (Fin 2) R) (a b : Fin 2) :
    ((Matrix.GeneralLinearGroup.map f y : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) a b =
      f ((y : Matrix (Fin 2) (Fin 2) R) a b) :=
  Matrix.GeneralLinearGroup.map_apply f a b y

open scoped TensorProduct.RightActions in

private theorem thetaAut_mapGL_iterate (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (i : ℕ)
    (y : GL (Fin 2) (w.1.adicCompletion L)) :
    (⇑(thetaAut K L σ v w hdeg e).mapGL)^[i] y =
      Matrix.GeneralLinearGroup.map (thetaAlg K L σ v w e ^ i).toAlgHom.toRingHom y := by
  induction i with
  | zero =>
      refine Units.ext (Matrix.ext fun a b => ?_)
      rw [Function.iterate_zero_apply, generalLinearGroup_map_coe_apply, pow_zero]
      rfl
  | succ i ih =>
      refine Units.ext (Matrix.ext fun a b => ?_)
      rw [Function.iterate_succ_apply', ih, LT.LatticeTree.IntegralAut.mapGL_apply, thetaAut_toField,
        generalLinearGroup_map_coe_apply, generalLinearGroup_map_coe_apply]
      change theta K L σ v w e ((thetaAlg K L σ v w e ^ i) _) = (thetaAlg K L σ v w e ^ (i + 1)) _
      rw [pow_succ', AlgEquiv.mul_apply]
      rfl

open scoped TensorProduct.RightActions in
private theorem glEquiv_iterate_sigmaGL (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (i : ℕ)
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e ((⇑(sigmaGL K L (v.adicCompletion K) σ))^[i] x) =
      (⇑(thetaAut K L σ v w hdeg e).mapGL)^[i] (glEquiv K L v w e x) :=
  (Function.Semiconj.iterate_right (fun x => glEquiv_sigmaGL K L σ v w e x) i) x

open scoped TensorProduct.RightActions in

private theorem glEquiv_normString (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e (normString K L (v.adicCompletion K) σ δ) =
      LT.TwistedNorm.sigmaNormPow (thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) := by
  rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => glEquiv_iterate_sigmaGL K L σ v w hdeg e i δ

open scoped TensorProduct.RightActions in

private theorem glEquiv_normString_eq_prod (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e (normString K L (v.adicCompletion K) σ δ) =
      ((List.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))).map fun i : ℕ =>
        Matrix.GeneralLinearGroup.map (thetaAlg K L σ v w e ^ i).toAlgHom.toRingHom (glEquiv K L v w e δ)).prod := by
  rw [glEquiv_normString K L σ v w hdeg e δ, finrank_adicCompletion_eq K L v w hdeg e,
    LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  congr 1
  exact List.map_congr_left fun i _ => thetaAut_mapGL_iterate K L σ v w hdeg e i _

end InertPair

end InertTransport

namespace TwistedTorusIndices

open scoped ENNReal

section Measure

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

private theorem measure_coe_eq_relIndex_mul (μ : Measure G) [μ.IsMulLeftInvariant] {H H' : Subgroup G}
    (hle : H ≤ H') (hfin : H.relIndex H' ≠ 0) (hH : MeasurableSet (H : Set G)) :
    μ (H' : Set G) = (H.relIndex H' : ℝ≥0∞) * μ (H : Set G) := by
  classical
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hfin⟩
  let rep : H' ⧸ H.subgroupOf H' → G := fun q => ((Quotient.out q : H') : G)
  let piece : H' ⧸ H.subgroupOf H' → Set G := fun q => (fun x => (rep q)⁻¹ * x) ⁻¹' (H : Set G)
  have hrep : ∀ q, rep q ∈ H' := fun q => (Quotient.out q : H').2
  have hmk : ∀ (y : H') (q : H' ⧸ H.subgroupOf H'), (y : H' ⧸ H.subgroupOf H') = q ↔ (rep q)⁻¹ * y ∈ H := by
    intro y q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hcover : (H' : Set G) = ⋃ q, piece q := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      exact ⟨(⟨x, hx⟩ : H'), (hmk ⟨x, hx⟩ _).1 rfl⟩
    · rintro ⟨q, hq⟩
      have := H'.mul_mem (hrep q) (hle hq)
      rwa [mul_inv_cancel_left] at this
  have hdisj : Pairwise (Function.onFun Disjoint piece) := by
    intro q₁ q₂ hne
    refine Set.disjoint_left.2 fun x h₁ h₂ => hne ?_
    have hx₁ : (rep q₁)⁻¹ * x ∈ H := h₁
    have hx₂ : (rep q₂)⁻¹ * x ∈ H := h₂
    have hy : (rep q₁)⁻¹ * rep q₂ ∈ H := by
      have := H.mul_mem hx₁ (H.inv_mem hx₂)
      rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
    rw [← QuotientGroup.out_eq' q₂, eq_comm, hmk]
    exact hy
  have hmeas : ∀ q, MeasurableSet (piece q) := fun q => measurable_const_mul _ hH
  have hpiece : ∀ q, μ (piece q) = μ (H : Set G) := fun q => measure_preimage_mul μ _ _
  rw [hcover, measure_iUnion hdisj hmeas]
  simp only [hpiece, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  rfl

end Measure

section Transitive

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq Module"
open scoped Matrix

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem _root_.TwistedTorusIndices.act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g v) = v := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

p2m_export "TwistedTorusIndices" "act_inv_act"
private theorem _root_.TwistedTorusIndices.act_act_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g (Vertex.act g⁻¹ v) = v := by
  rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

p2m_export "TwistedTorusIndices" "act_act_inv"

private theorem act_eq_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) (x y : Vertex R K) :
    Vertex.act g x = y ↔ x = Vertex.act g⁻¹ y :=
  ⟨fun h => by rw [← h, act_inv_act], fun h => by rw [h, act_act_inv]⟩

variable (R K) in

private theorem isTorsionFree_of_isFractionRing [IsDomain R] [IsFractionRing R K] : Module.IsTorsionFree R K :=
  Module.isTorsionFree_iff_smul_eq_zero.2 fun r x h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h0 => (map_eq_zero_iff _ (IsFractionRing.injective R K)).1 h0) id

private theorem exists_latticeMap_stdLattice_eq [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, latticeMap g (stdLattice R K) = L := by
  classical
  haveI : Module.IsTorsionFree R K := isTorsionFree_of_isFractionRing R K
  haveI : Submodule.IsLattice K L := ⟨hL.1, hL.2⟩
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R L) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Submodule.IsLattice.finrank_of_pi K L, Fintype.card_fin]
  let b : Basis (Fin 2) R L := (Module.Free.chooseBasis R L).reindex (Fintype.equivFinOfCardEq hcard)
  let bK : Basis (Fin 2) K (Fin 2 → K) := b.extendOfIsLattice K
  let e : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  refine ⟨⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK, bK.toMatrix_mul_toMatrix_flip e⟩,
    ?_⟩
  have hcol : ∀ j : Fin 2, (e.toMatrix bK) *ᵥ (Pi.single j 1 : Fin 2 → K) = (b j : Fin 2 → K) := by
    intro j
    ext i
    rw [Matrix.mulVec_single_one]
    change e.toMatrix bK i j = _
    simp only [e, bK, Basis.toMatrix_apply, Pi.basisFun_repr, Basis.extendOfIsLattice_apply]
  have himg : (mulVecLinR (R := R) (⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK,
      bK.toMatrix_mul_toMatrix_flip e⟩ : Matrix.GeneralLinearGroup (Fin 2) K)) ''
        Set.range (fun j : Fin 2 => (Pi.single j 1 : Fin 2 → K)) =
      L.subtype '' Set.range b := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext j
    exact hcol j
  rw [latticeMap, stdLattice_eq_span, Submodule.map_span, himg, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

private theorem exists_act_stdVertex_eq [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] (x : Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, Vertex.act g (stdVertex R K) = x := by
  induction x using Quotient.inductionOn with
  | h L =>
    obtain ⟨g, hg⟩ := exists_latticeMap_stdLattice_eq L.2
    refine ⟨g, ?_⟩
    change Vertex.mk R K (latticeMap g (stdLattice R K)) _ = Vertex.mk R K L.1 L.2
    rw [Vertex.mk_eq_mk_iff, hg]
    exact Homothetic.refl L.1

end Transitive

section Twisted

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq AutomorphicForm"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem galAct_act (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.galAct σ (Vertex.act g v) = Vertex.act (σ.mapGL g) (Vertex.galAct σ v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeGal_latticeMap σ g L.1))

private theorem coe_map_apply (y : Matrix.GeneralLinearGroup (Fin 2) R) :
    ((Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      (y : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K) := rfl

private theorem det_map (y : Matrix.GeneralLinearGroup (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K) y) =
      Units.map (algebraMap R K).toMonoidHom (Matrix.GeneralLinearGroup.det y) := by
  ext
  change Matrix.det ((y : Matrix (Fin 2) (Fin 2) R).map _) = algebraMap R K (Matrix.det _)
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

private theorem exists_det_eq_of_mem_range {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    ∃ w : Rˣ, Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w := by
  obtain ⟨y, rfl⟩ := hg
  exact ⟨Matrix.GeneralLinearGroup.det y, congrArg Units.val (det_map y)⟩

private theorem _root_.TwistedTorusIndices.det_coe_conj (s t : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.det ((s⁻¹ * t * s : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.det (t : Matrix (Fin 2) (Fin 2) K) := by
  have h1 : Matrix.det ((s⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      Matrix.det (s : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, h1, one_mul]

p2m_export "TwistedTorusIndices" "det_coe_conj"
variable (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)

private noncomputable def twistedUnitCentralizer : Subgroup (Matrix.GeneralLinearGroup (Fin 2) K) :=
  sigmaCentralizer σ.mapGL δ ⊓
    Subgroup.comap (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ)
      (Units.map (algebraMap R K).toMonoidHom).range

private theorem mem_twistedUnitCentralizer_iff (t : Matrix.GeneralLinearGroup (Fin 2) K) :
    t ∈ twistedUnitCentralizer σ δ ↔
      t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        ∃ w : Rˣ, Matrix.det (t : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w := by
  rw [twistedUnitCentralizer, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_range]
  refine and_congr Iff.rfl (exists_congr fun w => ?_)
  exact ⟨fun h => (congrArg Units.val h).symm, fun h => Units.ext h.symm⟩

private theorem twistedUnitCentralizer_le : twistedUnitCentralizer σ δ ≤ sigmaCentralizer σ.mapGL δ :=
  fun _ ht => ((mem_twistedUnitCentralizer_iff σ δ _).1 ht).1

private noncomputable def twistedConjStabilizer (s : Matrix.GeneralLinearGroup (Fin 2) K) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) K) :=
  sigmaCentralizer σ.mapGL δ ⊓
    (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range.map (MulAut.conj s).toMonoidHom

private theorem mem_twistedConjStabilizer_iff_range (s t : Matrix.GeneralLinearGroup (Fin 2) K) :
    t ∈ twistedConjStabilizer σ δ s ↔
      t ∈ sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  rw [twistedConjStabilizer, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

private theorem twistedConjStabilizer_le_twistedUnitCentralizer (s : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedConjStabilizer σ δ s ≤ twistedUnitCentralizer σ δ := by
  intro t ht
  rw [mem_twistedConjStabilizer_iff_range] at ht
  rw [mem_twistedUnitCentralizer_iff]
  refine ⟨ht.1, ?_⟩
  obtain ⟨w, hw⟩ := exists_det_eq_of_mem_range ht.2
  exact ⟨w, (det_coe_conj s t).symm.trans hw⟩

private theorem measure_twistedUnitCentralizer_subgroupOf_eq [MeasurableSpace (sigmaCentralizer σ.mapGL δ)]
    [MeasurableMul (sigmaCentralizer σ.mapGL δ)] (μ : MeasureTheory.Measure (sigmaCentralizer σ.mapGL δ))
    [μ.IsMulLeftInvariant] (s : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) ≠ 0)
    (hmeas : MeasurableSet ((twistedConjStabilizer σ δ s).subgroupOf (sigmaCentralizer σ.mapGL δ) :
      Set (sigmaCentralizer σ.mapGL δ))) :
    μ ((twistedUnitCentralizer σ δ).subgroupOf (sigmaCentralizer σ.mapGL δ) : Set (sigmaCentralizer σ.mapGL δ)) =
      ((twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) : ℝ≥0∞) *
        μ ((twistedConjStabilizer σ δ s).subgroupOf (sigmaCentralizer σ.mapGL δ) :
          Set (sigmaCentralizer σ.mapGL δ)) := by
  have hTc := twistedUnitCentralizer_le σ δ
  have hle : (twistedConjStabilizer σ δ s).subgroupOf (sigmaCentralizer σ.mapGL δ) ≤
      (twistedUnitCentralizer σ δ).subgroupOf (sigmaCentralizer σ.mapGL δ) :=
    fun _ hx => Subgroup.mem_subgroupOf.2
      (twistedConjStabilizer_le_twistedUnitCentralizer σ δ s (Subgroup.mem_subgroupOf.1 hx))
  rw [measure_coe_eq_relIndex_mul μ hle (by rwa [Subgroup.relIndex_subgroupOf hTc]) hmeas,
    Subgroup.relIndex_subgroupOf hTc]

private theorem twistedAct_act_of_mem {t : Matrix.GeneralLinearGroup (Fin 2) K} (ht : t ∈ sigmaCentralizer σ.mapGL δ)
    (x : Vertex R K) :
    Vertex.twistedAct δ σ (Vertex.act t x) = Vertex.act t (Vertex.twistedAct δ σ x) := by
  have h : δ * σ.mapGL t = t * δ := (mul_inv_eq_iff_eq_mul.1 (mem_sigmaCentralizer_iff.1 ht)).symm
  simp only [Vertex.twistedAct]
  rw [galAct_act, ← Vertex.act_mul, h, Vertex.act_mul]

section Closed

variable [TopologicalSpace K] [IsTopologicalRing K]

private theorem isClosed_sigmaCentralizer [T2Space K] (hσ : Continuous σ.mapGL) :
    IsClosed (sigmaCentralizer σ.mapGL δ : Set (Matrix.GeneralLinearGroup (Fin 2) K)) := by
  show IsClosed {t : Matrix.GeneralLinearGroup (Fin 2) K | t * δ * (σ.mapGL t)⁻¹ = δ}
  exact isClosed_eq ((continuous_id.mul continuous_const).mul hσ.inv) continuous_const

end Closed

section Scalars

private theorem twistedConj_mul_mul {t : Matrix.GeneralLinearGroup (Fin 2) K} (ht : t ∈ sigmaCentralizer σ.mapGL δ) (s u :
    Matrix.GeneralLinearGroup (Fin 2) K) :
    (t * s * u)⁻¹ * δ * σ.mapGL (t * s * u) = u⁻¹ * (s⁻¹ * δ * σ.mapGL s) * σ.mapGL u := by
  have ht' : t⁻¹ * δ * σ.mapGL t = δ := by
    rw [mul_assoc, ← mul_inv_eq_iff_eq_mul.1 (mem_sigmaCentralizer_iff.1 ht), inv_mul_cancel_left]
  calc (t * s * u)⁻¹ * δ * σ.mapGL (t * s * u)
      = u⁻¹ * (s⁻¹ * (t⁻¹ * δ * σ.mapGL t) * σ.mapGL s) * σ.mapGL u := by
        rw [map_mul, map_mul]
        group
    _ = u⁻¹ * (s⁻¹ * δ * σ.mapGL s) * σ.mapGL u := by rw [ht']

private theorem sigmaCentralizer_scalarGL_mul (c : Kˣ) :
    sigmaCentralizer σ.mapGL (scalarGL c * δ) = sigmaCentralizer σ.mapGL δ := by
  ext t
  have key : t * (scalarGL c * δ) * (σ.mapGL t)⁻¹ = scalarGL c * (t * δ * (σ.mapGL t)⁻¹) := by
    rw [← mul_assoc, ← scalarGL_mul_comm]
    simp only [mul_assoc]
  rw [mem_sigmaCentralizer_iff, mem_sigmaCentralizer_iff, key]
  exact mul_right_inj _

end Scalars

section Masses

private theorem relIndex_mul_measureReal_eq [MeasurableSpace (sigmaCentralizer σ.mapGL δ)]
    [MeasurableMul (sigmaCentralizer σ.mapGL δ)] (μ : MeasureTheory.Measure (sigmaCentralizer σ.mapGL δ))
    [μ.IsMulLeftInvariant] (s : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) ≠ 0)
    (hmeas : MeasurableSet ((twistedConjStabilizer σ δ s).subgroupOf (sigmaCentralizer σ.mapGL δ) :
      Set (sigmaCentralizer σ.mapGL δ))) :
    ((twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) : ℝ) *
        (μ ((twistedConjStabilizer σ δ s).subgroupOf (sigmaCentralizer σ.mapGL δ) :
          Set (sigmaCentralizer σ.mapGL δ))).toReal =
      (μ ((twistedUnitCentralizer σ δ).subgroupOf (sigmaCentralizer σ.mapGL δ) :
        Set (sigmaCentralizer σ.mapGL δ))).toReal := by
  rw [measure_twistedUnitCentralizer_subgroupOf_eq σ δ μ s hfin hmeas, ENNReal.toReal_mul, ENNReal.toReal_natCast]

end Masses

variable [IsFractionRing R K]

private theorem mem_integralUnitsSet_range_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    g ∈ integralUnitsSet (Set.range (algebraMap R K)) ↔
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  constructor
  · intro hg
    rw [mem_integralUnitsSet] at hg
    choose A hA using hg.1
    choose B hB using hg.2
    have hAm : (Matrix.of A).map (algebraMap R K) = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hA i j
    have hBm : (Matrix.of B).map (algebraMap R K) =
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hB i j
    have hAB : Matrix.of A * Matrix.of B = 1 := by
      apply Matrix.map_injective (IsFractionRing.injective R K)
      show (Matrix.of A * Matrix.of B).map (algebraMap R K) = (1 : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K)
      rw [Matrix.map_mul, hAm, hBm, Matrix.map_one _ (map_zero _) (map_one _), Units.mul_inv]
    have hBA : Matrix.of B * Matrix.of A = 1 := by
      apply Matrix.map_injective (IsFractionRing.injective R K)
      show (Matrix.of B * Matrix.of A).map (algebraMap R K) = (1 : Matrix (Fin 2) (Fin 2) R).map (algebraMap R K)
      rw [Matrix.map_mul, hAm, hBm, Matrix.map_one _ (map_zero _) (map_one _), Units.inv_mul]
    exact ⟨⟨Matrix.of A, Matrix.of B, hAB, hBA⟩, Units.ext hAm⟩
  · intro hg
    rw [mem_integralUnitsSet]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact RingHom.mem_rangeS.1 (isInteger_apply_of_mem_range hg i j)
    · exact RingHom.mem_rangeS.1 (isInteger_apply_of_mem_range (Subgroup.inv_mem _ hg) i j)

private theorem coe_range_eq :
    (((Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range :
        Subgroup (Matrix.GeneralLinearGroup (Fin 2) K)) : Set (Matrix.GeneralLinearGroup (Fin 2) K)) =
      integralUnitsSet (Set.range (algebraMap R K)) :=
  Set.ext fun g => (mem_integralUnitsSet_range_iff g).symm

private theorem mem_twistedConjStabilizer_iff (s t : Matrix.GeneralLinearGroup (Fin 2) K) :
    t ∈ twistedConjStabilizer σ δ s ↔
      t ∈ AutomorphicForm.sigmaCentralizer σ.mapGL δ ∧
        s⁻¹ * t * s ∈ AutomorphicForm.integralUnitsSet (Set.range (algebraMap R K)) := by
  rw [mem_twistedConjStabilizer_iff_range, mem_integralUnitsSet_range_iff]

private theorem coe_twistedConjStabilizer (s : Matrix.GeneralLinearGroup (Fin 2) K) :
    (twistedConjStabilizer σ δ s : Set (Matrix.GeneralLinearGroup (Fin 2) K)) =
      (sigmaCentralizer σ.mapGL δ : Set (Matrix.GeneralLinearGroup (Fin 2) K)) ∩
        (fun u => s * u * s⁻¹) '' integralUnitsSet (Set.range (algebraMap R K)) := by
  rw [twistedConjStabilizer, Subgroup.coe_inf, Subgroup.coe_map, coe_range_eq]
  rfl

section Compact

variable [TopologicalSpace K] [IsTopologicalRing K]

private theorem isCompact_twistedConjStabilizer
    (hT : IsClosed (sigmaCentralizer σ.mapGL δ : Set (Matrix.GeneralLinearGroup (Fin 2) K)))
    (hU : IsCompact (integralUnitsSet (Set.range (algebraMap R K)))) (s : Matrix.GeneralLinearGroup (Fin 2) K) :
    IsCompact (twistedConjStabilizer σ δ s : Set (Matrix.GeneralLinearGroup (Fin 2) K)) := by
  rw [coe_twistedConjStabilizer]
  exact (hU.image ((continuous_const.mul continuous_id).mul continuous_const)).inter_left hT

end Compact

section Systems

open scoped Pointwise

private theorem mapGL_mem_integralUnitsSet_range {u : Matrix.GeneralLinearGroup (Fin 2) K} (hu : u ∈ integralUnitsSet
    (Set.range (algebraMap R K))) :
    σ.mapGL u ∈ integralUnitsSet (Set.range (algebraMap R K)) := by
  rw [mem_integralUnitsSet_range_iff] at hu ⊢
  obtain ⟨A, rfl⟩ := hu
  refine ⟨Matrix.GeneralLinearGroup.map (σ.toBase : R →+* R) A, ?_⟩
  ext i j
  show algebraMap R K (σ.toBase ((A : Matrix (Fin 2) (Fin 2) R) i j)) =
    σ.toField (algebraMap R K ((A : Matrix (Fin 2) (Fin 2) R) i j))
  exact (σ.commutes _).symm

private theorem mul_mem_integralUnitsSet_range {g h : Matrix.GeneralLinearGroup (Fin 2) K} (hg : g ∈ integralUnitsSet
    (Set.range (algebraMap R K))) (hh : h ∈ integralUnitsSet (Set.range (algebraMap R K))) : g *
    h ∈ integralUnitsSet (Set.range (algebraMap R K)) := by
  rw [mem_integralUnitsSet_range_iff] at hg hh ⊢
  exact Subgroup.mul_mem _ hg hh

private theorem inv_mem_integralUnitsSet_range {g : Matrix.GeneralLinearGroup (Fin 2) K} (hg : g ∈ integralUnitsSet (Set.range
    (algebraMap R K))) : g⁻¹ ∈ integralUnitsSet (Set.range (algebraMap R K)) := by
  rw [mem_integralUnitsSet_range_iff] at hg ⊢
  exact Subgroup.inv_mem _ hg

private theorem mul_mem_mul_mul_of_mem {d y : Matrix.GeneralLinearGroup (Fin 2) K} (hy : y ∈ integralUnitsSet (Set.range
    (algebraMap R K)) * ({d} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) *
    integralUnitsSet (Set.range (algebraMap R K)))
    {u u' : Matrix.GeneralLinearGroup (Fin 2) K} (hu : u ∈ integralUnitsSet (Set.range (algebraMap R K))) (hu' : u' ∈
        integralUnitsSet (Set.range (algebraMap R K))) : u * y *
        u' ∈ integralUnitsSet (Set.range (algebraMap R K)) * ({d} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) *
        integralUnitsSet (Set.range (algebraMap R K)) := by
  obtain ⟨_, ⟨u₁, hu₁, e, he, rfl⟩, u₂, hu₂, rfl⟩ := hy
  refine ⟨u * u₁ * e, ⟨u * u₁, mul_mem_integralUnitsSet_range hu hu₁, e, he, rfl⟩, u₂ * u',
    mul_mem_integralUnitsSet_range hu₂ hu', ?_⟩
  simp only [mul_assoc]

private theorem twistedConj_mem_of_eq_mul {d x s t u : Matrix.GeneralLinearGroup (Fin 2) K} (ht : t ∈ sigmaCentralizer σ.mapGL
    δ) (hu : u ∈ integralUnitsSet (Set.range (algebraMap R K)))
    (hx : x = t * s * u) (hmem : x⁻¹ * δ * σ.mapGL x ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({d} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K))) :
    s⁻¹ * δ * σ.mapGL s ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({d} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)) := by
  rw [hx, twistedConj_mul_mul σ δ ht] at hmem
  have h := mul_mem_mul_mul_of_mem hmem hu (inv_mem_integralUnitsSet_range (mapGL_mem_integralUnitsSet_range σ hu))
  have hX : u * (u⁻¹ * (s⁻¹ * δ * σ.mapGL s) * σ.mapGL u) * (σ.mapGL u)⁻¹ = s⁻¹ * δ * σ.mapGL s := by group
  rwa [hX] at h

private theorem scalarGL_zpow_mul_mem_iff (ϖ : R) (hϖ : Irreducible ϖ) (b : ℤ) (dl : Matrix.GeneralLinearGroup (Fin 2) K)
    (hdl : (dl : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap R K ϖ ^ b, algebraMap R K ϖ ^ b])
    (y : Matrix.GeneralLinearGroup (Fin 2) K) :
    scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (-b)) * y ∈ integralUnitsSet (Set.range (algebraMap R K)) ↔
        y ∈ integralUnitsSet (Set.range (algebraMap R K)) * ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) *
        integralUnitsSet (Set.range (algebraMap R K)) := by
  have hdl' : dl = scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ b) := by
    apply Units.ext
    rw [hdl, scalarGL_coe, Units.val_zpow_eq_zpow_val, unitOfNeZero_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have hinv : scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (-b)) * dl = 1 := by
    rw [hdl', ← scalarGL_mul, ← zpow_add, neg_add_cancel, zpow_zero, scalarGL_one]
  have hinv' : dl * scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (-b)) = 1 := by
    rw [hdl', ← scalarGL_mul, ← zpow_add, add_neg_cancel, zpow_zero, scalarGL_one]
  have h1 : (1 : Matrix.GeneralLinearGroup (Fin 2) K) ∈ integralUnitsSet (Set.range (algebraMap R K)) := by
    rw [mem_integralUnitsSet_range_iff]
    exact Subgroup.one_mem _
  constructor
  · intro hy
    refine ⟨dl, ⟨1, h1, dl, rfl, one_mul dl⟩, scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (-b)) * y, hy, ?_⟩
    show dl * (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (-b)) * y) = y
    rw [← mul_assoc, hinv', one_mul]
  · intro hy
    obtain ⟨_, ⟨u₁, hu₁, e, he, rfl⟩, u₂, hu₂, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at he
    rw [he]
    have hcomm : scalarGL (unitOfNeZero (K := K) hϖ.ne_zero ^ (-b)) * (u₁ * dl * u₂) = u₁ * u₂ := by
      rw [← mul_assoc, ← mul_assoc, scalarGL_mul_comm, mul_assoc u₁, hinv, mul_one]
    rw [hcomm]
    exact mul_mem_integralUnitsSet_range hu₁ hu₂

end Systems

variable [IsDomain R] [IsDiscreteValuationRing R]

private theorem scalarGL_mem_range_of_sq {c : Kˣ} {u : Rˣ} (hc : (c : K) ^ 2 = algebraMap R K u) :
    scalarGL c ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hu : algebraMap R K u * algebraMap R K (u⁻¹ : Rˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : (c : K)⁻¹ = (c : K) * algebraMap R K (u⁻¹ : Rˣ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← sq, hc, hu]
  have hself : (c : K) = (c : K)⁻¹ * algebraMap R K u := by
    rw [← hc, sq, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

  have hmem : (∃ a : R, algebraMap R K a = (c : K)) ∧ ∃ b : R, algebraMap R K b = (c : K)⁻¹ := by
    rcases ValuationRing.isInteger_or_isInteger R (c : K) with h | h
    · obtain ⟨a, ha⟩ := RingHom.mem_rangeS.1 h
      refine ⟨⟨a, ha⟩, ⟨a * (u⁻¹ : Rˣ), ?_⟩⟩
      rw [map_mul, ha, hinv]
    · obtain ⟨b, hb⟩ := RingHom.mem_rangeS.1 h
      refine ⟨⟨b * u, ?_⟩, ⟨b, hb⟩⟩
      rw [map_mul, hb, ← hself]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hmem
  have hab : a * b = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, ha, hb, mul_inv_cancel₀ hc0, map_one]
  have hba : b * a = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, ha, hb, inv_mul_cancel₀ hc0, map_one]
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) ⟨a, b, hab, hba⟩, Units.ext ?_⟩
  rw [coe_map_apply]
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.one_apply, apply_ite (algebraMap R K), ha]

private theorem mem_range_of_scalarGL_mul {m : Matrix.GeneralLinearGroup (Fin 2) K} {w : Rˣ}
    (hm : Matrix.det (m : Matrix (Fin 2) (Fin 2) K) = algebraMap R K w) {c : Kˣ}
    (hc : scalarGL c * m ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    m ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  obtain ⟨w', hw'⟩ := exists_det_eq_of_mem_range hc
  have hdet : Matrix.det ((scalarGL c * m : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) ^ 2 * algebraMap R K w := by
    rw [Units.val_mul, Matrix.det_mul, scalarGL_coe, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, hm]
  have hsq : (c : K) ^ 2 = algebraMap R K (w' * w⁻¹ : Rˣ) := by
    rw [Units.val_mul, map_mul, ← hw', hdet, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  have hs := scalarGL_mem_range_of_sq (R := R) hsq
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) hc
  rwa [inv_mul_cancel_left] at this

private theorem mem_twistedConjStabilizer_iff_act_eq {t : Matrix.GeneralLinearGroup (Fin 2) K}
    (ht : t ∈ twistedUnitCentralizer σ δ) (s : Matrix.GeneralLinearGroup (Fin 2) K) :
    t ∈ twistedConjStabilizer σ δ s ↔
      Vertex.act t (Vertex.act s (stdVertex R K)) = Vertex.act s (stdVertex R K) := by
  obtain ⟨hT, w, hw⟩ := (mem_twistedUnitCentralizer_iff σ δ t).1 ht
  have hdet : Matrix.det ((s⁻¹ * t * s : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K w :=
    (det_coe_conj s t).trans hw
  have hact : Vertex.act t (Vertex.act s (stdVertex R K)) = Vertex.act s (stdVertex R K) ↔
      Vertex.act (s⁻¹ * t * s) (stdVertex R K) = stdVertex R K := by
    rw [Vertex.act_mul, Vertex.act_mul, act_eq_iff s⁻¹, inv_inv]
  rw [mem_twistedConjStabilizer_iff_range, hact, Vertex.act_stdVertex_eq_iff]
  constructor
  · rintro ⟨-, hm⟩
    exact ⟨1, by rw [scalarGL_one, one_mul]; exact hm⟩
  · rintro ⟨c, hc⟩
    exact ⟨hT, mem_range_of_scalarGL_mul hdet hc⟩

private theorem relIndex_twistedConjStabilizer_ne_zero_of_stable [TopologicalSpace K] [IsTopologicalRing K]
    (hT : IsClosed (sigmaCentralizer σ.mapGL δ : Set (Matrix.GeneralLinearGroup (Fin 2) K)))
    (hUc : IsCompact (integralUnitsSet (Set.range (algebraMap R K))))
    (hUo : IsOpen (integralUnitsSet (Set.range (algebraMap R K))))
    {F : Set (Vertex R K)} (hF : F.Finite) (hne : F.Nonempty)
    (hstab : ∀ t ∈ twistedUnitCentralizer σ δ, ∀ x ∈ F, Vertex.act t x ∈ F) (s : Matrix.GeneralLinearGroup (Fin 2) K) :
    (twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨g₀, rfl⟩ := exists_act_stdVertex_eq x₀

  have h₁ : (twistedConjStabilizer σ δ g₀).relIndex (twistedUnitCentralizer σ δ) ≠ 0 := by
    letI : MulAction (Matrix.GeneralLinearGroup (Fin 2) K) (Vertex R K) :=
      { smul := Vertex.act
        one_smul := Vertex.act_one
        mul_smul := Vertex.act_mul }
    set x₀ := Vertex.act g₀ (stdVertex R K)
    have horbit : MulAction.orbit (twistedUnitCentralizer σ δ) x₀ ⊆ F := by
      rintro _ ⟨t, rfl⟩
      change Vertex.act (t : Matrix.GeneralLinearGroup (Fin 2) K) x₀ ∈ F
      exact hstab t t.2 x₀ hx₀
    have hidx : (MulAction.stabilizer (twistedUnitCentralizer σ δ) x₀).index ≠ 0 := by
      rw [MulAction.index_stabilizer]
      exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self x₀) (hF.subset horbit)
    have hstab' : MulAction.stabilizer (twistedUnitCentralizer σ δ) x₀ =
        (twistedConjStabilizer σ δ g₀).subgroupOf (twistedUnitCentralizer σ δ) := by
      ext t
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_twistedConjStabilizer_iff_act_eq σ δ t.2]
      exact Iff.rfl
    rw [hstab'] at hidx
    exact hidx

  have h₂ : (twistedConjStabilizer σ δ s).relIndex (twistedConjStabilizer σ δ g₀) ≠ 0 := by
    haveI : CompactSpace (twistedConjStabilizer σ δ g₀) :=
      isCompact_iff_compactSpace.1 (isCompact_twistedConjStabilizer σ δ hT hUc g₀)
    have hopen : IsOpen (((twistedConjStabilizer σ δ s).subgroupOf (twistedConjStabilizer σ δ g₀) :
        Subgroup (twistedConjStabilizer σ δ g₀)) : Set (twistedConjStabilizer σ δ g₀)) := by
      have hset : (((twistedConjStabilizer σ δ s).subgroupOf (twistedConjStabilizer σ δ g₀) :
          Subgroup (twistedConjStabilizer σ δ g₀)) : Set (twistedConjStabilizer σ δ g₀)) =
            (fun t : twistedConjStabilizer σ δ g₀ => s⁻¹ * (t : Matrix.GeneralLinearGroup (Fin 2) K) * s) ⁻¹'
              integralUnitsSet (Set.range (algebraMap R K)) := by
        ext t
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_twistedConjStabilizer_iff, Set.mem_preimage]
        exact ⟨fun h => h.2, fun h => ⟨((mem_twistedConjStabilizer_iff_range σ δ g₀ _).1 t.2).1, h⟩⟩
      rw [hset]
      exact hUo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    haveI := Subgroup.quotient_finite_of_isOpen _ hopen
    show ((twistedConjStabilizer σ δ s).subgroupOf (twistedConjStabilizer σ δ g₀)).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_ne_zero_trans (hHK := h₂) (hKL := h₁)

private theorem relIndex_twistedConjStabilizer_ne_zero [TopologicalSpace K] [IsTopologicalRing K]
    (hT : IsClosed (sigmaCentralizer σ.mapGL δ : Set (Matrix.GeneralLinearGroup (Fin 2) K)))
    (hUc : IsCompact (integralUnitsSet (Set.range (algebraMap R K))))
    (hUo : IsOpen (integralUnitsSet (Set.range (algebraMap R K))))
    (hfix : twistedUnitOrbitalCount δ σ ≠ 0) (s : Matrix.GeneralLinearGroup (Fin 2) K) :
    (twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) ≠ 0 := by
  have hfix' : Nat.card (twistedFixedVertexSet δ σ) ≠ 0 := hfix
  obtain ⟨⟨⟨x₀, hx₀⟩⟩, hfin⟩ := Nat.card_ne_zero.1 hfix'
  haveI := hfin
  refine relIndex_twistedConjStabilizer_ne_zero_of_stable σ δ hT hUc hUo (Set.toFinite _) ⟨x₀, hx₀⟩ ?_ s
  intro t ht x hx
  rw [mem_twistedFixedVertexSet] at hx ⊢
  rw [twistedAct_act_of_mem σ δ (twistedUnitCentralizer_le σ δ ht), hx]

end Twisted

section IndexSums

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq AutomorphicForm"
open scoped Pointwise

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]
variable (σ : IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K) (ϖ : R)

open scoped Classical in

private theorem card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_filter (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ) [Finite
    (R ⧸ Ideal.span {ϖ})] (b : ℤ)
    (n : ℕ) (hn : 1 ≤ n) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ (2 * b + (n : ℤ)))
    (dl : Matrix.GeneralLinearGroup (Fin 2) K)
    (hdl : (dl : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![algebraMap R K ϖ ^ (b + (n : ℤ)), algebraMap R K ϖ ^ b])
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ sigmaCentralizer σ.mapGL δ, ∀ u ∈ integralUnitsSet (Set.range (algebraMap R K)),
        s' = t * s * u → s' = s)
    (hcov : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K, x⁻¹ * δ *
        σ.mapGL x ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)) →
      ∃ s ∈ S, ∃ t ∈ sigmaCentralizer σ.mapGL δ, ∃ u ∈ integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u) :
    Nat.card
        ↥(twistedOrbitalBall (unitOfNeZero (K := K) hϖ.ne_zero) n δ σ \
          twistedOrbitalBall (unitOfNeZero (K := K) hϖ.ne_zero) (n - 1) δ σ) =
      (twistedUnitCentralizer σ δ ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex (sigmaCentralizer
          σ.mapGL δ) *
        ∑ s ∈ S with s⁻¹ * δ * σ.mapGL s ∈ integralUnitsSet (Set.range (algebraMap R K)) *
            ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)),
          (twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) := by
  refine card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow R K σ ϖ hϖ hσϖ δ b n hn u hdet
    dl hdl (twistedUnitCentralizer σ δ) (mem_twistedUnitCentralizer_iff σ δ) (twistedConjStabilizer σ δ)
    (mem_twistedConjStabilizer_iff σ δ) (S.filter fun s => s⁻¹ * δ *
        σ.mapGL s ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)))
    (fun s hs => (Finset.mem_filter.1 hs).2) ?_ ?_
  · intro s hs s' hs' t ht u hu h
    exact hS s (Finset.mem_filter.1 hs).1 s' (Finset.mem_filter.1 hs').1 t ht u hu h
  · intro x hx
    obtain ⟨s, hs, t, ht, u, hu, rfl⟩ := hcov x hx
    exact ⟨s, Finset.mem_filter.2 ⟨hs, twistedConj_mem_of_eq_mul σ δ ht hu rfl hx⟩, t, ht, u, hu, rfl⟩

private theorem relIndex_sup_center_ne_zero_of_card_ne_zero (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ) [Finite (R ⧸
    Ideal.span {ϖ})] (b : ℤ) (n : ℕ)
    (hn : 1 ≤ n) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ (2 * b + (n : ℤ)))
    (dl : Matrix.GeneralLinearGroup (Fin 2) K)
    (hdl : (dl : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![algebraMap R K ϖ ^ (b + (n : ℤ)), algebraMap R K ϖ ^ b])
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ sigmaCentralizer σ.mapGL δ, ∀ u ∈ integralUnitsSet (Set.range (algebraMap R K)),
        s' = t * s * u → s' = s)
    (hcov : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K, x⁻¹ * δ *
        σ.mapGL x ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)) →
      ∃ s ∈ S, ∃ t ∈ sigmaCentralizer σ.mapGL δ, ∃ u ∈ integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u)
    (hcard : Nat.card
        ↥(twistedOrbitalBall (unitOfNeZero (K := K) hϖ.ne_zero) n δ σ \
          twistedOrbitalBall (unitOfNeZero (K := K) hϖ.ne_zero) (n - 1) δ σ) ≠ 0) :
    (twistedUnitCentralizer σ δ ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex (sigmaCentralizer
        σ.mapGL δ) ≠ 0 := by
  classical
  rw [card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_filter σ δ ϖ hϖ hσϖ b n hn u hdet dl hdl S hS hcov] at hcard
  exact left_ne_zero_of_mul hcard

open scoped Classical in

private theorem twistedUnitOrbitalCount_eq_relIndex_mul_sum_filter (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ) [Finite (R ⧸
    Ideal.span {ϖ})] (b : ℤ) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ (2 * b))
    (dl : Matrix.GeneralLinearGroup (Fin 2) K)
    (hdl : (dl : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap R K ϖ ^ b, algebraMap R K ϖ ^ b])
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ sigmaCentralizer σ.mapGL δ, ∀ u ∈ integralUnitsSet (Set.range (algebraMap R K)),
        s' = t * s * u → s' = s)
    (hcov : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K, x⁻¹ * δ *
        σ.mapGL x ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)) →
      ∃ s ∈ S, ∃ t ∈ sigmaCentralizer σ.mapGL δ, ∃ u ∈ integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u) :
    twistedUnitOrbitalCount δ σ =
      (twistedUnitCentralizer σ δ ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex (sigmaCentralizer
          σ.mapGL δ) *
        ∑ s ∈ S with s⁻¹ * δ * σ.mapGL s ∈ integralUnitsSet (Set.range (algebraMap R K)) *
            ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)),
          (twistedConjStabilizer σ δ s).relIndex (twistedUnitCentralizer σ δ) := by
  set e : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero ^ (-b) with he
  have hcent : sigmaCentralizer σ.mapGL (scalarGL e * δ) = sigmaCentralizer σ.mapGL δ :=
    sigmaCentralizer_scalarGL_mul σ δ e

  have hdet' : Matrix.det ((scalarGL e *
      δ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u := by
    rw [Units.val_mul, Matrix.det_mul, scalarGL_coe, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, hdet,
      he, Units.val_zpow_eq_zpow_val, unitOfNeZero_coe, ← zpow_natCast, ← zpow_mul, ← mul_assoc]
    have hne : algebraMap R K ϖ ≠ 0 := (unitOfNeZero (K := K) hϖ.ne_zero).ne_zero
    have h0 : -b * ((2 : ℕ) : ℤ) + 2 * b = 0 := by push_cast; ring
    rw [mul_right_comm, ← zpow_add₀ hne, h0, zpow_zero, one_mul]

  have hconj : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K, x⁻¹ * (scalarGL e * δ) * σ.mapGL x = scalarGL e * (x⁻¹ *
      δ * σ.mapGL x) := by
    intro x
    rw [← mul_assoc x⁻¹ (scalarGL e) δ, ← scalarGL_mul_comm e x⁻¹]
    simp only [mul_assoc]
  have key := twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap R K σ ϖ hϖ hσϖ
    (scalarGL e * δ) u hdet' (twistedUnitCentralizer σ δ)
    (fun t => by rw [mem_twistedUnitCentralizer_iff, hcent]) (twistedConjStabilizer σ δ)
    (fun s t => by rw [mem_twistedConjStabilizer_iff, hcent])
    (S.filter fun s => s⁻¹ * δ * σ.mapGL s ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)))
    (fun s hs => by
      rw [hconj]
      exact (scalarGL_zpow_mul_mem_iff ϖ hϖ b dl hdl _).2 (Finset.mem_filter.1 hs).2)
    (fun s hs s' hs' t ht u hu h => by
      rw [hcent] at ht
      exact hS s (Finset.mem_filter.1 hs).1 s' (Finset.mem_filter.1 hs').1 t ht u hu h)
    (fun x hx => by
      rw [hconj, scalarGL_zpow_mul_mem_iff ϖ hϖ b dl hdl] at hx
      obtain ⟨s, hs, t, ht, u, hu, rfl⟩ := hcov x hx
      refine ⟨s, Finset.mem_filter.2 ⟨hs, twistedConj_mem_of_eq_mul σ δ ht hu rfl hx⟩, t, ?_, u, hu, rfl⟩
      rwa [hcent])
  rw [TwistedTreeTransport.twistedUnitOrbitalCount_scalarGL_mul, hcent] at key
  exact key

private theorem relIndex_sup_center_ne_zero_of_twistedUnitOrbitalCount_ne_zero (hϖ : Irreducible ϖ) (hσϖ : σ.toBase ϖ = ϖ)
    [Finite (R ⧸ Ideal.span {ϖ})]
    (b : ℤ) (u : Rˣ)
    (hdet : Matrix.det (δ : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ (2 * b))
    (dl : Matrix.GeneralLinearGroup (Fin 2) K)
    (hdl : (dl : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap R K ϖ ^ b, algebraMap R K ϖ ^ b])
    (S : Finset (Matrix.GeneralLinearGroup (Fin 2) K))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ sigmaCentralizer σ.mapGL δ, ∀ u ∈ integralUnitsSet (Set.range (algebraMap R K)),
        s' = t * s * u → s' = s)
    (hcov : ∀ x : Matrix.GeneralLinearGroup (Fin 2) K, x⁻¹ * δ *
        σ.mapGL x ∈ integralUnitsSet (Set.range (algebraMap R K)) *
        ({dl} : Set (Matrix.GeneralLinearGroup (Fin 2) K)) * integralUnitsSet (Set.range (algebraMap R K)) →
      ∃ s ∈ S, ∃ t ∈ sigmaCentralizer σ.mapGL δ, ∃ u ∈ integralUnitsSet (Set.range (algebraMap R K)), x = t * s * u)
    (hfix : twistedUnitOrbitalCount δ σ ≠ 0) :
    (twistedUnitCentralizer σ δ ⊔ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)).relIndex (sigmaCentralizer
        σ.mapGL δ) ≠ 0 := by
  classical
  rw [twistedUnitOrbitalCount_eq_relIndex_mul_sum_filter σ δ ϖ hϖ hσϖ b u hdet dl hdl S hS hcov] at hfix
  exact left_ne_zero_of_mul hfix

end IndexSums

section Place

open NumberField IsDedekindDomain AutomorphicForm

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem algebraMap_self_mem (x : u.adicCompletionIntegers F) :
    algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) x ∈ u.adicCompletionIntegers F := x.2

private theorem range_algebraMap_eq :
    Set.range (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)) =
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact algebraMap_self_mem F u a
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem integralUnitsSet_range_eq_localIntegralSet :
    integralUnitsSet (Set.range (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F))) =
      localIntegralSet F u := by
  rw [range_algebraMap_eq]
  rfl

private theorem isCompact_integralUnitsSet_range :
    IsCompact (integralUnitsSet (Set.range (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)))) := by
  rw [integralUnitsSet_range_eq_localIntegralSet]
  exact isCompact_localIntegralSet F u

private theorem isOpen_integralUnitsSet_range :
    IsOpen (integralUnitsSet (Set.range (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)))) := by
  rw [integralUnitsSet_range_eq_localIntegralSet]
  exact isOpen_localIntegralSet F u

end Place

end TwistedTorusIndices

namespace TwistedValues

open NumberField IsDedekindDomain AutomorphicForm MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

section Values

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

private noncomputable def twistedRealisedValue (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) : ℂ :=
  ∑ s ∈ S, φ (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s) /
    ((τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v}).toReal : ℂ)

private theorem twistedRealisedValue_add (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :
    twistedRealisedValue K L v σ δ τ' (φ + ψ) S =
      twistedRealisedValue K L v σ δ τ' φ S + twistedRealisedValue K L v σ δ τ' ψ S := by
  simp only [twistedRealisedValue, Pi.add_apply, add_div, Finset.sum_add_distrib]

private theorem twistedRealisedValue_smul (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (c : ℂ) (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :
    twistedRealisedValue K L v σ δ τ' (c • φ) S = c * twistedRealisedValue K L v σ δ τ' φ S := by
  simp only [twistedRealisedValue, Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

private theorem exists_isTwistedOrbitalIntegralOn (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    {φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ semiLocalIntegralSet K L v, ∀ u₂ ∈ semiLocalIntegralSet K L v, φ (u₁ * g * u₂) = φ g)
    (hφs : ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g, φ g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ semiLocalIntegralSet K L v) :
    ∃ I, IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I := by
  obtain ⟨S, hS, hcov⟩ :=
    exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ φ hφs
  exact ⟨_, isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ' φ hφ
    S hS hcov⟩

private theorem twistedRealisedValue_indicator (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (D : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    [DecidablePred fun s : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s ∈ D]
    (ι : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℕ) (m : ℝ) (hm : m ≠ 0)
    (hidx : ∀ s ∈ S, (ι s : ℝ) *
      (τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v}).toReal = m) :
    twistedRealisedValue K L v σ δ τ' (D.indicator 1) S =
      (∑ s ∈ S with s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s ∈ D, (ι s : ℂ)) / (m : ℂ) := by
  rw [twistedRealisedValue, Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  split_ifs with h
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    have hidxs := hidx s hs
    have hτ0 : (τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈
        semiLocalIntegralSet K L v}).toReal ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hidxs
      exact hm hidxs.symm
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hm), div_mul_eq_mul_div, one_mul,
      div_eq_iff (Complex.ofReal_ne_zero.mpr hτ0), ← hidxs, Complex.ofReal_mul, Complex.ofReal_natCast]
  · rw [Set.indicator_of_notMem h, zero_div]

variable [FiniteDimensional K L]

private theorem twistedOrbitalIntegral_add (hσn : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    {φ ψ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ semiLocalIntegralSet K L v, ∀ u₂ ∈ semiLocalIntegralSet K L v, φ (u₁ * g * u₂) = φ g)
    (hψ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ semiLocalIntegralSet K L v, ∀ u₂ ∈ semiLocalIntegralSet K L v, ψ (u₁ * g * u₂) = ψ g)
    (hφs : ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g, φ g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ semiLocalIntegralSet K L v)
    (hψs : ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g, ψ g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ semiLocalIntegralSet K L v)
    (hφm : Measurable[glBorelOf (L ⊗[K] v.adicCompletion K)] φ)
    (hψm : Measurable[glBorelOf (L ⊗[K] v.adicCompletion K)] ψ)
    (hφb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (hψb : ∃ C : ℝ, ∀ g, ‖ψ g‖ ≤ C)
    {I J M : ℂ} (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I)
    (hJ : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' ψ J)
    (hM : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (φ + ψ) M) :
    M = I + J := by
  classical
  obtain ⟨F₀, hF₀⟩ := hφs
  obtain ⟨G₀, hG₀⟩ := hψs

  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => if φ y ≠ 0 ∨ ψ y ≠ 0 then (1 : ℂ) else 0)
    ⟨F₀ ∪ G₀, fun y hy => by
      by_cases hy' : φ y ≠ 0 ∨ ψ y ≠ 0
      · rcases hy' with hy' | hy'
        · obtain ⟨c, hc, hcy⟩ := hF₀ y hy'
          exact ⟨c, Finset.mem_union_left _ hc, hcy⟩
        · obtain ⟨c, hc, hcy⟩ := hG₀ y hy'
          exact ⟨c, Finset.mem_union_right _ hc, hcy⟩
      · exact (hy (if_neg hy')).elim⟩
  have hcovφ : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K), φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
      ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
        ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u :=
    fun x hx => hcov x (by rw [if_pos (Or.inl hx)]; exact one_ne_zero)
  have hcovψ : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K), ψ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
      ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
        ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u :=
    fun x hx => hcov x (by rw [if_pos (Or.inr hx)]; exact one_ne_zero)
  have hcovφψ : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (φ + ψ) (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u := by
    intro x hx
    refine hcov x ?_
    have hor : φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 ∨
        ψ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hx (by rw [Pi.add_apply, hno.1, hno.2, add_zero])
    rw [if_pos hor]
    exact one_ne_zero
  have hφψ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ semiLocalIntegralSet K L v, ∀ u₂ ∈ semiLocalIntegralSet K L v, (φ + ψ) (u₁ * g * u₂) = (φ + ψ) g :=
    fun g u₁ hu₁ u₂ hu₂ => by rw [Pi.add_apply, Pi.add_apply, hφ g u₁ hu₁ u₂ hu₂, hψ g u₁ hu₁ u₂ hu₂]
  have h1 := isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ' φ hφ S
    hS hcovφ
  have h2 := isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ' ψ hψ S
    hS hcovψ
  have h3 := isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ' (φ + ψ)
    hφψ S hS hcovφψ
  have hφψb : ∃ C : ℝ, ∀ g, ‖(φ + ψ) g‖ ≤ C := by
    obtain ⟨Cφ, hCφ⟩ := hφb
    obtain ⟨Cψ, hCψ⟩ := hψb
    exact ⟨Cφ + Cψ, fun g => (norm_add_le _ _).trans (add_le_add (hCφ g) (hCψ g))⟩
  rw [IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ' (φ + ψ) (hφm.add hψm) hφψb hM h3,
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ' φ hφm hφb hI h1,
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ' ψ hψm hψb hJ h2]
  simp only [Pi.add_apply, add_div, Finset.sum_add_distrib]

private theorem twistedOrbitalIntegral_smul (hσn : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    {φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ} (c : ℂ)
    (hφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ semiLocalIntegralSet K L v, ∀ u₂ ∈ semiLocalIntegralSet K L v, φ (u₁ * g * u₂) = φ g)
    (hφs : ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g, φ g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ semiLocalIntegralSet K L v)
    (hφm : Measurable[glBorelOf (L ⊗[K] v.adicCompletion K)] φ) (hφb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C)
    {I M : ℂ} (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φ I)
    (hM : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (c • φ) M) :
    M = c * I := by
  classical
  obtain ⟨S, hS, hcov⟩ :=
    exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ φ hφs
  have hcovc : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (c • φ) (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u :=
    fun x hx => hcov x (right_ne_zero_of_mul hx)
  have hcφ : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ u₁ ∈ semiLocalIntegralSet K L v, ∀ u₂ ∈ semiLocalIntegralSet K L v, (c • φ) (u₁ * g * u₂) = (c • φ) g :=
    fun g u₁ hu₁ u₂ hu₂ => by rw [Pi.smul_apply, Pi.smul_apply, hφ g u₁ hu₁ u₂ hu₂]
  have h1 := isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ' φ hφ S
    hS hcov
  have h2 := isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ' (c • φ)
    hcφ S hS hcovc
  have hcφb : ∃ C : ℝ, ∀ g, ‖(c • φ) g‖ ≤ C := by
    obtain ⟨C, hC⟩ := hφb
    exact ⟨‖c‖ * C, fun g => by
      rw [Pi.smul_apply, norm_smul]
      exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)⟩
  rw [IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ' (c • φ) (hφm.const_smul c) hcφb hM h2,
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ' φ hφm hφb hI h1]
  simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

end Values

end TwistedValues

namespace CoupledTransport

open TensorProduct
open scoped TensorProduct.RightActions

section Commutant

variable {R : Type} [CommRing R]

private theorem exists_eq_smul_one_add_smul_of_commute (g m : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) :
    ∃ x y : R, m = x • (1 : Matrix (Fin 2) (Fin 2) R) + y • g := by
  obtain ⟨u, hu⟩ := hg
  have hinv : (↑u⁻¹ : R) * ((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) = 1 := by
    have h := u.inv_mul
    rwa [hu, Matrix.trace_fin_two, Matrix.det_fin_two] at h
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨m 0 0 - (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)) * g 0 0,
    (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, if_true, if_false, mul_one, mul_zero, zero_add, one_ne_zero,
    zero_ne_one]
  · ring
  · linear_combination (-(m 0 1)) * hinv + (-((↑u⁻¹ : R) * (g 0 0 - g 1 1))) * h01 + (2 * (↑u⁻¹ : R) * g 0 1) * h00
  · linear_combination (-(m 1 0)) * hinv + ((↑u⁻¹ : R) * (g 0 0 - g 1 1)) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h00
  · linear_combination (m 0 0 - m 1 1) * hinv + (2 * (↑u⁻¹ : R) * g 0 1) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h01

private theorem commute_of_commute_of_commute {g m m' : Matrix (Fin 2) (Fin 2) R}
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) (hm' : m' * g = g * m') : m * m' = m' * m := by
  obtain ⟨x, y, rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m hg hm
  obtain ⟨x', y', rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m' hg hm'
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

end Commutant

section Twist

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

open AutomorphicForm

private theorem coe_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    (sigmaGL K L A σ x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (sigmaTensor K L A σ) := by
  ext i j
  rfl

private theorem coe_toTensorGL (t₀ : GL (Fin 2) A) :
    (toTensorGL K L A t₀ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (t₀ : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) := by
  ext i j
  rfl

private theorem sigmaTensor_algebraMap (a : A) :
    sigmaTensor K L A σ (algebraMap A (L ⊗[K] A) a) = algebraMap A (L ⊗[K] A) a := by
  simp [sigmaTensor, TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.map_tmul]

private theorem sigmaGL_toTensorGL (t₀ : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A t₀) = toTensorGL K L A t₀ := by
  apply Units.ext
  rw [coe_sigmaGL, coe_toTensorGL, Matrix.map_map]
  ext i j
  exact sigmaTensor_algebraMap σ _

private theorem iterate_sigmaGL_eq_self (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    (x : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x :=
  LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self hσn x

private theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) δ :=
  (LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range (sigmaGL K L A σ) δ (Module.finrank K L)).symm

private theorem isNormConjugator_one_of_isNormConjugator
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {γ : GL (Fin 2) A}
    {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y) :
    IsNormConjugator K L A σ γ (y⁻¹ * δ * sigmaGL K L A σ y) 1 := by
  unfold IsNormConjugator at hy ⊢
  rw [inv_one, one_mul, mul_one, normString_eq_sigmaNormPow,
    LT.TwistedNorm.sigmaNormPow_sigmaConjElt _ _ (iterate_sigmaGL_eq_self σ hσn y), ← normString_eq_sigmaNormPow, hy]

private theorem commute_normString_of_mem_twistedCentralizer
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {δ t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) : t * normString K L A σ δ = normString K L A σ δ * t := by
  have h1 : t⁻¹ * δ * sigmaGL K L A σ t = δ := mem_sigmaCentralizer_iff_inv.1 ht
  have key := LT.TwistedNorm.sigmaNormPow_sigmaConjElt (sigmaGL K L A σ) (Module.finrank K L)
    (iterate_sigmaGL_eq_self σ hσn t) δ
  rw [h1] at key
  rw [normString_eq_sigmaNormPow]
  conv_lhs => rw [key]
  group

private theorem commute_toTensorGL_of_isNormConjugator_one
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {γ : GL (Fin 2) A}
    {δ : GL (Fin 2) (L ⊗[K] A)} (hN : IsNormConjugator K L A σ γ δ 1) :
    δ * toTensorGL K L A γ = toTensorGL K L A γ * δ := by
  unfold IsNormConjugator at hN
  rw [inv_one, one_mul, mul_one] at hN
  have key := LT.TwistedNorm.map_sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L)
    (iterate_sigmaGL_eq_self σ hσn δ)
  rw [← normString_eq_sigmaNormPow, ← hN, sigmaGL_toTensorGL] at key
  conv_lhs => rw [key]
  group

private theorem isUnit_disc_toTensorGL {γ : GL (Fin 2) A} (hγ : IsRegularSemisimple γ) :
    IsUnit ((toTensorGL K L A γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace ^ 2 -
      4 * (toTensorGL K L A γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det) := by
  unfold IsRegularSemisimple at hγ
  have h : (toTensorGL K L A γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace ^ 2 -
      4 * (toTensorGL K L A γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
        algebraMap A (L ⊗[K] A)
          ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det) := by
    simp only [coe_toTensorGL, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.map_apply, map_sub, map_mul, map_pow,
      map_add, map_ofNat]
  rw [h]
  exact hγ.map _

private theorem twistedCentralizer_eq_map_centralizer_of_fixed_range
    (hfixK : ∀ z : L ⊗[K] A, sigmaTensor K L A σ z = z → z ∈ Set.range (algebraMap A (L ⊗[K] A)))
    (hinj : Function.Injective (algebraMap A (L ⊗[K] A)))
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {γ : GL (Fin 2) A}
    (hγ : IsRegularSemisimple γ) {δ : GL (Fin 2) (L ⊗[K] A)} (hN : IsNormConjugator K L A σ γ δ 1) :
    twistedCentralizer K L A σ δ = (Subgroup.centralizer {γ}).map (toTensorGL K L A) := by
  have hdisc := isUnit_disc_toTensorGL (K := K) (L := L) hγ
  have hδγ : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * toTensorGL K L A γ = toTensorGL K L A γ * δ := by
    rw [← Units.val_mul, ← Units.val_mul, commute_toTensorGL_of_isNormConjugator_one σ hσn hN]
  have hNγ : normString K L A σ δ = toTensorGL K L A γ := by
    unfold IsNormConjugator at hN
    rwa [inv_one, one_mul, mul_one, eq_comm] at hN
  ext t
  constructor
  · intro ht

    have htγ : (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * toTensorGL K L A γ = toTensorGL K L A γ * t := by
      rw [← Units.val_mul, ← Units.val_mul, ← hNγ, commute_normString_of_mem_twistedCentralizer σ hσn ht]
    have htδ : t * δ = δ * t :=
      Units.ext (commute_of_commute_of_commute hdisc htγ hδγ)
    have hfix : sigmaGL K L A σ t = t := by
      have h1 : t⁻¹ * δ * sigmaGL K L A σ t = δ := mem_sigmaCentralizer_iff_inv.1 ht
      have h2 : sigmaGL K L A σ t = δ⁻¹ * (t * δ) := by
        calc sigmaGL K L A σ t = δ⁻¹ * (t * (t⁻¹ * δ * sigmaGL K L A σ t)) := by group
          _ = δ⁻¹ * (t * δ) := by rw [h1]
      rw [h2, htδ, inv_mul_cancel_left]
    have hfixed : ∀ x : GL (Fin 2) (L ⊗[K] A), sigmaGL K L A σ x = x →
        ∀ i j, ∃ a : A, algebraMap A (L ⊗[K] A) a = (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j := by
      intro x hx i j
      have hij := congrArg (fun z : GL (Fin 2) (L ⊗[K] A) => (z : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) hx
      simp only [coe_sigmaGL, Matrix.map_apply] at hij
      exact Set.mem_range.1 (hfixK _ hij)
    have hfix' : sigmaGL K L A σ t⁻¹ = t⁻¹ := by rw [map_inv, hfix]
    choose a ha using hfixed t hfix
    choose b hb using hfixed t⁻¹ hfix'
    have hamap : (Matrix.of a).map (algebraMap A (L ⊗[K] A)) = (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
      ext i j; exact ha i j
    have hbmap : (Matrix.of b).map (algebraMap A (L ⊗[K] A)) =
        ((t⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
      ext i j; exact hb i j
    have hmapinj : Function.Injective fun M : Matrix (Fin 2) (Fin 2) A => M.map (algebraMap A (L ⊗[K] A)) := by
      intro M N h
      ext i j
      exact hinj (congrFun (congrFun h i) j)
    have hab : Matrix.of a * Matrix.of b = 1 := by
      apply hmapinj
      simp only [Matrix.map_mul, hamap, hbmap, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hba : Matrix.of b * Matrix.of a = 1 := by
      apply hmapinj
      simp only [Matrix.map_mul, hamap, hbmap, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨⟨Matrix.of a, Matrix.of b, hab, hba⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      apply Units.ext
      apply hmapinj
      simp only [Units.val_mul, Matrix.map_mul, hamap]
      rw [← coe_toTensorGL]
      exact htγ.symm
    · apply Units.ext
      rw [coe_toTensorGL]
      exact hamap
  · rintro ⟨t₀, ht₀, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at ht₀
    have hγt₀ : γ * t₀ = t₀ * γ := ht₀ γ (Set.mem_singleton γ)
    have htγ : ((toTensorGL K L A t₀ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
        toTensorGL K L A γ = toTensorGL K L A γ * (toTensorGL K L A t₀ : GL (Fin 2) (L ⊗[K] A)) := by
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hγt₀]
    have htδ : toTensorGL K L A t₀ * δ = δ * toTensorGL K L A t₀ :=
      Units.ext (commute_of_commute_of_commute hdisc htγ hδγ)
    refine mem_sigmaCentralizer_iff_inv.2 ?_
    rw [sigmaGL_toTensorGL, mul_assoc, ← htδ, inv_mul_cancel_left]

end Twist

section Descent

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

open AutomorphicForm

private theorem toTensorGL_injective (hinj : Function.Injective (algebraMap A (L ⊗[K] A))) :
    Function.Injective (toTensorGL K L A) := by
  intro s t h
  have h' := congrArg (fun x : GL (Fin 2) (L ⊗[K] A) => (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) h
  simp only [coe_toTensorGL] at h'
  apply Units.ext
  ext i j
  exact hinj (congrFun (congrFun h' i) j)

private theorem det_toTensorGL (t₀ : GL (Fin 2) A) :
    (toTensorGL K L A t₀ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      algebraMap A (L ⊗[K] A) (t₀ : Matrix (Fin 2) (Fin 2) A).det := by
  rw [coe_toTensorGL, RingHom.map_det, RingHom.mapMatrix_apply]

private theorem mem_twistedCentralizer_and_det_mem_iff
    (hfixK : ∀ z : L ⊗[K] A, sigmaTensor K L A σ z = z → z ∈ Set.range (algebraMap A (L ⊗[K] A)))
    (hinj : Function.Injective (algebraMap A (L ⊗[K] A)))
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {γ : GL (Fin 2) A}
    (hγ : IsRegularSemisimple γ) {δ : GL (Fin 2) (L ⊗[K] A)} (hN : IsNormConjugator K L A σ γ δ 1)
    {Dset : Set (L ⊗[K] A)} {D : Set A} (hD : ∀ d : A, algebraMap A (L ⊗[K] A) d ∈ Dset ↔ d ∈ D)
    (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ twistedCentralizer K L A σ δ ∧ (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det ∈ Dset ↔
      ∃ t₀ ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
        (t₀ : Matrix (Fin 2) (Fin 2) A).det ∈ D ∧ toTensorGL K L A t₀ = t := by
  rw [twistedCentralizer_eq_map_centralizer_of_fixed_range σ hfixK hinj hσn hγ hN, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨t₀, ht₀, rfl⟩, hdet⟩
    refine ⟨t₀, ht₀, ?_, rfl⟩
    rwa [det_toTensorGL, hD] at hdet
  · rintro ⟨t₀, ht₀, hdet, rfl⟩
    exact ⟨⟨t₀, ht₀, rfl⟩, by rw [det_toTensorGL, hD]; exact hdet⟩

private theorem center_inf_twistedCentralizer_eq
    (hfixK : ∀ z : L ⊗[K] A, sigmaTensor K L A σ z = z → z ∈ Set.range (algebraMap A (L ⊗[K] A)))
    (hinj : Function.Injective (algebraMap A (L ⊗[K] A)))
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {γ : GL (Fin 2) A}
    (hγ : IsRegularSemisimple γ) {δ : GL (Fin 2) (L ⊗[K] A)} (hN : IsNormConjugator K L A σ γ δ 1) :
    Subgroup.center (GL (Fin 2) (L ⊗[K] A)) ⊓ twistedCentralizer K L A σ δ =
      (Subgroup.center (GL (Fin 2) A)).map (toTensorGL K L A) := by
  rw [twistedCentralizer_eq_map_centralizer_of_fixed_range σ hfixK hinj hσn hγ hN]
  ext t
  simp only [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hz, t₀, -, rfl⟩
    refine ⟨t₀, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply toTensorGL_injective hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hz (toTensorGL K L A g)
  · rintro ⟨t₀, ht₀, rfl⟩
    refine ⟨?_, t₀, Subgroup.center_le_centralizer _ ht₀, rfl⟩
    obtain ⟨r, hr⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 ht₀
    refine Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 ⟨algebraMap A (L ⊗[K] A) r, ?_⟩
    show _ = (toTensorGL K L A t₀ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
    rw [coe_toTensorGL, ← hr, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

private theorem relIndex_sup_center_eq
    (hfixK : ∀ z : L ⊗[K] A, sigmaTensor K L A σ z = z → z ∈ Set.range (algebraMap A (L ⊗[K] A)))
    (hinj : Function.Injective (algebraMap A (L ⊗[K] A)))
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {γ : GL (Fin 2) A}
    (hγ : IsRegularSemisimple γ) {δ : GL (Fin 2) (L ⊗[K] A)} (hN : IsNormConjugator K L A σ γ δ 1)
    {Tc : Subgroup (GL (Fin 2) A)} (hTc : Tc ≤ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    {Tc' : Subgroup (GL (Fin 2) (L ⊗[K] A))} (hc : Tc' = Tc.map (toTensorGL K L A)) :
    (Tc' ⊔ Subgroup.center (GL (Fin 2) (L ⊗[K] A))).relIndex (twistedCentralizer K L A σ δ) =
      (Tc ⊔ Subgroup.center (GL (Fin 2) A)).relIndex (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := by
  have hT := twistedCentralizer_eq_map_centralizer_of_fixed_range σ hfixK hinj hσn hγ hN
  have hZ := center_inf_twistedCentralizer_eq σ hfixK hinj hσn hγ hN
  have hle : Tc' ≤ twistedCentralizer K L A σ δ := by
    rw [hc, hT]
    exact Subgroup.map_mono hTc
  have hmod : (Tc' ⊔ Subgroup.center (GL (Fin 2) (L ⊗[K] A))) ⊓ twistedCentralizer K L A σ δ =
      Tc' ⊔ (Subgroup.center (GL (Fin 2) (L ⊗[K] A)) ⊓ twistedCentralizer K L A σ δ) := by
    refine le_antisymm ?_ (sup_le (le_inf le_sup_left hle) (inf_le_inf_right _ le_sup_right))
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hx' : x ∈ ((Tc' ⊔ Subgroup.center (GL (Fin 2) (L ⊗[K] A)) : Subgroup _) : Set _) := hx.1
    rw [Subgroup.mul_normal] at hx'
    obtain ⟨a, ha, z, hz, rfl⟩ := Set.mem_mul.1 hx'
    have hzT : z ∈ twistedCentralizer K L A σ δ := by
      have h := (twistedCentralizer K L A σ δ).mul_mem ((twistedCentralizer K L A σ δ).inv_mem (hle ha)) hx.2
      rwa [inv_mul_cancel_left] at h
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hz, hzT⟩))
  rw [← Subgroup.inf_relIndex_right, hmod, hZ, hc, hT, ← Subgroup.map_sup,
    Subgroup.relIndex_map_map_of_injective _ _ (toTensorGL_injective hinj)]

end Descent

section Masses

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {A : Type} [CommRing A] [Algebra K A]
  [TopologicalSpace A] (σ : L ≃ₐ[K] L)

open AutomorphicForm MeasureTheory

private theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  have hf : Continuous (algebraMap A (L ⊗[K] A)) := continuous_algebraMap A (L ⊗[K] A)
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ toTensorGL K L A) = fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A).map
        (algebraMap A (L ⊗[K] A)) := funext fun g => coe_toTensorGL g
    rw [h]
    exact Units.continuous_val.matrix_map hf
  · have h : (fun g : GL (Fin 2) A => (((toTensorGL K L A g)⁻¹ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) = fun g : GL (Fin 2) A =>
          ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) := by
      funext g
      rw [← map_inv, coe_toTensorGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map hf

private theorem measure_preimage_eq_of_coupled_one {γ : GL (Fin 2) A} {δ : GL (Fin 2) (L ⊗[K] A)}
    {τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)}
    {τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)}
    (hc : Coupled K L A σ γ δ 1 τ τ') {B : Set (GL (Fin 2) (L ⊗[K] A))}
    (hB : MeasurableSet[glBorelOf (L ⊗[K] A)] B) :
    τ' ((fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A))) ⁻¹' B) =
      τ ((fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => toTensorGL K L A (t : GL (Fin 2) A)) ⁻¹' B) := by
  unfold Coupled at hc
  simp only [inv_one, one_mul, mul_one] at hc
  letI := glBorelOf (L ⊗[K] A)
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  have h1 : Measurable fun t : twistedCentralizer K L A σ δ => (t : GL (Fin 2) (L ⊗[K] A)) :=
    continuous_subtype_val.measurable
  have h2 : Measurable fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      toTensorGL K L A (t : GL (Fin 2) A) :=
    ((continuous_toTensorGL (K := K) (L := L)).comp continuous_subtype_val).measurable
  have h := congrArg (fun μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)) => μ B) hc
  beta_reduce at h
  rwa [Measure.map_apply h1 hB, Measure.map_apply h2 hB] at h

end Masses

end CoupledTransport

namespace InertBaseChange

open NumberField IsDedekindDomain HeckePair LocalGL2 AutomorphicForm
open scoped Pointwise

section ConstantTerm

open AddMonoidAlgebra

private theorem map_rec_eq_satakePow {A B F : Type*} [Ring A] [CommRing B] [FunLike F A B] [RingHomClass F A B] (f : F)
    (s e : A) (p : ℕ → A) (h0 : p 0 = 2) (h1 : p 1 = s) (h : ∀ k, p (k + 2) = s * p (k + 1) - e * p k) :
    ∀ k : ℕ, f (p k) = satakePow k (f s) (f e)
  | 0 => by rw [h0, satakePow_zero]; exact map_ofNat f 2
  | 1 => by rw [h1, satakePow_one]
  | (k + 2) => by
      rw [h, map_sub, map_mul, map_mul, map_rec_eq_satakePow f s e p h0 h1 h k,
        map_rec_eq_satakePow f s e p h0 h1 h (k + 1), satakePow_add_two]

private theorem satakePow_add_mul {A : Type*} [CommRing A] (α β : A) :
    ∀ k : ℕ, satakePow k (α + β) (α * β) = α ^ k + β ^ k
  | 0 => by rw [satakePow_zero, pow_zero, pow_zero]; norm_num
  | 1 => by rw [satakePow_one, pow_one, pow_one]
  | (k + 2) => by
      simp only [satakePow]
      rw [satakePow_add_mul α β k, satakePow_add_mul α β (k + 1)]
      ring

private theorem constantTerm_comp_eq_of_rec {R₀ : Type*} [CommRing R₀] {HL : Type*} [Ring HL] [Algebra R₀ HL]
    {HK : Type*} [Ring HK] [Algebra R₀ HK]
    (SL : HL →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ)) (SK : HK →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ))
    (b : HL →ₐ[R₀] HK) (TL cL : HL) (TK cK EK : HK) (q Q : R₀) (n : ℕ) (hQ : Q = q ^ n)
    (hSLT : SL TL = single (1, 0) Q + single (0, 1) 1) (hSLc : SL cL = single (1, 1) 1)
    (hSKT : SK TK = single (1, 0) q + single (0, 1) 1) (hSKc : SK cK = single (1, 1) 1)
    (hE : EK = q • cK) (p : ℕ → HK) (hp0 : p 0 = 2) (hp1 : p 1 = TK)
    (hp : ∀ k : ℕ, p (k + 2) = TK * p (k + 1) - EK * p k) (hbT : b TL = p n) (hbc : b cL = cK ^ n)
    (huniq : ∀ χ₁ χ₂ : HL →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ), χ₁ TL = χ₂ TL → χ₁ cL = χ₂ cL → χ₁ = χ₂) :
    SK.comp b = (mapDomainAlgHom R₀ R₀ (n • AddMonoidHom.id (ℤ × ℤ))).comp SL := by
  have happ : ∀ x : AddMonoidAlgebra R₀ (ℤ × ℤ),
      mapDomainAlgHom R₀ R₀ (n • AddMonoidHom.id (ℤ × ℤ)) x = mapDomain (n • AddMonoidHom.id (ℤ × ℤ)) x :=
    fun _ => rfl
  have hid : ∀ a : ℤ × ℤ, (n • AddMonoidHom.id (ℤ × ℤ)) a = n • a := fun _ => rfl
  have hαβ : q • single ((1 : ℤ), (1 : ℤ)) (1 : R₀) = single (1, 0) q * single (0, 1) 1 := by
    rw [smul_single', single_mul_single, Prod.mk_add_mk, add_zero, zero_add]
  apply huniq
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, hbT, map_rec_eq_satakePow SK TK EK p hp0 hp1 hp n, hE, map_smul, hSKT,
      hSKc, hSLT, happ, mapDomain_add, mapDomain_single, mapDomain_single, hid, hid, hαβ, satakePow_add_mul,
      single_pow, single_pow, one_pow, hQ]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, hbc, map_pow, hSKc, hSLc, happ, mapDomain_single, hid,
      single_pow, one_pow]

private theorem algHom_eq_of_existsUnique {R₀ A B : Type*} [CommSemiring R₀] [Semiring A] [Algebra R₀ A]
    [Semiring B] [Algebra R₀ B] (T c : A)
    (h : ∀ (a : B) (b : Bˣ), ∃! χ : A →ₐ[R₀] B, χ T = a ∧ χ c = ↑b) (hc : IsUnit c)
    (χ₁ χ₂ : A →ₐ[R₀] B) (hT : χ₁ T = χ₂ T) (hcc : χ₁ c = χ₂ c) : χ₁ = χ₂ :=
  (h (χ₁ T) (hc.map χ₁).unit).unique ⟨rfl, (hc.map χ₁).unit_spec.symm⟩
    ⟨hT.symm, hcc.symm.trans (hc.map χ₁).unit_spec.symm⟩

end ConstantTerm

section ResidueCard

variable {K : Type*} [Field K] [NumberField K]

private theorem natCard_quot_span_eq_absNorm (v : HeightOneSpectrum (𝓞 K)) (ϖ : v.adicCompletionIntegers K)
    (hϖ : Irreducible ϖ) : Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal := by
  rw [← hϖ.maximalIdeal_eq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).symm.toEquiv

end ResidueCard

section ResidueDegree

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

open scoped TensorProduct

open scoped TensorProduct.RightActions in

private theorem _root_.InertBaseChange.finrank_adicCompletion_eq (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L := by
  rw [← e.toLinearEquiv.finrank_eq, TensorProduct.finrank_rightAlgebra]

p2m_export "InertBaseChange" "finrank_adicCompletion_eq"
private theorem asIdeal_eq_under : v.asIdeal = (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal :=
  congrArg HeightOneSpectrum.asIdeal w.2.symm

open scoped TensorProduct.RightActions in

private theorem inertiaDeg_eq_finrank (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    v.asIdeal.inertiaDeg' w.1.asIdeal = Module.finrank K L := by
  have h := HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w
  have hw' : v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := by rw [asIdeal_eq_under K L v w]; exact hw
  rwa [hw', one_mul, finrank_adicCompletion_eq K L v w e] at h

open scoped TensorProduct.RightActions in

private theorem absNorm_eq_pow (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ Module.finrank K L := by
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨asIdeal_eq_under K L v w⟩
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot,
    inertiaDeg_eq_finrank K L v w hw e]

end ResidueDegree

section Central

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]

private theorem coe_diagPi_mul_localRepInf (ϖ : R) (hϖ0 : algebraMap R F ϖ ≠ 0) :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      algebraMap R F ϖ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagPi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

private theorem diagPi_mul_localRepInf_comm (ϖ : R) (hϖ0 : algebraMap R F ϖ ≠ 0) (g : GL (Fin 2) F) :
    g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) = diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g := by
  have h : ((diagPi ϖ hϖ0 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (localRepInf ϖ hϖ0 : GL (Fin 2) F) =
      algebraMap R F ϖ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul]; exact coe_diagPi_mul_localRepInf ϖ hϖ0
  apply Units.ext
  simp only [Units.val_mul]
  rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

private theorem finite_image_mul_central (ϖ : R) (hϖ0 : algebraMap R F ϖ ≠ 0) (U : Subgroup (GL (Fin 2) F)) :
    (QuotientGroup.mk '' ((U : Set (GL (Fin 2) F)) * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) :
      Set (GL (Fin 2) F ⧸ U)).Finite := by
  refine (Set.finite_singleton (QuotientGroup.mk (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0))).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨u, hu, z, hz, rfl⟩ := Set.mem_mul.mp hx
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [Set.mem_singleton_iff, QuotientGroup.eq, diagPi_mul_localRepInf_comm ϖ hϖ0 u, mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem hu

private theorem doubleCoset_central_eq (ϖ : R) (hϖ0 : algebraMap R F ϖ ≠ 0) (U : Subgroup (GL (Fin 2) F)) :
    doubleCoset U (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) =
      {x : GL (Fin 2) F | ∃ u ∈ U,
        (x : Matrix (Fin 2) (Fin 2) F) = algebraMap R F ϖ • (u : Matrix (Fin 2) (Fin 2) F)} := by
  ext x
  rw [mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, u', hu', rfl⟩
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [diagPi_mul_localRepInf_comm, Units.val_mul, Units.val_mul, coe_diagPi_mul_localRepInf,
      Matrix.smul_mul, Matrix.one_mul, Units.val_mul]
    exact smul_mul_assoc _ _ _
  · rintro ⟨u, hu, hx⟩
    refine ⟨u, hu, 1, one_mem U, ?_⟩
    apply Units.ext
    rw [mul_one, diagPi_mul_localRepInf_comm, Units.val_mul, coe_diagPi_mul_localRepInf, Matrix.smul_mul,
      Matrix.one_mul, hx]

end Central

section Residue

variable (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

private theorem finite_quotient_span (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) :
    Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) := by
  rw [← hϖ.maximalIdeal_eq]
  have h := IsLocalRing.isOpen_iff_finite_quotient.mp
    (IsLocalRing.isOpen_maximalIdeal_pow (v.adicCompletionIntegers K) 1)
  rwa [pow_one] at h

end Residue

section CompactSubring

variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ₀] [TopologicalSpace E]
  [IsTopologicalRing E]

private theorem val_le_one_of_mem_of_isCompact (w : Valuation E Γ₀) (hball : IsOpen {a : E | w a ≤ 1})
    (S : Subring E) (hS : IsCompact (S : Set E)) {x : E} (hx : x ∈ S) : w x ≤ 1 := by
  by_contra hcon
  have hlt : 1 < w x := lt_of_not_ge hcon
  have hcover : (S : Set E) ⊆ ⋃ s ∈ (S : Set E), (fun a : E => s + a) '' {a : E | w a ≤ 1} := by
    intro s hs
    refine Set.mem_iUnion₂.2 ⟨s, hs, 0, ?_, add_zero s⟩
    show w 0 ≤ 1
    rw [map_zero]
    exact zero_le_one
  obtain ⟨t, -, htfin, hsub⟩ := hS.elim_finite_subcover_image
    (fun s _ => (Homeomorph.addLeft s).isOpenMap _ hball) hcover
  have hmem : ∀ k : ℕ, x ^ (k + 1) ∈ (S : Set E) := fun k => S.pow_mem hx _
  choose f hft hf using fun k => Set.mem_iUnion₂.1 (hsub (hmem k))
  haveI : Finite t := htfin.to_subtype
  obtain ⟨i, j, hij, hfij⟩ :=
    Finite.exists_ne_map_eq_of_infinite fun k : ℕ => (⟨f k, hft k⟩ : t)
  have hfij' : f i = f j := congrArg Subtype.val hfij
  obtain ⟨a, ha, hxa⟩ := hf i
  obtain ⟨b, hb, hxb⟩ := hf j

  have hdiff : w (x ^ (i + 1) - x ^ (j + 1)) ≤ 1 := by
    have : x ^ (i + 1) - x ^ (j + 1) = a - b := by
      rw [← hxa, ← hxb, hfij']
      exact add_sub_add_left_eq_sub a b (f j)
    rw [this]
    exact (w.map_sub a b).trans (max_le ha hb)

  rcases lt_or_gt_of_ne hij with h | h
  · have hpow : w (x ^ (i + 1)) < w (x ^ (j + 1)) := by
      rw [map_pow, map_pow]
      exact pow_lt_pow_right₀ hlt (by omega)
    rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ hpow, map_pow] at hdiff
    exact absurd hdiff (not_le.2 (one_lt_pow₀ hlt (Nat.succ_ne_zero j)))
  · have hpow : w (x ^ (j + 1)) < w (x ^ (i + 1)) := by
      rw [map_pow, map_pow]
      exact pow_lt_pow_right₀ hlt (by omega)
    rw [Valuation.map_sub_eq_of_lt_left _ hpow, map_pow] at hdiff
    exact absurd hdiff (not_le.2 (one_lt_pow₀ hlt (Nat.succ_ne_zero i)))

end CompactSubring

section Completion

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem mem_adicCompletionIntegers_of_mem_of_isCompact (S : Subring (u.adicCompletion F))
    (hS : IsCompact (S : Set (u.adicCompletion F))) {x : u.adicCompletion F} (hx : x ∈ S) :
    x ∈ u.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  refine val_le_one_of_mem_of_isCompact (Valued.v : Valuation (u.adicCompletion F) _) ?_ S hS hx
  have h := (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 F) F).out u
  convert h using 1
  all_goals first | rfl | (ext; simp [HeightOneSpectrum.mem_adicCompletionIntegers])

end Completion

section IntegralCarrier

private theorem coe_map_apply {A F : Type} [CommRing A] [CommRing F] (φ : A →+* F) (y : GL (Fin 2) A) :
    ((Matrix.GeneralLinearGroup.map φ y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) A).map φ := rfl

private theorem integralUnitsSet_eq_integralSubgroup (F : Type) [Field F] (O : ValuationSubring F) :
    integralUnitsSet (O : Set F) = (LocalGL2.integralSubgroup O F : Set (GL (Fin 2) F)) := by
  ext g
  rw [mem_integralUnitsSet, SetLike.mem_coe, LocalGL2.mem_integralSubgroup_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hinj : Function.Injective (algebraMap O F) := Subtype.val_injective
    let A : Matrix (Fin 2) (Fin 2) O := fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) F) i j, h₁ i j⟩
    let B : Matrix (Fin 2) (Fin 2) O :=
      fun i j => ⟨((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j, h₂ i j⟩
    have hA : A.map (algebraMap O F) = (g : Matrix (Fin 2) (Fin 2) F) := by ext i j; rfl
    have hB : B.map (algebraMap O F) = ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; rfl
    have hAB : A * B = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hA, hB, Matrix.map_one (algebraMap O F) (map_zero _) (map_one _)]
      exact g.mul_inv
    have hBA : B * A = 1 := by
      apply Matrix.map_injective hinj
      dsimp only
      rw [Matrix.map_mul, hB, hA, Matrix.map_one (algebraMap O F) (map_zero _) (map_one _)]
      exact g.inv_mul
    refine ⟨⟨A, B, hAB, hBA⟩, Units.ext ?_⟩
    rw [coe_map_apply]
    exact hA
  · rintro ⟨y, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [coe_map_apply]
      exact (y i j).2
    · rw [← map_inv, coe_map_apply]
      exact (y⁻¹ i j).2

private theorem map_mem_integralUnitsSet_iff {A F : Type} [CommRing A] [CommRing F] (φ : A →+* F)
    (T : Set F) (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.map φ g ∈ integralUnitsSet T ↔
      (∀ a b : Fin 2, φ ((g : Matrix (Fin 2) (Fin 2) A) a b) ∈ T) ∧
        ∀ a b : Fin 2, φ (((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) a b) ∈ T := by
  rw [mem_integralUnitsSet, ← map_inv, coe_map_apply, coe_map_apply]
  exact Iff.rfl

end IntegralCarrier

open InertTransport (theta theta_apply glEquiv glEquiv_apply glEquiv_sigmaGL)

section Transport

open scoped TensorProduct

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

open scoped TensorProduct.RightActions in

private theorem glEquiv_twistedConj (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) =
      (glEquiv K L v w e x)⁻¹ * glEquiv K L v w e δ *
        Matrix.GeneralLinearGroup.map (theta K L σ v w e).toRingHom (glEquiv K L v w e x) := by
  rw [map_mul, map_mul, map_inv, glEquiv_sigmaGL]

open scoped TensorProduct.RightActions in

private theorem exists_algEquiv_pi_adicCompletion (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        Π w : v.Extension (𝓞 L), w.1.adicCompletion L,
      ∀ z : L ⊗[K] v.adicCompletion K,
        z ∈ semiLocalIntegers K L v ↔ ∀ w : v.Extension (𝓞 L), c z w ∈ w.1.adicCompletionIntegers L := by
  refine ⟨AlgEquiv.ofRingEquiv
    (f := (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv) ?_, ?_⟩
  · intro x
    funext w
    rw [TensorProduct.RightActions.algebraMap_eval, Pi.algebraMap_apply]
    exact (HeightOneSpectrum.adicCompletion.baseChange_tmul_apply K L (𝓞 L) v 1 x w).trans
      (by rw [map_one, one_mul])
  · intro z
    rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
    exact Iff.rfl

open scoped TensorProduct.RightActions in

private theorem eq_of_under_eq (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (w₁ w₂ : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (h₁ : IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w₁ = v)
    (h₂ : IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w₂ = v) : w₁ = w₂ := by
  classical
  by_contra hne
  obtain ⟨c, -⟩ := exists_algEquiv_pi_adicCompletion K L v
  let f : (Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) ≃+* w.1.adicCompletion L :=
    (c.symm.trans e).toRingEquiv
  let u₁ : (Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) := fun w' => if w'.1 = w₁ then 1 else 0
  let u₂ : (Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) := fun w' => if w'.1 = w₂ then 1 else 0
  have h1 : u₁ ≠ 0 := by
    intro h
    have h' : u₁ ⟨w₁, h₁⟩ = (0 : Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) ⟨w₁, h₁⟩ := congrFun h _
    have h'' : u₁ ⟨w₁, h₁⟩ = 1 := if_pos rfl
    exact one_ne_zero (h''.symm.trans h')
  have h2 : u₂ ≠ 0 := by
    intro h
    have h' : u₂ ⟨w₂, h₂⟩ = (0 : Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) ⟨w₂, h₂⟩ := congrFun h _
    have h'' : u₂ ⟨w₂, h₂⟩ = 1 := if_pos rfl
    exact one_ne_zero (h''.symm.trans h')
  have hmul : u₁ * u₂ = 0 := by
    funext k
    show u₁ k * u₂ k = (0 : Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) k
    simp only [u₁, u₂]
    split_ifs with hk1 hk2
    · exact absurd (hk1.symm.trans hk2) hne
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _
  have hinj : Function.Injective f := f.injective
  have h1' : f u₁ ≠ 0 := fun h => h1 (hinj (h.trans (map_zero f).symm))
  have h2' : f u₂ ≠ 0 := fun h => h2 (hinj (h.trans (map_zero f).symm))
  exact mul_ne_zero h1' h2' (by rw [← map_mul, hmul, map_zero])

open scoped TensorProduct.RightActions in
private theorem continuous_algEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Continuous e :=
  IsModuleTopology.continuous_of_linearMap e.toLinearMap

open scoped TensorProduct.RightActions in
private theorem continuous_algEquiv_symm
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) : Continuous e.symm :=
  IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

open scoped TensorProduct.RightActions in

private theorem mem_semiLocalIntegers_iff_mem
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (z : L ⊗[K] v.adicCompletion K) :
    z ∈ semiLocalIntegers K L v ↔ e z ∈ w.1.adicCompletionIntegers L := by
  let S : Subring (L ⊗[K] v.adicCompletion K) :=
    (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubring
  have hS : (S : Set (L ⊗[K] v.adicCompletion K)) = semiLocalIntegers K L v := by
    ext y
    simp [S, semiLocalIntegers]
  constructor
  · intro hz
    have hcpt : IsCompact ((S.map e.toRingEquiv.toRingHom : Subring (w.1.adicCompletion L)) :
        Set (w.1.adicCompletion L)) := by
      rw [Subring.coe_map, hS]
      exact (isCompact_semiLocalIntegers K L v).image (continuous_algEquiv K L v w e)
    refine mem_adicCompletionIntegers_of_mem_of_isCompact L w.1 _ hcpt ?_
    rw [← SetLike.mem_coe, Subring.coe_map, hS]
    exact ⟨z, hz, rfl⟩
  · intro hz
    let P : Subring (L ⊗[K] v.adicCompletion K) :=
      (w.1.adicCompletionIntegers L).toSubring.comap e.toRingEquiv.toRingHom
    have hzP : z ∈ P := by
      rw [Subring.mem_comap]
      exact hz
    have hPcpt : IsCompact (P : Set (L ⊗[K] v.adicCompletion K)) := by
      have himg : (P : Set (L ⊗[K] v.adicCompletion K)) =
          e.symm '' (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) := by
        ext y
        constructor
        · intro hy
          exact ⟨e y, hy, e.symm_apply_apply y⟩
        · rintro ⟨c, hc, rfl⟩
          show e.toRingEquiv.toRingHom (e.symm c) ∈ (w.1.adicCompletionIntegers L).toSubring
          simpa using hc
      rw [himg]
      exact (isCompact_iff_compactSpace.2
        (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w.1)).image (continuous_algEquiv_symm K L v w e)
    rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
    intro w'
    let ρ : L ⊗[K] v.adicCompletion K →+* w'.1.adicCompletion L :=
      (Pi.evalRingHom (fun w'' : v.Extension (𝓞 L) => w''.1.adicCompletion L) w').comp
        (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v).toRingHom
    have hcpt : IsCompact ((P.map ρ : Subring (w'.1.adicCompletion L)) : Set (w'.1.adicCompletion L)) := by
      rw [Subring.coe_map]
      refine hPcpt.image ((continuous_apply w').comp ?_)
      exact (semiLocalHomeomorph K L v).continuous
    exact mem_adicCompletionIntegers_of_mem_of_isCompact L w'.1 _ hcpt ⟨z, hzP, rfl⟩

open scoped TensorProduct.RightActions in

private theorem mem_semiLocalIntegralSet_iff_glEquiv_mem
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    g ∈ semiLocalIntegralSet K L v ↔
      glEquiv K L v w e g ∈
        LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) := by
  rw [← SetLike.mem_coe,
    ← integralUnitsSet_eq_integralSubgroup (w.1.adicCompletion L) (w.1.adicCompletionIntegers L),
    glEquiv_apply, map_mem_integralUnitsSet_iff, semiLocalIntegralSet, mem_integralUnitsSet]
  simp only [mem_semiLocalIntegers_iff_mem K L v w e]
  rfl

end Transport

section Shadow

open AddMonoidAlgebra

variable {R₀ : Type*} [CommRing R₀]

private def shadow (D : ℤ) (C : R₀) (F : AddMonoidAlgebra R₀ (ℤ × ℤ)) : R₀ :=
  (if Even D then C * F.coeff (D / 2, D / 2) else 0) +
    2 * F.coeff.sum fun (x : ℤ × ℤ) (r : R₀) => if x.1 < x.2 ∧ x.1 + x.2 = D then r else 0

private theorem shadow_add (D : ℤ) (C : R₀) (F G : AddMonoidAlgebra R₀ (ℤ × ℤ)) :
    shadow D C (F + G) = shadow D C F + shadow D C G := by
  simp only [shadow, coeff_add, Finsupp.add_apply]
  rw [Finsupp.sum_add_index']
  · split_ifs <;> ring
  · intro x
    split_ifs <;> rfl
  · intro x a b
    split_ifs <;> simp

private theorem shadow_smul (D : ℤ) (C : R₀) (c : R₀) (F : AddMonoidAlgebra R₀ (ℤ × ℤ)) :
    shadow D C (c • F) = c * shadow D C F := by
  simp only [shadow, coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' fun x => by split_ifs <;> rfl]
  have h : (F.coeff.sum fun (x : ℤ × ℤ) (r : R₀) => if x.1 < x.2 ∧ x.1 + x.2 = D then c * r else 0) =
      c * F.coeff.sum fun (x : ℤ × ℤ) (r : R₀) => if x.1 < x.2 ∧ x.1 + x.2 = D then r else 0 := by
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro x _
    split_ifs <;> simp
  simp only [smul_eq_mul] at h ⊢
  rw [h]
  split_ifs <;> ring

private theorem shadow_mapDomain (n : ℕ) (hn : 0 < n) (D : ℤ) (C : R₀) (F : AddMonoidAlgebra R₀ (ℤ × ℤ)) :
    shadow (n * D) C (mapDomain (n • AddMonoidHom.id (ℤ × ℤ)) F) = shadow D C F := by
  have hid : ∀ a : ℤ × ℤ, (n • AddMonoidHom.id (ℤ × ℤ)) a = ((n : ℤ) * a.1, (n : ℤ) * a.2) := fun a => by
    simp [Prod.ext_iff]
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hinj : Function.Injective (n • AddMonoidHom.id (ℤ × ℤ)) := by
    intro a b hab
    rw [hid, hid, Prod.mk.injEq] at hab
    exact Prod.ext (mul_left_cancel₀ hn0 hab.1) (mul_left_cancel₀ hn0 hab.2)
  simp only [shadow, coeff_mapDomain]
  congr 1
  · by_cases hD : Even D
    · obtain ⟨k, rfl⟩ := hD
      have h1 : Even ((n : ℤ) * (k + k)) := ⟨n * k, by ring⟩
      have h2 : Even (k + k) := ⟨k, rfl⟩
      rw [if_pos h1, if_pos h2]
      have h3 : (n : ℤ) * (k + k) / 2 = n * k := by
        rw [show (n : ℤ) * (k + k) = 2 * (n * k) by ring, Int.mul_ediv_cancel_left _ two_ne_zero]
      have h4 : (k + k) / 2 = k := by rw [← two_mul, Int.mul_ediv_cancel_left _ two_ne_zero]
      have h5 : (n • AddMonoidHom.id (ℤ × ℤ)) (k, k) = ((n : ℤ) * k, (n : ℤ) * k) := by rw [hid]
      rw [h3, h4, ← h5, Finsupp.mapDomain_apply hinj]
    · rw [if_neg hD]
      split_ifs with h1
      · rw [Finsupp.mapDomain_notin_range, mul_zero]
        rintro ⟨⟨a, b⟩, hab⟩
        rw [hid, Prod.mk.injEq] at hab
        obtain ⟨j, hj⟩ := h1
        have hj2 : (n : ℤ) * D / 2 = j := by rw [hj, ← two_mul, Int.mul_ediv_cancel_left _ two_ne_zero]
        have ha : (n : ℤ) * a = j := by rw [← hj2]; exact hab.1
        exact hD ⟨a, mul_left_cancel₀ hn0 (by rw [mul_add, ha, hj])⟩
      · rfl
  · congr 1
    rw [Finsupp.sum_mapDomain_index_inj hinj]
    apply Finsupp.sum_congr
    intro x _
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn
    have hlt : (n : ℤ) * x.1 < (n : ℤ) * x.2 ↔ x.1 < x.2 := mul_lt_mul_iff_right₀ hnpos
    have heq : (n : ℤ) * x.1 + (n : ℤ) * x.2 = (n : ℤ) * D ↔ x.1 + x.2 = D := by
      rw [← mul_add]; exact mul_right_inj' hn0
    simp only [hid, hlt, heq]

end Shadow

section ShadowBasis

open AddMonoidAlgebra

variable {R₀ : Type*} [CommRing R₀]

private theorem shadow_zero (D : ℤ) (C : R₀) : shadow D C (0 : AddMonoidAlgebra R₀ (ℤ × ℤ)) = 0 := by
  have h := shadow_smul D C (0 : R₀) (0 : AddMonoidAlgebra R₀ (ℤ × ℤ))
  rwa [zero_smul, zero_mul] at h

private theorem shadow_sum {ι : Type*} (s : Finset ι) (D : ℤ) (C : R₀) (F : ι → AddMonoidAlgebra R₀ (ℤ × ℤ)) :
    shadow D C (∑ i ∈ s, F i) = ∑ i ∈ s, shadow D C (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, shadow_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, shadow_add, ih]

private theorem shadow_single (D : ℤ) (C : R₀) (p : ℤ × ℤ) (r : R₀) :
    shadow D C (single p r) =
      (if Even D ∧ p = (D / 2, D / 2) then C * r else 0) + 2 * if p.1 < p.2 ∧ p.1 + p.2 = D then r else 0 := by
  classical
  unfold shadow
  have hc : (single p r : AddMonoidAlgebra R₀ (ℤ × ℤ)).coeff = Finsupp.single p r := rfl
  rw [hc, Finsupp.sum_single_index (by split_ifs <;> rfl), Finsupp.single_apply]
  congr 1
  by_cases hD : Even D
  · by_cases hp : p = (D / 2, D / 2)
    · rw [if_pos hD, if_pos hp, if_pos ⟨hD, hp⟩]
    · rw [if_pos hD, if_neg hp, if_neg (fun h => hp h.2), mul_zero]
  · rw [if_neg hD, if_neg (fun h => hD h.1)]

private theorem shadow_single_mul_sum (D : ℤ) (C : R₀) (a : ℤ) (m : ℕ) (c : ℕ → R₀) :
    shadow D C (single (a, a) (1 : R₀) *
        ∑ k ∈ Finset.range (m + 1), c k • single ((k : ℤ), ((m - k : ℕ) : ℤ)) (1 : R₀)) =
      if 2 * a + m = D then
        (if Even m then C * c (m / 2) else 0) + 2 * ∑ k ∈ Finset.range ((m + 1) / 2), c k
      else 0 := by
  classical
  have hmul : (single (a, a) (1 : R₀) : AddMonoidAlgebra R₀ (ℤ × ℤ)) *
      ∑ k ∈ Finset.range (m + 1), c k • single ((k : ℤ), ((m - k : ℕ) : ℤ)) (1 : R₀) =
      ∑ k ∈ Finset.range (m + 1), single ((a + k : ℤ), (a + (m - k : ℕ) : ℤ)) (c k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, single_mul_single, one_mul, smul_single', mul_one, Prod.mk_add_mk]
  rw [hmul, shadow_sum]
  simp only [shadow_single]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  by_cases hD : 2 * a + m = D
  · rw [if_pos hD]
    congr 1
    ·
      by_cases hm : Even m
      · obtain ⟨e, rfl⟩ := hm
        have hDe : D / 2 = a + e := by omega
        rw [if_pos ⟨e, rfl⟩, show (e + e) / 2 = e by omega]
        rw [Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr (by omega))]
        · rw [if_pos]
          refine ⟨⟨a + e, by omega⟩, ?_⟩
          refine Prod.ext ?_ ?_
          · show (a : ℤ) + e = D / 2
            omega
          · show (a : ℤ) + ((e + e - e : ℕ) : ℤ) = D / 2
            omega
        · intro k hk hke
          rw [if_neg]
          rintro ⟨-, h⟩
          have h1 := congrArg Prod.fst h
          simp only at h1
          omega
      · rw [if_neg hm]
        refine Finset.sum_eq_zero fun k hk => if_neg ?_
        rintro ⟨⟨d, hd⟩, h⟩
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only at h1 h2
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact hm ⟨k, by omega⟩
    ·
      congr 1
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hk, hlt, -⟩
        omega
      · intro hk
        exact ⟨by omega, by omega, by omega⟩
  · rw [if_neg hD]
    have h0 : ∀ k ∈ Finset.range (m + 1),
        (if Even D ∧ ((a + k : ℤ), (a + (m - k : ℕ) : ℤ)) = (D / 2, D / 2) then C * c k else 0) = 0 := by
      intro k hk
      refine if_neg ?_
      rintro ⟨⟨d, hd⟩, h⟩
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      omega
    have h0' : ∀ k ∈ Finset.range (m + 1),
        (if (a + k : ℤ) < (a + (m - k : ℕ) : ℤ) ∧ (a + k : ℤ) + (a + (m - k : ℕ) : ℤ) = D then c k else 0) = 0 := by
      intro k hk
      refine if_neg ?_
      rintro ⟨-, h⟩
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      omega
    rw [Finset.sum_eq_zero h0, Finset.sum_eq_zero h0', mul_zero, add_zero]

end ShadowBasis

section Values

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open MeasureTheory

private noncomputable def realisedValue (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (S : Finset (GL (Fin 2) (v.adicCompletion K))) : ℂ :=
  ∑ s ∈ S, f (s⁻¹ * γ * s) /
    ((τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal : ℂ)

private theorem realisedValue_add (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (f g : GL (Fin 2) (v.adicCompletion K) → ℂ) (S : Finset (GL (Fin 2) (v.adicCompletion K))) :
    realisedValue K v γ τ (f + g) S = realisedValue K v γ τ f S + realisedValue K v γ τ g S := by
  simp only [realisedValue, Pi.add_apply, add_div, Finset.sum_add_distrib]

private theorem realisedValue_smul (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (c : ℂ) (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (S : Finset (GL (Fin 2) (v.adicCompletion K))) :
    realisedValue K v γ τ (c • f) S = c * realisedValue K v γ τ f S := by
  simp only [realisedValue, Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

private theorem orbitalIntegral_add (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    {f g : GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hf : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ localIntegralSet K v, ∀ u₂ ∈ localIntegralSet K v, f (u₁ * x * u₂) = f x)
    (hg : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ localIntegralSet K v, ∀ u₂ ∈ localIntegralSet K v, g (u₁ * x * u₂) = g x)
    (hfs : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
      ∀ x, f x ≠ 0 → ∃ c ∈ F₀, c⁻¹ * x ∈ localIntegralSet K v)
    (hgs : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
      ∀ x, g x ≠ 0 → ∃ c ∈ F₀, c⁻¹ * x ∈ localIntegralSet K v)
    (hfm : Measurable[glBorelOf (v.adicCompletion K)] f) (hgm : Measurable[glBorelOf (v.adicCompletion K)] g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    {I J M : ℂ} (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f I)
    (hJ : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ g J)
    (hM : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ (f + g) M) : M = I + J := by
  classical
  obtain ⟨F₀, hF₀⟩ := hfs
  obtain ⟨G₀, hG₀⟩ := hgs

  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple K v γ hγ
    (fun y => if f y ≠ 0 ∨ g y ≠ 0 then (1 : ℂ) else 0)
    ⟨F₀ ∪ G₀, fun y hy => by
      by_cases h : f y ≠ 0 ∨ g y ≠ 0
      · rcases h with h | h
        · obtain ⟨c, hc, hcy⟩ := hF₀ y h
          exact ⟨c, Finset.mem_union_left _ hc, hcy⟩
        · obtain ⟨c, hc, hcy⟩ := hG₀ y h
          exact ⟨c, Finset.mem_union_right _ hc, hcy⟩
      · exact (hy (if_neg h)).elim⟩
  have hcovf : ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) ≠ 0 →
      ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
        ∃ u ∈ localIntegralSet K v, x = t * s * u :=
    fun x hx => hcov x (by rw [if_pos (Or.inl hx)]; exact one_ne_zero)
  have hcovg : ∀ x : GL (Fin 2) (v.adicCompletion K), g (x⁻¹ * γ * x) ≠ 0 →
      ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
        ∃ u ∈ localIntegralSet K v, x = t * s * u :=
    fun x hx => hcov x (by rw [if_pos (Or.inr hx)]; exact one_ne_zero)
  have hcovfg : ∀ x : GL (Fin 2) (v.adicCompletion K), (f + g) (x⁻¹ * γ * x) ≠ 0 →
      ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
        ∃ u ∈ localIntegralSet K v, x = t * s * u := by
    intro x hx
    refine hcov x ?_
    have h : f (x⁻¹ * γ * x) ≠ 0 ∨ g (x⁻¹ * γ * x) ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by rw [Pi.add_apply, h.1, h.2, add_zero])
    rw [if_pos h]
    exact one_ne_zero
  have hfg : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ localIntegralSet K v, ∀ u₂ ∈ localIntegralSet K v, (f + g) (u₁ * x * u₂) = (f + g) x :=
    fun x u₁ hu₁ u₂ hu₂ => by rw [Pi.add_apply, Pi.add_apply, hf x u₁ hu₁ u₂ hu₂, hg x u₁ hu₁ u₂ hu₂]
  have h1 := isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hγ τ hτ f hf S hS hcovf
  have h2 := isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hγ τ hτ g hg S hS hcovg
  have h3 := isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hγ τ hτ (f + g) hfg S hS
    hcovfg
  have hfgb : ∃ C : ℝ, ∀ x, ‖(f + g) x‖ ≤ C := by
    obtain ⟨Cf, hCf⟩ := hfb
    obtain ⟨Cg, hCg⟩ := hgb
    exact ⟨Cf + Cg, fun x => (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))⟩
  rw [IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
      (isHaarMeasure_localHaar K v) γ hγ τ hτ (f + g) (hfm.add hgm) hfgb hM h3,
    IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
      (isHaarMeasure_localHaar K v) γ hγ τ hτ f hfm hfb hI h1,
    IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
      (isHaarMeasure_localHaar K v) γ hγ τ hτ g hgm hgb hJ h2]
  simp only [Pi.add_apply, add_div, Finset.sum_add_distrib]

private theorem orbitalIntegral_smul (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    {f : GL (Fin 2) (v.adicCompletion K) → ℂ} (c : ℂ)
    (hf : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ localIntegralSet K v, ∀ u₂ ∈ localIntegralSet K v, f (u₁ * x * u₂) = f x)
    (hfs : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
      ∀ x, f x ≠ 0 → ∃ c ∈ F₀, c⁻¹ * x ∈ localIntegralSet K v)
    (hfm : Measurable[glBorelOf (v.adicCompletion K)] f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    {I M : ℂ} (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f I)
    (hM : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ (c • f) M) : M = c * I := by
  classical
  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple K v γ hγ f hfs
  have hcovc : ∀ x : GL (Fin 2) (v.adicCompletion K), (c • f) (x⁻¹ * γ * x) ≠ 0 →
      ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
        ∃ u ∈ localIntegralSet K v, x = t * s * u :=
    fun x hx => hcov x (right_ne_zero_of_mul hx)
  have hcf : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ localIntegralSet K v, ∀ u₂ ∈ localIntegralSet K v, (c • f) (u₁ * x * u₂) = (c • f) x :=
    fun x u₁ hu₁ u₂ hu₂ => by rw [Pi.smul_apply, Pi.smul_apply, hf x u₁ hu₁ u₂ hu₂]
  have h1 := isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hγ τ hτ f hf S hS hcov
  have h2 := isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hγ τ hτ (c • f) hcf S hS
    hcovc
  have hcfb : ∃ C : ℝ, ∀ x, ‖(c • f) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hfb
    exact ⟨‖c‖ * C, fun x => by rw [Pi.smul_apply, norm_smul]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩
  rw [IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
      (isHaarMeasure_localHaar K v) γ hγ τ hτ (c • f) (hfm.const_smul c) hcfb hM h2,
    IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
      (isHaarMeasure_localHaar K v) γ hγ τ hτ f hfm hfb hI h1]
  simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

private theorem exists_isOrbitalIntegralOn (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    {f : GL (Fin 2) (v.adicCompletion K) → ℂ}
    (hf : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∀ u₁ ∈ localIntegralSet K v, ∀ u₂ ∈ localIntegralSet K v, f (u₁ * x * u₂) = f x)
    (hfs : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
      ∀ x, f x ≠ 0 → ∃ c ∈ F₀, c⁻¹ * x ∈ localIntegralSet K v) :
    ∃ I, IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ f I := by
  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple K v γ hγ f hfs
  exact ⟨_, isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hγ τ hτ f hf S hS hcov⟩

private theorem localIntegralSet_eq :
    localIntegralSet K v = (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K))) := by
  rw [localIntegralSet, integralUnitsSet_eq_integralSubgroup (v.adicCompletion K) (v.adicCompletionIntegers K)]

variable (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)

private theorem hecke_bi_invariant : ∀ x : GL (Fin 2) (v.adicCompletion K),
    ∀ u₁ ∈ localIntegralSet K v, ∀ u₂ ∈ localIntegralSet K v,
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (u₁ * x * u₂) = (f : GL (Fin 2) (v.adicCompletion K) → ℂ) x := by
  intro x u₁ hu₁ u₂ hu₂
  rw [localIntegralSet_eq] at hu₁ hu₂
  rw [apply_mul_right f hu₂, apply_left_mul f hu₁]

private theorem hecke_finite_support : ∃ F₀ : Finset (GL (Fin 2) (v.adicCompletion K)),
    ∀ x, (f : GL (Fin 2) (v.adicCompletion K) → ℂ) x ≠ 0 → ∃ c ∈ F₀, c⁻¹ * x ∈ localIntegralSet K v := by
  classical
  obtain ⟨T, hT⟩ := (finite_cosets f).exists_finset_coe
  refine ⟨T.image Quotient.out, fun x hx => ?_⟩
  have hxT : (QuotientGroup.mk x : GL (Fin 2) (v.adicCompletion K) ⧸
      integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ∈ T := by
    rw [← Finset.mem_coe, hT]
    exact ⟨x, hx, rfl⟩
  refine ⟨Quotient.out (QuotientGroup.mk x), Finset.mem_image_of_mem _ hxT, ?_⟩
  rw [localIntegralSet_eq, SetLike.mem_coe]
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

private theorem hecke_bounded : ∃ C : ℝ, ∀ x, ‖(f : GL (Fin 2) (v.adicCompletion K) → ℂ) x‖ ≤ C := by
  classical
  obtain ⟨F₀, hF₀⟩ := hecke_finite_support K v f
  refine ⟨∑ c ∈ F₀, ‖(f : GL (Fin 2) (v.adicCompletion K) → ℂ) c‖, fun x => ?_⟩
  by_cases hx : (f : GL (Fin 2) (v.adicCompletion K) → ℂ) x = 0
  · rw [hx, norm_zero]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · obtain ⟨c, hc, hcx⟩ := hF₀ x hx
    have h := hecke_bi_invariant K v f c 1 (one_mem_localIntegralSet K v) (c⁻¹ * x) hcx
    rw [one_mul, mul_inv_cancel_left] at h
    rw [h]
    exact Finset.single_le_sum (fun c _ => norm_nonneg ((f : GL (Fin 2) (v.adicCompletion K) → ℂ) c)) hc

private theorem hecke_measurable : Measurable[glBorelOf (v.adicCompletion K)] (f : GL (Fin 2) (v.adicCompletion K) → ℂ) := by
  letI := glBorelOf (v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := ⟨rfl⟩
  apply Continuous.measurable
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{y | x⁻¹ * y ∈ localIntegralSet K v}, ?_, ?_, fun y hy => ?_⟩
  · exact (isOpen_localIntegralSet K v).preimage (continuous_const.mul continuous_id)
  · show x⁻¹ * x ∈ localIntegralSet K v
    rw [inv_mul_cancel]
    exact one_mem_localIntegralSet K v
  · have h := hecke_bi_invariant K v f x 1 (one_mem_localIntegralSet K v) (x⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h

end Values

section Indices

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open MeasureTheory

open scoped Classical in

private theorem realisedValue_heckeIndicator (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (g : GL (Fin 2) (v.adicCompletion K)) (hfin) (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (ι : GL (Fin 2) (v.adicCompletion K) → ℕ) (m : ℝ) (hm : m ≠ 0)
    (hidx : ∀ s ∈ S,
      (ι s : ℝ) * (τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal = m) :
    realisedValue K v γ τ
        ((heckeIndicator ℂ g hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) S =
      (∑ s ∈ S with
          s⁻¹ * γ * s ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) g,
        (ι s : ℂ)) / (m : ℂ) := by
  rw [realisedValue, Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  split_ifs with h
  · rw [heckeIndicator_apply_of_mem hfin h]
    have hidxs := hidx s hs
    have hτ0 : (τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hidxs
      exact hm hidxs.symm
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hm), div_mul_eq_mul_div, one_mul,
      div_eq_iff (Complex.ofReal_ne_zero.mpr hτ0), ← hidxs, Complex.ofReal_mul, Complex.ofReal_natCast]
  · rw [heckeIndicator_apply_of_notMem hfin h, zero_div]

end Indices

section BasisElement

open LocalGL2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

private theorem coe_zpow_of_coe_eq_diagonal (g : GL (Fin 2) K) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = !![x, 0; 0, y]) (z : ℤ) :
    ((g ^ z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![x ^ z, 0; 0, y ^ z] := by
  have hinv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![x⁻¹, 0; 0, y⁻¹] := by
    rw [Matrix.coe_units_inv, hg]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hy]
  induction z using Int.induction_on with
  | zero =>
    rw [zpow_zero, zpow_zero, zpow_zero, Units.val_one]
    exact Matrix.one_fin_two
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih, hg, zpow_add_one₀ hx, zpow_add_one₀ hy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hinv, zpow_sub_one₀ hx, zpow_sub_one₀ hy]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

private theorem coe_diagPi_zpow_mul_localRepInf_zpow (a c : ℤ) :
    ((diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![algebraMap R K ϖ ^ a, 0; 0, algebraMap R K ϖ ^ c] := by
  rw [Units.val_mul, coe_zpow_of_coe_eq_diagonal _ _ _ hϖ0 one_ne_zero (coe_diagPi ϖ hϖ0) a,
    coe_zpow_of_coe_eq_diagonal _ _ _ one_ne_zero hϖ0 (coe_localRepInf ϖ hϖ0) c, one_zpow, one_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

private theorem coe_weylInt_mul_mul_weylInt (a c : ℤ) :
    ((weylInt R K * (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ c) * weylInt R K : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![algebraMap R K ϖ ^ c, algebraMap R K ϖ ^ a] := by
  rw [Units.val_mul, Units.val_mul, coe_diagPi_zpow_mul_localRepInf_zpow, coe_weylInt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

private theorem doubleCoset_eq_of_mem {U : Subgroup (GL (Fin 2) K)} {w : GL (Fin 2) K} (hw : w ∈ U) (hw2 : w * w = 1)
    (g : GL (Fin 2) K) : doubleCoset U (w * g * w) = doubleCoset U g := by
  ext x
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    exact ⟨u₁ * w, mul_mem hu₁ hw, w * u₂, mul_mem hw hu₂, by simp only [mul_assoc]⟩
  · rintro ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    refine ⟨u₁ * w, mul_mem hu₁ hw, w * u₂, mul_mem hw hu₂, ?_⟩
    calc u₁ * w * (w * g * w) * (w * u₂) = u₁ * (w * w) * g * (w * w) * u₂ := by simp only [mul_assoc]
      _ = u₁ * g * u₂ := by rw [hw2, mul_one, mul_one]

end BasisElement

section DetValuation

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem _root_.InertBaseChange.valued_coe_unit (x : (u.adicCompletionIntegers F)ˣ) :
    Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) = 1 := by
  have hmul : ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
      ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) = 1 :=
    congrArg Subtype.val (Units.mul_inv x)
  have hx : Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) ≤ 1 := by
    have h := (x : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  have hxi : Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
      u.adicCompletion F) ≤ 1 := by
    have h := ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F).2
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  refine le_antisymm hx ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        ((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F)) := by rw [hmul, map_one]
    _ = Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) *
        Valued.v (((x⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) :
          u.adicCompletion F) := map_mul _ _ _
    _ ≤ Valued.v ((x : u.adicCompletionIntegers F) : u.adicCompletion F) := mul_le_of_le_one_right' hxi

p2m_export "InertBaseChange" "valued_coe_unit"

private theorem _root_.InertBaseChange.valued_coe_eq_of_irreducible {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : u.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.adicCompletion.exists_uniformizer F u
  have hspan : Ideal.span {ϖ} = Ideal.span {π} :=
    hϖ.maximalIdeal_eq.symm.trans (HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer F u hπ)
  obtain ⟨c, hc⟩ := Ideal.span_singleton_eq_span_singleton.1 hspan
  rw [← hπ, ← hc]
  change _ = Valued.v ((ϖ : u.adicCompletion F) * ((c : u.adicCompletionIntegers F) : u.adicCompletion F))
  rw [map_mul, valued_coe_unit F u c, mul_one]

p2m_export "InertBaseChange" "valued_coe_eq_of_irreducible"

private theorem zpow_exponent_unique {ϖ : u.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (w w' : (u.adicCompletionIntegers F)ˣ) (D D' : ℤ)
    (h : algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) w *
        algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ^ D =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) w' *
        algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ^ D') : D = D' := by
  have hv := congrArg Valued.v h
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀] at hv
  change Valued.v ((w : u.adicCompletionIntegers F) : u.adicCompletion F) *
      Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ D =
    Valued.v ((w' : u.adicCompletionIntegers F) : u.adicCompletion F) *
      Valued.v ((ϖ : u.adicCompletionIntegers F) : u.adicCompletion F) ^ D' at hv
  rw [valued_coe_unit, valued_coe_unit, one_mul, one_mul, valued_coe_eq_of_irreducible F u hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_zpow, WithZero.coe_inj, ← ofAdd_zsmul, ← ofAdd_zsmul, Multiplicative.ofAdd.injective.eq_iff,
    smul_neg, smul_neg, neg_inj, zsmul_one, zsmul_one, Int.cast_inj] at hv
  exact hv

private theorem exists_det_eq_of_mem_doubleCoset (x y : u.adicCompletionIntegers F)
    (g : GL (Fin 2) (u.adicCompletion F))
    (hg : (g : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      !![algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) x, 0;
        0, algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) y])
    {z : GL (Fin 2) (u.adicCompletion F)}
    (hz : z ∈ doubleCoset (integralSubgroup (u.adicCompletionIntegers F) (u.adicCompletion F)) g) :
    ∃ w : (u.adicCompletionIntegers F)ˣ,
      Matrix.det (z : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
        algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) w *
          (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) x *
            algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) y) := by
  obtain ⟨u₁, ⟨γ₁, rfl⟩, u₂, ⟨γ₂, rfl⟩, rfl⟩ := mem_doubleCoset_iff.mp hz
  refine ⟨Matrix.GeneralLinearGroup.det γ₁ * Matrix.GeneralLinearGroup.det γ₂, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hg, Matrix.det_fin_two_of, mul_zero, sub_zero,
    Units.val_mul, map_mul]
  have h₁ : Matrix.det ((Matrix.GeneralLinearGroup.map
      (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)) γ₁ : GL (Fin 2) (u.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) (Matrix.GeneralLinearGroup.det γ₁) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  have h₂ : Matrix.det ((Matrix.GeneralLinearGroup.map
      (algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F)) γ₂ : GL (Fin 2) (u.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) =
      algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) (Matrix.GeneralLinearGroup.det γ₂) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  rw [h₁, h₂]
  ring

end DetValuation

section GroupIdentities

variable {G : Type*} [Group G]

private theorem conj_mul_mul_eq (γ s t u : G) (h : γ * t = t * γ) :
    (t * s * u)⁻¹ * γ * (t * s * u) = u⁻¹ * (s⁻¹ * γ * s) * u := by
  have ht : t⁻¹ * γ * t = γ := by rw [mul_assoc, inv_mul_eq_iff_eq_mul, h]
  calc (t * s * u)⁻¹ * γ * (t * s * u) = u⁻¹ * s⁻¹ * (t⁻¹ * γ * t) * s * u := by group
    _ = u⁻¹ * (s⁻¹ * γ * s) * u := by rw [ht]; group

private theorem eq_mul_mul_inv_of_eq (a b u : G) (h : a = u⁻¹ * b * u) : b = u * a * u⁻¹ := by
  rw [h]; group

end GroupIdentities

section PerBasisIndex

open LocalGL2

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem weylInt_mul_self {R : Type*} [CommRing R] [Algebra R (v.adicCompletion K)] :
    weylInt R (v.adicCompletion K) * weylInt R (v.adicCompletion K) = 1 := by
  ext i j
  rw [Units.val_mul, coe_weylInt, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem algebraMap_ne_zero_of_irreducible {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0 := fun h =>
  hϖ.ne_zero (Subtype.ext h)

private theorem doubleCoset_basis_eq (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (a c : ℤ) :
    doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ c) =
      localIntegralSet K v *
          ({weylInt (v.adicCompletionIntegers K) (v.adicCompletion K) * (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ c) *
              weylInt (v.adicCompletionIntegers K) (v.adicCompletion K)} :
            Set (GL (Fin 2) (v.adicCompletion K))) *
        localIntegralSet K v := by
  rw [← doubleCoset_eq_of_mem weylInt_mem (weylInt_mul_self K v) (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ c),
    localIntegralSet_eq]
  rfl

private theorem setOf_mem_localIntegralSet_eq (γ s : GL (Fin 2) (v.adicCompletion K)) :
    {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
        s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v} =
      ((TorusIndices.conjStabilizer K v γ s).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))) := by
  ext t
  rw [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_subgroupOf, TorusIndices.mem_conjStabilizer_iff]
  exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩

open scoped Classical in

private theorem card_sdiff_eq_relIndex_mul_sum_filter (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ) (a : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a + (m : ℤ)))
    (hfin) (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
      ∀ u ∈ localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ (a + (m : ℤ))) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∃ u ∈ localIntegralSet K v, x = t * s * u) :
    Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) m γ \
          LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) (m - 1) γ) =
      (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S with
            s⁻¹ * γ * s ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
              (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
                localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ (a + (m : ℤ))),
          (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) := by
  set hϖ0 := algebraMap_ne_zero_of_irreducible K v hϖ
  set g := diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ (a + (m : ℤ)) with hg
  have hD := doubleCoset_basis_eq K v ϖ hϖ0 a (a + (m : ℤ))
  refine LT.LatticeTree.card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow K v ϖ hϖ γ a m hm
    u hdet (weylInt (v.adicCompletionIntegers K) (v.adicCompletion K) * g *
      weylInt (v.adicCompletionIntegers K) (v.adicCompletion K))
    (coe_weylInt_mul_mul_weylInt ϖ hϖ0 a (a + (m : ℤ))) (TorusIndices.unitCentralizer K v γ)
    (TorusIndices.mem_unitCentralizer_iff K v γ) (TorusIndices.conjStabilizer K v γ)
    (TorusIndices.mem_conjStabilizer_iff K v γ) _ (fun s hs => ?_) (fun s hs s' hs' => ?_) (fun x hx => ?_)
  · rw [← hD]
    exact (Finset.mem_filter.mp hs).2
  · exact hS s (Finset.mem_filter.mp hs).1 s' (Finset.mem_filter.mp hs').1
  · rw [← hD] at hx
    obtain ⟨s, hs, t, ht, u', hu', rfl⟩ := hcov x (by rw [heckeIndicator_apply_of_mem hfin hx]; exact one_ne_zero)
    refine ⟨s, Finset.mem_filter.mpr ⟨hs, ?_⟩, t, ht, u', hu', rfl⟩
    have hu'U : u' ∈ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
      rw [← SetLike.mem_coe, ← localIntegralSet_eq]; exact hu'
    have h1 := conj_mul_mul_eq γ s t u' (Subgroup.mem_centralizer_iff.mp ht γ (Set.mem_singleton γ))
    have h2 : s⁻¹ * γ * s = u' * ((t * s * u')⁻¹ * γ * (t * s * u')) * u'⁻¹ := eq_mul_mul_inv_of_eq _ _ _ h1
    rw [h2]
    exact doubleCoset_mul_mem (mul_mem_doubleCoset hx hu'U) (inv_mem hu'U)

end PerBasisIndex

section PerBasisValue

open LocalGL2 MeasureTheory

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem measurableSet_conjStabilizer_subgroupOf (γ s : GL (Fin 2) (v.adicCompletion K)) :
    MeasurableSet[centralizerBorel (v.adicCompletion K) γ]
      ((TorusIndices.conjStabilizer K v γ s).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))) := by
  letI := centralizerBorel (v.adicCompletion K) γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  rw [Subgroup.coe_subgroupOf, Subgroup.coe_subtype]
  exact ((TorusIndices.isCompact_conjStabilizer K v γ s).isClosed.preimage continuous_subtype_val).measurableSet

private theorem relIndex_mul_measureReal_eq (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (s : GL (Fin 2) (v.adicCompletion K))
    (hidx : (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0) :
    ((TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) : ℝ) *
        (τ {t | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal =
      (τ ((TorusIndices.unitCentralizer K v γ).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal := by
  letI := centralizerBorel (v.adicCompletion K) γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI := hτ
  rw [setOf_mem_localIntegralSet_eq,
    TorusIndices.measure_unitCentralizer_subgroupOf_eq K v γ τ s hidx
      (measurableSet_conjStabilizer_subgroupOf K v γ s),
    ENNReal.toReal_mul, ENNReal.toReal_natCast]

private theorem measureReal_unitCentralizer_ne_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (hidx : (TorusIndices.conjStabilizer K v γ 1).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0) :
    (τ ((TorusIndices.unitCentralizer K v γ).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal ≠ 0 := by
  letI := centralizerBorel (v.adicCompletion K) γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI := hτ
  have hS : (τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
      (1 : GL (Fin 2) (v.adicCompletion K))⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * 1 ∈
        localIntegralSet K v}).toReal ≠ 0 := by
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
    · refine (IsOpen.measure_pos τ ((isOpen_localIntegralSet K v).preimage (by fun_prop)) ⟨1, ?_⟩).ne'
      show (1 : GL (Fin 2) (v.adicCompletion K))⁻¹ *
          ((1 : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
            GL (Fin 2) (v.adicCompletion K)) * 1 ∈ localIntegralSet K v
      rw [inv_one, one_mul, mul_one, OneMemClass.coe_one]
      exact one_mem_localIntegralSet K v
    · rw [setOf_mem_localIntegralSet_eq, Subgroup.coe_subgroupOf, Subgroup.coe_subtype]
      exact ((TorusIndices.isClosed_centralizer K v γ).isClosedEmbedding_subtypeVal.isCompact_preimage
        (TorusIndices.isCompact_conjStabilizer K v γ 1)).measure_lt_top.ne
  rw [← relIndex_mul_measureReal_eq K v γ τ hτ 1 hidx]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hidx) hS

end PerBasisValue

section ScalarMember

p2m_open "LocalGL2 LT.LatticeTree~exists_act_stdVertex_eq"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem scalarGL_inv (d : (v.adicCompletion K)ˣ) :
    (scalarGL d : GL (Fin 2) (v.adicCompletion K))⁻¹ = scalarGL d⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one])

private theorem diagPi_zpow_mul_localRepInf_zpow_self (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (a : ℤ) :
    diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ a =
      scalarGL (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 ^ a) := by
  refine Units.ext ?_
  rw [coe_diagPi_zpow_mul_localRepInf_zpow, scalarGL_coe, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem mem_doubleCoset_scalarGL_iff (d : (v.adicCompletion K)ˣ) (x : GL (Fin 2) (v.adicCompletion K)) :
    x ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) (scalarGL d) ↔
      scalarGL d⁻¹ * x ∈ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
  constructor
  · intro h
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_doubleCoset_iff.mp h
    have e : scalarGL d⁻¹ * (u₁ * scalarGL d * u₂) = u₁ * u₂ := by
      rw [← scalarGL_mul_comm d u₁, mul_assoc (scalarGL d) u₁ u₂, ← mul_assoc, ← scalarGL_mul, inv_mul_cancel,
        scalarGL_one, one_mul]
    rw [e]
    exact mul_mem hu₁ hu₂
  · intro h
    refine mem_doubleCoset_iff.mpr ⟨1, one_mem _, scalarGL d⁻¹ * x, h, ?_⟩
    rw [one_mul, ← mul_assoc, ← scalarGL_mul, mul_inv_cancel, scalarGL_one, one_mul]

private theorem centralizer_scalarGL_mul (d : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K)) :
    Subgroup.centralizer ({scalarGL d * γ} : Set (GL (Fin 2) (v.adicCompletion K))) =
      Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) := by
  ext t
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    apply mul_left_cancel (a := scalarGL d)
    rw [← mul_assoc, h, ← mul_assoc, ← scalarGL_mul_comm d t, mul_assoc]
  · intro h
    rw [mul_assoc, h, ← mul_assoc, scalarGL_mul_comm d t, mul_assoc]

private theorem conj_scalarGL_mul (d : (v.adicCompletion K)ˣ) (γ s : GL (Fin 2) (v.adicCompletion K)) :
    s⁻¹ * (scalarGL d * γ) * s = scalarGL d * (s⁻¹ * γ * s) := by
  rw [← mul_assoc s⁻¹, ← scalarGL_mul_comm d s⁻¹, mul_assoc (scalarGL d) s⁻¹ γ, mul_assoc (scalarGL d) (s⁻¹ * γ) s]

private theorem det_scalarGL_mul_eq (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (γ : GL (Fin 2) (v.adicCompletion K))
    (u : (v.adicCompletionIntegers K)ˣ) (a : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a)) :
    Matrix.det ((scalarGL (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 ^ a)⁻¹ *
        γ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u := by
  rw [Units.val_mul, scalarGL_coe, Matrix.smul_mul, one_mul, Matrix.det_smul, Fintype.card_fin, hdet,
    Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hx : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a ≠ 0 := zpow_ne_zero a hϖ0
  have h2 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a) =
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a) ^ 2 := by
    rw [mul_comm, zpow_mul, zpow_two, sq]
  rw [h2, inv_pow, mul_left_comm, inv_mul_cancel₀ (pow_ne_zero 2 hx), mul_one]

end ScalarMember

section ScalarPlug

p2m_open "LocalGL2 LT.LatticeTree~exists_act_stdVertex_eq P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedTreeTransport"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

open scoped Classical in

private theorem unitOrbitalCount_eq_relIndex_mul_sum_filter (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ) (a : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a))
    (hfin) (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
      ∀ u ∈ localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∃ u ∈ localIntegralSet K v, x = t * s * u) :
    unitOrbitalCount (v.adicCompletionIntegers K) γ =
      (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S with
            s⁻¹ * γ * s ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
              (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
                localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a),
          (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) := by
  set hϖ0 := algebraMap_ne_zero_of_irreducible K v hϖ
  set d : (v.adicCompletion K)ˣ :=
    Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hϖ0 ^ a with hd
  have hg : diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ a = scalarGL d := diagPi_zpow_mul_localRepInf_zpow_self K v ϖ hϖ0 a
  have hcent := centralizer_scalarGL_mul K v d⁻¹ γ
  have hmem : ∀ s : GL (Fin 2) (v.adicCompletion K),
      s⁻¹ * γ * s ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
          (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ a) ↔
        s⁻¹ * (scalarGL d⁻¹ * γ) * s ∈ localIntegralSet K v := by
    intro s
    rw [hg, mem_doubleCoset_scalarGL_iff, conj_scalarGL_mul, localIntegralSet_eq, SetLike.mem_coe]
  have key := unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap K v (scalarGL d⁻¹ * γ) u
    (det_scalarGL_mul_eq K v ϖ hϖ0 γ u a hdet) (TorusIndices.unitCentralizer K v γ)
    (fun t => by rw [hcent]; exact TorusIndices.mem_unitCentralizer_iff K v γ t) (TorusIndices.conjStabilizer K v γ)
    (fun s t => by rw [hcent]; exact TorusIndices.mem_conjStabilizer_iff K v γ s t)
    (S.filter fun s => s⁻¹ * γ * s ∈
      doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ a))
    (fun s hs => (hmem s).mp (Finset.mem_filter.mp hs).2)
    (fun s hs s' hs' t ht => hS s (Finset.mem_filter.mp hs).1 s' (Finset.mem_filter.mp hs').1 t (by rwa [hcent] at ht))
    (fun x hx => by
      rw [← hmem] at hx
      obtain ⟨s, hs, t, ht, u', hu', rfl⟩ := hcov x (by rw [heckeIndicator_apply_of_mem hfin hx]; exact one_ne_zero)
      refine ⟨s, Finset.mem_filter.mpr ⟨hs, ?_⟩, t, by rwa [hcent], u', hu', rfl⟩
      have hu'U : u' ∈ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
        rw [← SetLike.mem_coe, ← localIntegralSet_eq]; exact hu'
      have h1 := conj_mul_mul_eq γ s t u' (Subgroup.mem_centralizer_iff.mp ht γ (Set.mem_singleton γ))
      rw [eq_mul_mul_inv_of_eq _ _ _ h1]
      exact doubleCoset_mul_mem (mul_mem_doubleCoset hx hu'U) (inv_mem hu'U))
  rw [unitOrbitalCount_scalarGL_mul, hcent] at key
  exact key

private theorem relIndex_sup_center_ne_zero (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ) (a : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a))
    (hfix : unitOrbitalCount (v.adicCompletionIntegers K) γ ≠ 0)
    (hfin) (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
      ∀ u ∈ localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∃ u ∈ localIntegralSet K v, x = t * s * u) :
    (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
        (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≠ 0 := by
  intro h
  apply hfix
  rw [unitOrbitalCount_eq_relIndex_mul_sum_filter K v ϖ hϖ γ u a hdet hfin S hS hcov, h, zero_mul]

end ScalarPlug

section BasisValue

p2m_open "LocalGL2 LT.LatticeTree~exists_act_stdVertex_eq MeasureTheory"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem exists_det_eq_mul_det_of_mem_doubleCoset (g : GL (Fin 2) (v.adicCompletion K))
    {z : GL (Fin 2) (v.adicCompletion K)}
    (hz : z ∈ doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) g) :
    ∃ w : (v.adicCompletionIntegers K)ˣ,
      Matrix.det (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w *
          Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_doubleCoset_iff.mp hz
  obtain ⟨w₁, hw₁⟩ := TorusIndices.exists_det_eq_of_mem_localIntegralSet K v
    ((TorusIndices.mem_integralSubgroup_iff_mem_localIntegralSet K v u₁).1 hu₁)
  obtain ⟨w₂, hw₂⟩ := TorusIndices.exists_det_eq_of_mem_localIntegralSet K v
    ((TorusIndices.mem_integralSubgroup_iff_mem_localIntegralSet K v u₂).1 hu₂)
  refine ⟨w₁ * w₂, ?_⟩
  simp only [Units.val_mul, Matrix.det_mul, map_mul]
  rw [hw₁, hw₂]
  ring

private theorem realisedValue_heckeIndicator_eq_zero (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ) (D : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (a c : ℤ) (hD : a + c ≠ D)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hfin) (S : Finset (GL (Fin 2) (v.adicCompletion K))) :
    realisedValue K v γ τ
        ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ c) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) S = 0 := by
  rw [realisedValue]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [heckeIndicator_apply_of_notMem hfin ?_, zero_div]
  intro hmem
  obtain ⟨w, hw⟩ := exists_det_eq_mul_det_of_mem_doubleCoset K v _ hmem
  rw [TorusIndices.det_coe_conj, hdet, coe_diagPi_zpow_mul_localRepInf_zpow, Matrix.det_fin_two_of, mul_zero,
    sub_zero, ← zpow_add₀ (algebraMap_ne_zero_of_irreducible K v hϖ)] at hw
  exact hD (zpow_exponent_unique K v hϖ u w D (a + c) hw).symm

open scoped Classical in

private theorem realisedValue_heckeIndicator_eq_card_div (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ) (a : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a + (m : ℤ)))
    (hfin) (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
      ∀ u ∈ localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ (a + (m : ℤ))) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∃ u ∈ localIntegralSet K v, x = t * s * u)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (hidx : ∀ s : GL (Fin 2) (v.adicCompletion K),
      (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0)
    (hTZ : (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≠ 0) :
    realisedValue K v γ τ
        ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ (a + (m : ℤ))) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) S =
      (Nat.card
          ↥(orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) m γ \
            orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero)
              (m - 1) γ) : ℂ) /
        (((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℂ) *
          ((τ ((TorusIndices.unitCentralizer K v γ).subgroupOf
              (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
            Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ)) := by
  have hM := measureReal_unitCentralizer_ne_zero K v γ τ hτ (hidx 1)
  have h1 := realisedValue_heckeIndicator K v γ τ
    (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
      localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ (a + (m : ℤ))) hfin S
    (fun s => (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ)) _ hM
    (fun s _ => relIndex_mul_measureReal_eq K v γ τ hτ s (hidx s))
  have h2 := card_sdiff_eq_relIndex_mul_sum_filter K v ϖ hϖ γ u a m hm hdet hfin S hS hcov
  have h0 : (((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hTZ
  rw [h1, h2, Nat.cast_mul, Nat.cast_sum, mul_div_mul_left _ _ h0]

open scoped Classical in

private theorem realisedValue_heckeIndicator_eq_unitOrbitalCount_div (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ) (a : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a))
    (hfin) (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
      ∀ u ∈ localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) (x⁻¹ * γ * x) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∃ u ∈ localIntegralSet K v, x = t * s * u)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (hidx : ∀ s : GL (Fin 2) (v.adicCompletion K),
      (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0)
    (hTZ : (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≠ 0) :
    realisedValue K v γ τ
        ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a) hfin :
          HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
          GL (Fin 2) (v.adicCompletion K) → ℂ) S =
      (unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ) /
        (((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℂ) *
          ((τ ((TorusIndices.unitCentralizer K v γ).subgroupOf
              (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
            Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ)) := by
  have hM := measureReal_unitCentralizer_ne_zero K v γ τ hτ (hidx 1)
  have h1 := realisedValue_heckeIndicator K v γ τ
    (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
      localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a) hfin S
    (fun s => (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ)) _ hM
    (fun s _ => relIndex_mul_measureReal_eq K v γ τ hτ s (hidx s))
  have h2 := unitOrbitalCount_eq_relIndex_mul_sum_filter K v ϖ hϖ γ u a hdet hfin S hS hcov
  have h0 : (((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hTZ
  rw [h1, h2, Nat.cast_mul, Nat.cast_sum, mul_div_mul_left _ _ h0]

end BasisValue

section ShadowLink

p2m_open "LocalGL2 LT.LatticeTree~exists_act_stdVertex_eq MeasureTheory AddMonoidAlgebra"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem act_mem_orbitalBall_iff {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] (c : Fˣ) (n : ℕ)
    {γ t : Matrix.GeneralLinearGroup (Fin 2) F} (ht : γ * t = t * γ) (x : Vertex R F) :
    Vertex.act t x ∈ orbitalBall (R := R) c n γ ↔ x ∈ orbitalBall (R := R) c n γ := by
  have key : ∀ s : Matrix.GeneralLinearGroup (Fin 2) F, γ * s = s * γ → ∀ y : Vertex R F,
      y ∈ orbitalBall (R := R) c n γ → Vertex.act s y ∈ orbitalBall (R := R) c n γ := by
    intro s hs y hy
    rw [mem_orbitalBall] at hy ⊢
    rw [← Vertex.act_mul, hs, Vertex.act_mul]
    exact FixedOrInversion.isWithin_act s hy
  refine ⟨fun h => ?_, key t ht x⟩
  have h' := key t⁻¹ (show Commute γ t from ht).inv_right.eq _ h
  rwa [FixedOrInversion.act_inv_act] at h'

private theorem relIndex_conjStabilizer_ne_zero_of_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : Even D) (s : GL (Fin 2) (v.adicCompletion K)) :
    (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0 :=
  TorusIndices.relIndex_conjStabilizer_ne_zero K v γ
    (FixedOrInversion.unitOrbitalCount_ne_zero_of_even K v ϖ hϖ γ hγ D u hdet hD) s

private theorem relIndex_conjStabilizer_ne_zero_of_not_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : ¬ Even D) (s : GL (Fin 2) (v.adicCompletion K)) :
    (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0 := by
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := FixedOrInversion.exists_swap_of_not_even K v ϖ hϖ γ hγ D u hdet hD
  obtain ⟨hfinF, hcardF⟩ := (card_orbitalBall_sdiff_of_act_swap_of_isWithin_one (v.adicCompletionIntegers K)
    (v.adicCompletion K) ϖ hϖ γ x₀ x₁ hadj hne h₀ h₁).2.2 0
  refine TorusIndices.relIndex_conjStabilizer_ne_zero_of_stable K v γ hfinF ?_ ?_ s
  · have hcard0 : Nat.card
        ↥(orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero)
              (2 * 0 + 1) γ \
            orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero)
              (2 * 0) γ) ≠ 0 := by
      rw [hcardF]
      simp
    obtain ⟨⟨⟨x, hx⟩⟩, -⟩ := Nat.card_ne_zero.1 hcard0
    exact ⟨x, hx⟩
  · intro t ht x hx
    have htc : γ * t = t * γ :=
      (Subgroup.mem_centralizer_iff.1 (TorusIndices.unitCentralizer_le_centralizer K v γ ht)) γ rfl
    exact ⟨(act_mem_orbitalBall_iff _ _ htc x).2 hx.1, fun h => hx.2 ((act_mem_orbitalBall_iff _ _ htc x).1 h)⟩

private theorem relIndex_sup_center_ne_zero_of_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hrs : IsRegularSemisimple γ) (D : ℤ) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : Even D) :
    (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := hD
  have hdet' : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a) := by
    rw [two_mul, ← ha]
    exact hdet
  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple K v γ hrs
    ((heckeIndicator ℂ
      (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
        localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a)
      (finite_image_integralSubgroup_mul_singleton hϖ _) :
      HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
      GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hecke_finite_support K v _)
  exact relIndex_sup_center_ne_zero K v ϖ hϖ γ u a hdet'
    (FixedOrInversion.unitOrbitalCount_ne_zero_of_even K v ϖ hϖ γ hγ D u hdet ⟨a, ha⟩) _ S hS hcov

private theorem relIndex_sup_center_ne_zero_of_not_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hrs : IsRegularSemisimple γ) (D : ℤ) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : ¬ Even D) :
    (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := Int.not_even_iff_odd.mp hD
  have hdet' : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * a + ((1 : ℕ) : ℤ)) := by
    rw [Nat.cast_one, ← ha]
    exact hdet
  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple K v γ hrs
    ((heckeIndicator ℂ
      (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
        localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ (a + ((1 : ℕ) : ℤ)))
      (finite_image_integralSubgroup_mul_singleton hϖ _) :
      HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
      GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hecke_finite_support K v _)
  have hplug := card_sdiff_eq_relIndex_mul_sum_filter K v ϖ hϖ γ u a 1 le_rfl hdet' _ S hS hcov
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := FixedOrInversion.exists_swap_of_not_even K v ϖ hϖ γ hγ D u hdet hD
  have hcard := ((card_orbitalBall_sdiff_of_act_swap_of_isWithin_one (v.adicCompletionIntegers K)
    (v.adicCompletion K) ϖ hϖ γ x₀ x₁ hadj hne h₀ h₁).2.2 0).2
  intro h0
  rw [h0, zero_mul] at hplug
  have h2 : 2 * Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ 0 = 0 := by
    rw [← hcard]
    simpa using hplug
  simp at h2

private theorem unitOrbitalCount_eq_zero_of_not_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : ¬ Even D) : unitOrbitalCount (v.adicCompletionIntegers K) γ = 0 := by
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := FixedOrInversion.exists_swap_of_not_even K v ϖ hϖ γ hγ D u hdet hD
  have h := (card_orbitalBall_sdiff_of_act_swap_of_isWithin_one (v.adicCompletionIntegers K)
    (v.adicCompletion K) ϖ hϖ γ x₀ x₁ hadj hne h₀ h₁).1
  show Nat.card (fixedVertexSet (R := v.adicCompletionIntegers K) γ) = 0
  rw [h]
  simp

private theorem natCard_sphere_of_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : Even D) (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card
        ↥(orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) m γ \
          orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero)
            (m - 1) γ) : ℂ) =
      if Even m then
        ((unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ) *
              ((Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) - 1) + 2) *
          (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) ^ (m / 2 - 1)
      else 0 := by
  obtain ⟨hfin, hne⟩ := FixedOrInversion.finite_and_nonempty_fixedVertexSet_of_even K v ϖ hϖ γ hγ D u hdet hD
  have hD3F := card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty (v.adicCompletionIntegers K)
    (v.adicCompletion K) ϖ hϖ γ hfin hne
  split_ifs with hm2
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 2 := ⟨m / 2 - 1, by obtain ⟨e, rfl⟩ := hm2; omega⟩
    subst hr
    obtain ⟨-, hcard⟩ := hD3F.2 r
    have hq : 1 ≤ Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) :=
      Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega, hcard, show (2 * r + 2) / 2 - 1 = r by omega]
    push_cast [Nat.cast_sub hq]
    ring
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 1 := Nat.not_even_iff_odd.mp hm2
    subst hr
    rw [show 2 * r + 1 - 1 = 2 * r by omega, hD3F.1 r]
    simp

private theorem natCard_sphere_of_not_even (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (hD : ¬ Even D) (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card
        ↥(orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) m γ \
          orbitalBall (R := v.adicCompletionIntegers K) (unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero)
            (m - 1) γ) : ℂ) =
      if Even m then 0 else 2 * (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) ^ ((m - 1) / 2) := by
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := FixedOrInversion.exists_swap_of_not_even K v ϖ hϖ γ hγ D u hdet hD
  have hD3I := card_orbitalBall_sdiff_of_act_swap_of_isWithin_one (v.adicCompletionIntegers K)
    (v.adicCompletion K) ϖ hϖ γ x₀ x₁ hadj hne h₀ h₁
  split_ifs with hm2
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 2 := ⟨m / 2 - 1, by obtain ⟨e, rfl⟩ := hm2; omega⟩
    subst hr
    rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega, hD3I.2.1 r]
    simp
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 1 := Nat.not_even_iff_odd.mp hm2
    subst hr
    obtain ⟨-, hcard⟩ := hD3I.2.2 r
    rw [show 2 * r + 1 - 1 = 2 * r by omega, hcard, show 2 * r / 2 = r by omega]
    push_cast
    ring

private theorem shadow_single_mul_sat (D : ℤ) (C q : ℂ) (a : ℤ) (m : ℕ) :
    shadow D C (single (a, a) (1 : ℂ) * SatakeValues.sat q m) =
      if 2 * a + m = D then
        (if Even m then C * SatakeValues.satCoeff q m (m / 2) else 0) +
          2 * ∑ k ∈ Finset.range ((m + 1) / 2), SatakeValues.satCoeff q m k
      else 0 := by
  rw [SatakeValues.sat]
  exact shadow_single_mul_sum D C a m (SatakeValues.satCoeff q m)

private theorem shadow_single_mul_sat_of_eq (C q : ℂ) (a : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    shadow (2 * a + m) C (single (a, a) (1 : ℂ) * SatakeValues.sat q m) =
      (if Even m then C * ((q - 1) * q ^ (m / 2 - 1)) else 0) + 2 * q ^ ((m - 1) / 2) := by
  rw [shadow_single_mul_sat, if_pos rfl, SatakeValues.sum_satCoeff_range q (by omega : m ≠ 0)]
  split_ifs with hm2
  · obtain ⟨e, rfl⟩ : ∃ e, m = 2 * e := ⟨m / 2, by obtain ⟨r, rfl⟩ := hm2; omega⟩
    rw [show 2 * e / 2 = e by omega, SatakeValues.satCoeff_middle q (by omega : e ≠ 0)]
  · rfl

private theorem shadow_single_mul_sat_zero (D : ℤ) (C q : ℂ) (a : ℤ) :
    shadow D C (single (a, a) (1 : ℂ) * SatakeValues.sat q 0) = if 2 * a = D then C else 0 := by
  rw [shadow_single_mul_sat]
  simp [SatakeValues.satCoeff_zero_left]

private theorem orbitalIntegral_heckeIndicator_eq_shadow (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hrs : IsRegularSemisimple γ) (u : (v.adicCompletionIntegers K)ˣ) (D : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (S : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : S (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) =
      (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) • single ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : S (heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) = single ((1 : ℤ), (1 : ℤ)) 1)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (a b : ℤ) (hab : a ≤ b) {I : ℂ}
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      ((heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ b)
        (finite_image_integralSubgroup_mul_singleton hϖ _) :
        HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
        GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    I = (((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℂ) *
          ((τ ((TorusIndices.unitCentralizer K v γ).subgroupOf
              (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
            Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ))⁻¹ *
      shadow D (unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ)
        (S (heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ b)
          (finite_image_integralSubgroup_mul_singleton hϖ _))) := by
  classical

  obtain ⟨S₀, hS₀, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple K v γ hrs _
    (hecke_finite_support K v
      (heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ b)
        (finite_image_integralSubgroup_mul_singleton hϖ _)))
  have hIval : I = realisedValue K v γ τ
      ((heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ a *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) ^ b)
        (finite_image_integralSubgroup_mul_singleton hϖ _) :
        HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
        GL (Fin 2) (v.adicCompletion K) → ℂ) S₀ :=
    IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
      (isHaarMeasure_localHaar K v) γ hrs τ hτ _ (hecke_measurable K v _) (hecke_bounded K v _) hI
      (isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hrs τ hτ _
        (hecke_bi_invariant K v _) S₀ hS₀ hcov)

  have hSχ := SatakeValues.S_basis_of_le ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) hϖ
    (finite_image_integralSubgroup_mul_singleton hϖ) S hST hSc hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  ·
    rw [sub_self, Int.toNat_zero] at hSχ
    rw [hIval, hSχ, shadow_single_mul_sat_zero]
    by_cases hDa : 2 * a = D
    · subst hDa
      rw [if_pos rfl, realisedValue_heckeIndicator_eq_unitOrbitalCount_div K v ϖ hϖ γ u a hdet _ S₀ hS₀ hcov τ hτ
          (relIndex_conjStabilizer_ne_zero_of_even K v ϖ hϖ γ hγ _ u hdet (even_two_mul a))
          (relIndex_sup_center_ne_zero_of_even K v ϖ hϖ γ hγ hrs _ u hdet (even_two_mul a)), div_eq_inv_mul]
    · rw [if_neg hDa, mul_zero]
      exact realisedValue_heckeIndicator_eq_zero K v ϖ hϖ γ u D hdet a a (by rw [← two_mul]; exact hDa) τ _ S₀
  ·
    obtain ⟨n, hn⟩ := Int.le.dest hlt.le
    have hn1 : 1 ≤ n := by omega
    subst hn
    rw [add_sub_cancel_left, Int.toNat_natCast] at hSχ
    rw [hIval, hSχ]
    by_cases hDn : 2 * a + (n : ℤ) = D
    · subst hDn
      have hidx : ∀ s : GL (Fin 2) (v.adicCompletion K),
          (TorusIndices.conjStabilizer K v γ s).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0 := fun s => by
        by_cases hD : Even (2 * a + (n : ℤ))
        · exact relIndex_conjStabilizer_ne_zero_of_even K v ϖ hϖ γ hγ _ u hdet hD s
        · exact relIndex_conjStabilizer_ne_zero_of_not_even K v ϖ hϖ γ hγ _ u hdet hD s
      have hTZ : (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≠ 0 := by
        by_cases hD : Even (2 * a + (n : ℤ))
        · exact relIndex_sup_center_ne_zero_of_even K v ϖ hϖ γ hγ hrs _ u hdet hD
        · exact relIndex_sup_center_ne_zero_of_not_even K v ϖ hϖ γ hγ hrs _ u hdet hD
      rw [shadow_single_mul_sat_of_eq _ _ a n hn1,
        realisedValue_heckeIndicator_eq_card_div K v ϖ hϖ γ u a n hn1 hdet _ S₀ hS₀ hcov τ hτ hidx hTZ,
        div_eq_inv_mul]
      congr 1
      by_cases hD : Even (2 * a + (n : ℤ))
      · have hne : Even n := (Int.even_coe_nat n).mp ((Int.even_add.mp hD).mp (even_two_mul a))
        rw [natCard_sphere_of_even K v ϖ hϖ γ hγ _ u hdet hD n hn1, if_pos hne, if_pos hne]
        obtain ⟨e, rfl⟩ : ∃ e, n = 2 * e := ⟨n / 2, by obtain ⟨r, rfl⟩ := hne; omega⟩
        rw [show 2 * e / 2 - 1 = e - 1 by omega, show (2 * e - 1) / 2 = e - 1 by omega]
        ring
      · have hno : ¬ Even n := fun hne =>
          hD (Int.even_add.mpr ⟨fun _ => (Int.even_coe_nat n).mpr hne, fun _ => even_two_mul a⟩)
        rw [natCard_sphere_of_not_even K v ϖ hϖ γ hγ _ u hdet hD n hn1, if_neg hno, if_neg hno, zero_add]
    · rw [shadow_single_mul_sat, if_neg hDn, mul_zero]
      exact realisedValue_heckeIndicator_eq_zero K v ϖ hϖ γ u D hdet a (a + n)
        (fun h => hDn (by rw [← h]; ring)) τ _ S₀

end ShadowLink

section LinearExtension

p2m_open "LocalGL2 LT.LatticeTree~exists_act_stdVertex_eq MeasureTheory AddMonoidAlgebra"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem orbitalIntegral_zero (γ : GL (Fin 2) (v.adicCompletion K)) (hrs : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ) {J : ℂ}
    (hJ : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ (0 : GL (Fin 2) (v.adicCompletion K) → ℂ) J) :
    J = 0 := by
  have h0 := isOrbitalIntegralOn_localHaar_sum_div_of_forall_eq_of_forall_exists K v γ hrs τ hτ
    (0 : GL (Fin 2) (v.adicCompletion K) → ℂ) (fun _ _ _ _ _ => rfl) ∅ (fun _ h => absurd h (Finset.notMem_empty _))
    (fun _ h => absurd rfl h)
  rw [IsOrbitalIntegralOn.unique_of_isRegularSemisimple (v.adicCompletion K) (localHaar K v)
    (isHaarMeasure_localHaar K v) γ hrs τ hτ _ measurable_const ⟨0, fun _ => le_of_eq norm_zero⟩ hJ h0,
    Finset.sum_empty]

private noncomputable def shadowLinear {R₀ : Type*} [CommRing R₀] (D : ℤ) (C : R₀) : AddMonoidAlgebra R₀ (ℤ × ℤ) →ₗ[R₀] R₀
    where
  toFun := shadow D C
  map_add' := shadow_add D C
  map_smul' c F := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact shadow_smul D C c F

private theorem shadowLinear_apply {R₀ : Type*} [CommRing R₀] (D : ℤ) (C : R₀) (F : AddMonoidAlgebra R₀ (ℤ × ℤ)) :
    shadowLinear D C F = shadow D C F := rfl

private theorem orbitalIntegral_eq_of_basis (γ : GL (Fin 2) (v.adicCompletion K)) (hrs : IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (Φ : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₗ[ℂ] ℂ) {ι : Type} (bs :
        Module.Basis ι ℂ (HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ))
    (hbasis : ∀ (i : ι) (I : ℂ), IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      ((bs i : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) : GL (Fin 2)
          (v.adicCompletion K) → ℂ) I → I = Φ (bs i))
    (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) {I : ℂ}
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      ((f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) : GL (Fin 2)
          (v.adicCompletion K) → ℂ) I) :
    I = Φ f := by
  classical

  suffices key : ∀ (s : Finset ι) (c : ι → ℂ) (J : ℂ),
      IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
        ((∑ p ∈ s, c p • bs p : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
            GL (Fin 2) (v.adicCompletion K) → ℂ) J →
      J = Φ (∑ p ∈ s, c p • bs p) by
    have hf : f = ∑ p ∈ (bs.repr f).support, bs.repr f p • bs p := by
      conv_lhs => rw [← bs.linearCombination_repr f, Finsupp.linearCombination_apply]
      rfl
    rw [hf] at hI ⊢
    exact key _ _ _ hI
  intro s c
  induction s using Finset.induction_on with
  | empty =>
    intro J hJ
    rw [Finset.sum_empty, map_zero]
    rw [Finset.sum_empty] at hJ
    exact orbitalIntegral_zero K v γ hrs τ hτ hJ
  | insert p s hp ih =>
    intro J hJ
    rw [Finset.sum_insert hp] at hJ ⊢
    obtain ⟨I₁, hI₁⟩ := exists_isOrbitalIntegralOn K v γ hrs τ hτ (hecke_bi_invariant K v (c p • bs p))
      (hecke_finite_support K v (c p • bs p))
    obtain ⟨I₂, hI₂⟩ := exists_isOrbitalIntegralOn K v γ hrs τ hτ (hecke_bi_invariant K v (∑ p ∈ s, c p • bs p))
      (hecke_finite_support K v (∑ p ∈ s, c p • bs p))
    obtain ⟨I₃, hI₃⟩ := exists_isOrbitalIntegralOn K v γ hrs τ hτ (hecke_bi_invariant K v (bs p))
      (hecke_finite_support K v (bs p))
    have hsum : J = I₁ + I₂ :=
      orbitalIntegral_add K v γ hrs τ hτ (hecke_bi_invariant K v _) (hecke_bi_invariant K v _)
        (hecke_finite_support K v _) (hecke_finite_support K v _) (hecke_measurable K v _) (hecke_measurable K v _)
        (hecke_bounded K v _) (hecke_bounded K v _) hI₁ hI₂ hJ
    have hsmul : I₁ = c p * I₃ :=
      orbitalIntegral_smul K v γ hrs τ hτ (c p) (hecke_bi_invariant K v _) (hecke_finite_support K v _)
        (hecke_measurable K v _) (hecke_bounded K v _) hI₃ hI₁
    rw [hsum, hsmul, hbasis p I₃ hI₃, ih I₂ hI₂, map_add, map_smul, smul_eq_mul]

private theorem orbitalIntegral_eq_shadow (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})] (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hrs : IsRegularSemisimple γ) (u : (v.adicCompletionIntegers K)ˣ) (D : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (S : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : S (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) =
      (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) • single ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : S (heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) = single ((1 : ℤ), (1 : ℤ)) 1)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) {I : ℂ}
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    I = (((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℂ) *
          ((τ ((TorusIndices.unitCentralizer K v γ).subgroupOf
              (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
            Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ))⁻¹ *
      shadow D (unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ) (S f) := by
  classical

  have hidx : (TorusIndices.conjStabilizer K v γ 1).relIndex (TorusIndices.unitCentralizer K v γ) ≠ 0 := by
    by_cases hD : Even D
    · exact relIndex_conjStabilizer_ne_zero_of_even K v ϖ hϖ γ hγ D u hdet hD 1
    · exact relIndex_conjStabilizer_ne_zero_of_not_even K v ϖ hϖ γ hγ D u hdet hD 1
  have hm := measureReal_unitCentralizer_ne_zero K v γ τ hτ hidx
  have hTZ : (TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) ≠ 0 := by
    by_cases hD : Even D
    · exact relIndex_sup_center_ne_zero_of_even K v ϖ hϖ γ hγ hrs D u hdet hD
    · exact relIndex_sup_center_ne_zero_of_not_even K v ϖ hϖ γ hγ hrs D u hdet hD
  have hC : (fixedVertexSet (R := v.adicCompletionIntegers K) γ).Finite := by
    by_cases hD : Even D
    · exact (FixedOrInversion.finite_and_nonempty_fixedVertexSet_of_even K v ϖ hϖ γ hγ D u hdet hD).1
    · obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := FixedOrInversion.exists_swap_of_not_even K v ϖ hϖ γ hγ D u hdet hD
      rw [(card_orbitalBall_sdiff_of_act_swap_of_isWithin_one (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ hϖ γ
          x₀ x₁ hadj hne h₀ h₁).1]
      exact Set.finite_empty
  exact AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly K v ϖ hϖ (algebraMap_ne_zero_of_irreducible K
      v hϖ) (finite_image_integralSubgroup_mul_singleton hϖ) γ hγ u D hdet S hST hSc τ hτ hC hTZ hm f I hI

end LinearExtension

section TwistedSeam

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem thetaAut_mapGL_apply (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (y : GL (Fin 2) (w.1.adicCompletion L)) :
    (InertTransport.thetaAut K L σ v w hdeg e).mapGL y =
      Matrix.GeneralLinearGroup.map (theta K L σ v w e).toRingHom y :=
  Units.ext (Matrix.ext fun i j => by
    rw [IntegralAut.mapGL_apply, Matrix.GeneralLinearGroup.map_apply]
    rfl)

private theorem continuous_glEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Continuous (glEquiv K L v w e) := by
  have hmat : Continuous ((RingHom.mapMatrix e.toAlgHom.toRingHom).toMonoidHom :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) →* Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) :=
    continuous_id.matrix_map (continuous_algEquiv K L v w e)
  refine (Continuous.units_map _ hmat).congr fun g => ?_
  rw [glEquiv_apply]
  rfl

private theorem continuous_thetaAut_mapGL (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Continuous (InertTransport.thetaAut K L σ v w hdeg e).mapGL := by
  have hmat : Continuous ((RingHom.mapMatrix (theta K L σ v w e).toRingHom).toMonoidHom :
      Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L) →* Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) :=
    continuous_id.matrix_map (InertTransport.continuous_theta K L σ v w hdeg e)
  refine (Continuous.units_map _ hmat).congr fun g => ?_
  rw [thetaAut_mapGL_apply]
  rfl

private theorem isClosed_sigmaCentralizer_glEquiv (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsClosed (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ) :
      Set (GL (Fin 2) (w.1.adicCompletion L))) :=
  TwistedTorusIndices.isClosed_sigmaCentralizer _ _ (continuous_thetaAut_mapGL K L σ v w hdeg e)

private theorem glEquiv_twistedConj_mapGL (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (x δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) =
      (glEquiv K L v w e x)⁻¹ * glEquiv K L v w e δ *
        (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e x) := by
  rw [glEquiv_twistedConj, thetaAut_mapGL_apply]

private theorem mem_twistedCentralizer_iff_glEquiv_mem (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ ↔
      glEquiv K L v w e t ∈
        sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ) := by
  constructor
  · intro h
    rw [mem_sigmaCentralizer_iff] at h ⊢
    have h' := congrArg (glEquiv K L v w e) h
    rw [map_mul, map_mul, map_inv, glEquiv_sigmaGL] at h'
    rw [thetaAut_mapGL_apply]
    exact h'
  · intro h
    rw [mem_sigmaCentralizer_iff] at h ⊢
    apply (glEquiv K L v w e).injective
    rw [map_mul, map_mul, map_inv, glEquiv_sigmaGL, ← thetaAut_mapGL_apply K L σ v w hdeg e]
    exact h

private theorem comap_sigmaCentralizer_glEquiv (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)).comap
        (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L)) =
      twistedCentralizer K L (v.adicCompletion K) σ δ := by
  ext t
  rw [Subgroup.mem_comap, mem_twistedCentralizer_iff_glEquiv_mem K L σ v w hdeg e δ t]
  rfl

private theorem glEquiv_mem_integralUnitsSet_range_iff
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glEquiv K L v w e g ∈
        integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) ↔
      g ∈ semiLocalIntegralSet K L v := by
  rw [TwistedTorusIndices.integralUnitsSet_range_eq_localIntegralSet, localIntegralSet,
    integralUnitsSet_eq_integralSubgroup (w.1.adicCompletion L) (w.1.adicCompletionIntegers L), SetLike.mem_coe,
    mem_semiLocalIntegralSet_iff_glEquiv_mem K L v w e]

private theorem relIndex_comap_glEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (A B : Subgroup (GL (Fin 2) (w.1.adicCompletion L))) :
    (A.comap (glEquiv K L v w e :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).relIndex
      (B.comap (glEquiv K L v w e :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))) =
      A.relIndex B := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
  exact (glEquiv K L v w e).surjective

private theorem coe_subgroupOf_comap_twistedConjStabilizer (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ((((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) (glEquiv K L v w e s)).comap
        (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ) :
        Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
        Set (twistedCentralizer K L (v.adicCompletion K) σ δ)) =
      {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
        s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v} := by
  ext t
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_comap, Set.mem_setOf_eq,
    TwistedTorusIndices.mem_twistedConjStabilizer_iff, ← glEquiv_mem_integralUnitsSet_range_iff K L v w e, map_mul,
    map_mul, map_inv]
  exact ⟨fun h => h.2, fun h => ⟨(mem_twistedCentralizer_iff_glEquiv_mem K L σ v w hdeg e δ _).1 t.2, h⟩⟩

private theorem measurableSet_subgroupOf_comap_twistedConjStabilizer (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (s' : GL (Fin 2) (w.1.adicCompletion L)) :
    MeasurableSet[twistedCentralizerBorel K L (v.adicCompletion K) σ δ]
      ((((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
          (glEquiv K L v w e δ) s').comap
          (glEquiv K L v w e :
            GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ)) := by
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  rw [Subgroup.coe_subgroupOf, Subgroup.coe_subtype, Subgroup.coe_comap]
  exact (((TwistedTorusIndices.isCompact_twistedConjStabilizer _ _
    (isClosed_sigmaCentralizer_glEquiv K L σ v w hdeg e δ)
    (TwistedTorusIndices.isCompact_integralUnitsSet_range L w.1) s').isClosed.preimage
    (continuous_glEquiv K L v w e)).preimage continuous_subtype_val).measurableSet

open scoped Classical in

private theorem forall_image_glEquiv_of_forall (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∀ u ∈ semiLocalIntegralSet K L v, s' = t * s * u → s' = s) :
    ∀ s ∈ S.image (glEquiv K L v w e), ∀ s' ∈ S.image (glEquiv K L v w e),
      ∀ t ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ),
        ∀ u ∈ integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))),
          s' = t * s * u → s' = s := by
  classical
  intro s hs s' hs' t ht u hu h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hs
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hs'
  have ht' : (glEquiv K L v w e).symm t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ := by
    rw [mem_twistedCentralizer_iff_glEquiv_mem K L σ v w hdeg e, MulEquiv.apply_symm_apply]
    exact ht
  have hu' : (glEquiv K L v w e).symm u ∈ semiLocalIntegralSet K L v := by
    rw [← glEquiv_mem_integralUnitsSet_range_iff K L v w e, MulEquiv.apply_symm_apply]
    exact hu
  rw [hS a ha a' ha' _ ht' _ hu' ((glEquiv K L v w e).injective (by
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact h))]

open scoped Classical in

private theorem exists_image_glEquiv_of_exists (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (P : GL (Fin 2) (w.1.adicCompletion L) → Prop)
    (hcov : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      P (glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) →
        ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u) :
    ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      P (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) →
        ∃ s ∈ S.image (glEquiv K L v w e),
          ∃ t ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ),
            ∃ u ∈ integralUnitsSet
              (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))), x = t * s * u := by
  classical
  intro x hx
  have hx' : P (glEquiv K L v w e
      (((glEquiv K L v w e).symm x)⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ ((glEquiv K L v w e).symm x))) := by
    rw [glEquiv_twistedConj_mapGL K L σ v w hdeg e, MulEquiv.apply_symm_apply]
    exact hx
  obtain ⟨s, hs, t, ht, u, hu, hxe⟩ := hcov _ hx'
  refine ⟨glEquiv K L v w e s, Finset.mem_image_of_mem _ hs, glEquiv K L v w e t,
    (mem_twistedCentralizer_iff_glEquiv_mem K L σ v w hdeg e δ t).1 ht, glEquiv K L v w e u,
    (glEquiv_mem_integralUnitsSet_range_iff K L v w e u).2 hu, ?_⟩
  rw [← map_mul, ← map_mul, ← hxe, MulEquiv.apply_symm_apply]

end TwistedSeam

section TwistedPerBasis

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem isClosed_twistedCentralizer (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsClosed (twistedCentralizer K L (v.adicCompletion K) σ δ : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
  rw [← comap_sigmaCentralizer_glEquiv K L σ v w hdeg e δ, Subgroup.coe_comap]
  exact (isClosed_sigmaCentralizer_glEquiv K L σ v w hdeg e δ).preimage (continuous_glEquiv K L v w e)

private theorem coe_diagPi_zpow_mul_localRepInf_zpow_eq_diagonal (ϖ : w.1.adicCompletionIntegers L)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0) (b : ℤ) :
    ((diagPi ϖ hϖ0 ^ b * localRepInf ϖ hϖ0 ^ b : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      Matrix.diagonal ![algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ^ b,
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ^ b] := by
  rw [coe_diagPi_zpow_mul_localRepInf_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

open scoped Classical in

private theorem card_twisted_sdiff_eq_relIndex_mul_sum_filter (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hθϖ : (InertTransport.thetaAut K L σ v w hdeg e).toBase ϖ = ϖ)
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {ϖ})]
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (u : (w.1.adicCompletionIntegers L)ˣ) (a : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hdet : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) u *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ^ (2 * a + (m : ℤ)))
    (hfin) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∀ u ∈ semiLocalIntegralSet K L v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ (a + (m : ℤ))) hfin :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) :
          GL (Fin 2) (w.1.adicCompletion L) → ℂ)
        (glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u) :
    Nat.card
        ↥(twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) hϖ.ne_zero) m (glEquiv K L v w e δ)
            (InertTransport.thetaAut K L σ v w hdeg e) \
          twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) hϖ.ne_zero) (m - 1) (glEquiv K L v w e δ)
            (InertTransport.thetaAut K L σ v w hdeg e)) =
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
          (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) *
        ∑ s ∈ S with
            glEquiv K L v w e (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s) ∈
              doubleCoset (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
                (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a *
                  localRepInf ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ (a + (m : ℤ))),
          (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
              (glEquiv K L v w e s)).relIndex
            (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
              (glEquiv K L v w e δ)) := by
  have hD : doubleCoset (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ (algebraMap_ne_zero_of_irreducible L
            w.1 hϖ) ^ (a + (m : ℤ))) =
      integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) *
        ({weylInt (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) *
            (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ
                (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ (a + (m : ℤ))) *
          weylInt (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)} : Set (GL (Fin 2) (w.1.adicCompletion L))) *
          integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) := by
    rw [doubleCoset_basis_eq L w.1 ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) a (a + (m : ℤ)),
      TwistedTorusIndices.integralUnitsSet_range_eq_localIntegralSet]
  have hcov' := exists_image_glEquiv_of_exists K L σ v w hdeg e δ S
    (fun y => y ∈
      integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) *
        ({weylInt (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) *
            (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ
                (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ (a + (m : ℤ))) *
          weylInt (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)} : Set (GL (Fin 2) (w.1.adicCompletion L))) *
          integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))))
    fun x hx => hcov x (by
      rw [heckeIndicator_apply_of_mem hfin (by rw [hD]; exact hx)]
      exact one_ne_zero)
  rw [TwistedTorusIndices.card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_filter
    (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) ϖ hϖ hθϖ a m hm u hdet
    (weylInt (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) *
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ (algebraMap_ne_zero_of_irreducible L
            w.1 hϖ) ^ (a + (m : ℤ))) *
      weylInt (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
    (coe_weylInt_mul_mul_weylInt ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) a (a + (m : ℤ))) (S.image (glEquiv K L
        v w e))
    (forall_image_glEquiv_of_forall K L σ v w hdeg e δ S hS) hcov']
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_image fun x _ y _ h => (glEquiv K L v w e).injective h]
  refine Finset.sum_congr rfl fun s _ => if_congr ?_ rfl rfl
  rw [← glEquiv_twistedConj_mapGL K L σ v w hdeg e, hD]

open scoped Classical in

private theorem twistedUnitOrbitalCount_eq_relIndex_mul_sum_filter' (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hθϖ : (InertTransport.thetaAut K L σ v w hdeg e).toBase ϖ = ϖ)
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {ϖ})]
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (u : (w.1.adicCompletionIntegers L)ˣ) (a : ℤ)
    (hdet : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) u *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ^ (2 * a))
    (hfin) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∀ u ∈ semiLocalIntegralSet K L v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a *
            localRepInf ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a) hfin :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) :
          GL (Fin 2) (w.1.adicCompletion L) → ℂ)
        (glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u) :
    twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) =
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
          (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) *
        ∑ s ∈ S with
            glEquiv K L v w e (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s) ∈
              doubleCoset (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
                (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a *
                  localRepInf ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a),
          (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
              (glEquiv K L v w e s)).relIndex
            (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
              (glEquiv K L v w e δ)) := by
  have hD : doubleCoset (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ (algebraMap_ne_zero_of_irreducible L
            w.1 hϖ) ^ a) =
      integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) *
        ({diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ (algebraMap_ne_zero_of_irreducible
            L w.1 hϖ) ^ a} : Set (GL (Fin 2) (w.1.adicCompletion L))) *
          integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) := by
    rw [TwistedTorusIndices.integralUnitsSet_range_eq_localIntegralSet, localIntegralSet_eq]
    rfl
  have hcov' := exists_image_glEquiv_of_exists K L σ v w hdeg e δ S
    (fun y => y ∈
      integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) *
        ({diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ (algebraMap_ne_zero_of_irreducible
            L w.1 hϖ) ^ a} : Set (GL (Fin 2) (w.1.adicCompletion L))) *
          integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))))
    fun x hx => hcov x (by
      rw [heckeIndicator_apply_of_mem hfin (by rw [hD]; exact hx)]
      exact one_ne_zero)
  rw [TwistedTorusIndices.twistedUnitOrbitalCount_eq_relIndex_mul_sum_filter
    (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) ϖ hϖ hθϖ a u hdet
    (diagPi ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) ^ a * localRepInf ϖ (algebraMap_ne_zero_of_irreducible L w.1
        hϖ) ^ a)
    (coe_diagPi_zpow_mul_localRepInf_zpow_eq_diagonal K L v w ϖ (algebraMap_ne_zero_of_irreducible L w.1 hϖ) a)
        (S.image (glEquiv K L v w e))
    (forall_image_glEquiv_of_forall K L σ v w hdeg e δ S hS) hcov']
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_image fun x _ y _ h => (glEquiv K L v w e).injective h]
  refine Finset.sum_congr rfl fun s _ => if_congr ?_ rfl rfl
  rw [← glEquiv_twistedConj_mapGL K L σ v w hdeg e, hD]

private theorem comap_twistedUnitCentralizer_le (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)).comap
        (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L)) ≤
      twistedCentralizer K L (v.adicCompletion K) σ δ :=
  (Subgroup.comap_mono (TwistedTorusIndices.twistedUnitCentralizer_le _ _)).trans_eq
    (comap_sigmaCentralizer_glEquiv K L σ v w hdeg e δ)

private theorem twisted_relIndex_mul_measureReal_eq (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hidx : (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e s)).relIndex
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠
        0) :
    ((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e s)).relIndex
        (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) :
          ℝ) *
        (τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v}).toReal =
      (τ' ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
          (glEquiv K L v w e δ)).comap
          (glEquiv K L v w e :
            GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal := by
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := hτ'
  have hKT := comap_twistedUnitCentralizer_le K L σ v w hdeg e δ
  have hle : (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) (glEquiv K L v w e s)).comap
      (glEquiv K L v w e :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ)) ≤
      (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ)).comap
        (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ)) :=
    fun t ht => Subgroup.mem_subgroupOf.2 (Subgroup.mem_comap.2
      (TwistedTorusIndices.twistedConjStabilizer_le_twistedUnitCentralizer _ _ _
        (Subgroup.mem_comap.1 (Subgroup.mem_subgroupOf.1 ht))))
  have hidx' : (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) (glEquiv K L v w e s)).comap
      (glEquiv K L v w e :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ)).relIndex
      (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ)).comap
        (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ)) =
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e s)).relIndex
        (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
          (glEquiv K L v w e δ)) := by
    rw [Subgroup.relIndex_subgroupOf hKT, relIndex_comap_glEquiv]
  have hfin : (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) (glEquiv K L v w e s)).comap
      (glEquiv K L v w e :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ)).relIndex
      (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ)).comap
        (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ)) ≠ 0 := by
    rw [hidx']
    exact hidx
  have hmeas := measurableSet_subgroupOf_comap_twistedConjStabilizer K L σ v w hdeg e δ (glEquiv K L v w e s)
  have hm := TwistedTorusIndices.measure_coe_eq_relIndex_mul τ' hle hfin hmeas
  rw [coe_subgroupOf_comap_twistedConjStabilizer K L σ v w hdeg e δ s, hidx'] at hm
  rw [hm, ENNReal.toReal_mul, ENNReal.toReal_natCast]

private theorem twisted_measureReal_ne_zero (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hidx : (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        1).relIndex
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠
        0) :
    (τ' ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ)).comap
        (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
        (twistedCentralizer K L (v.adicCompletion K) σ δ) :
        Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
        Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal ≠ 0 := by
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := hτ'
  have hset : {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
      (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * 1 ∈
          semiLocalIntegralSet K L v} =
        Subtype.val ⁻¹' semiLocalIntegralSet K L v :=
    Set.ext fun t => by rw [Set.mem_setOf_eq, inv_one, one_mul, mul_one, Set.mem_preimage]
  have hS : (τ' {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
      (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * 1 ∈
          semiLocalIntegralSet K L v}).toReal ≠ 0 := by
    rw [hset]
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
    · refine (IsOpen.measure_pos τ' ((isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val)
        ⟨1, ?_⟩).ne'
      rw [Set.mem_preimage, OneMemClass.coe_one]
      exact one_mem_semiLocalIntegralSet K L v
    · exact ((isClosed_twistedCentralizer K L σ v w hdeg e δ).isClosedEmbedding_subtypeVal.isCompact_preimage
        (isCompact_semiLocalIntegralSet K L v)).measure_lt_top.ne
  have h := twisted_relIndex_mul_measureReal_eq K L σ v w hdeg e δ τ' hτ' 1 (by rwa [map_one])
  rw [map_one] at h
  rw [← h]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hidx) hS

end TwistedPerBasis

section TwistedTypes

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem act_mem_twistedOrbitalBall_iff {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    (θ : IntegralAut R F) (c : Fˣ) (n : ℕ) {δ' t : Matrix.GeneralLinearGroup (Fin 2) F}
    (ht : t ∈ sigmaCentralizer θ.mapGL δ') (x : Vertex R F) :
    Vertex.act t x ∈ twistedOrbitalBall c n δ' θ ↔ x ∈ twistedOrbitalBall c n δ' θ := by
  have key : ∀ s : Matrix.GeneralLinearGroup (Fin 2) F, s ∈ sigmaCentralizer θ.mapGL δ' → ∀ y : Vertex R F,
      y ∈ twistedOrbitalBall c n δ' θ → Vertex.act s y ∈ twistedOrbitalBall c n δ' θ := by
    intro s hs y hy
    rw [mem_twistedOrbitalBall] at hy ⊢
    rw [TwistedTorusIndices.twistedAct_act_of_mem θ δ' hs]
    exact FixedOrInversion.isWithin_act s hy
  refine ⟨fun h => ?_, key t ht x⟩
  have h' := key t⁻¹ (inv_mem ht) _ h
  rwa [FixedOrInversion.act_inv_act] at h'

private theorem twisted_eq_or_exists_swap (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) :
    (Even kδ ∧ twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) =
      unitOrbitalCount (v.adicCompletionIntegers K) γ) ∨
      (¬ Even kδ ∧ ∃ x₀ x₁ : Vertex (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Vertex.IsWithin (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w hw
            hϖ).ne_zero) 1
          x₀ x₁ ∧ x₀ ≠ x₁ ∧ Vertex.twistedAct (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) x₀ = x₁
              ∧
            Vertex.twistedAct (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) x₁ = x₀) :=
  FixedOrInversion.twistedUnitOrbitalCount_eq_or_exists_swap K v ϖ hϖ (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) (InertTransport.iota K L v w)
      (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (Module.finrank K L) hdeg.one_lt.le hres
          (InertTransport.thetaAut K L σ v w hdeg e)
      (InertTransport.thetaAut_toBase_iota K L σ v w hdeg e)
      (InertTransport.thetaAut_toBase_iterate_finrank K L σ v w hdeg e)
      (InertTransport.mem_range_iota_toBase_of_fixed K L σ v w hdeg hσ1 hw e) γ hγ D u hdet (glEquiv K L v w e δ) hnorm
          kδ uδ
      hdetδ hD

private theorem twistedUnitOrbitalCount_eq_of_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : Even kδ) :
    twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) = unitOrbitalCount
        (v.adicCompletionIntegers K) γ := by
  rcases twisted_eq_or_exists_swap K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD with ⟨-, h⟩ |
      ⟨hodd, -⟩
  · exact h
  · exact absurd hk hodd

private theorem twistedUnitOrbitalCount_ne_zero_of_even' (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : Even kδ) :
    twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) ≠ 0 := by
  rw [twistedUnitOrbitalCount_eq_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD hk]
  have hD' : Even D := by
    obtain ⟨b, hb⟩ := hk
    exact ⟨Module.finrank K L * b, by rw [hD, hb]; ring⟩
  exact FixedOrInversion.unitOrbitalCount_ne_zero_of_even K v ϖ hϖ γ hγ D u hdet hD'

private theorem exists_twisted_swap_of_not_even' (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : ¬ Even kδ) :
    ∃ x₀ x₁ : Vertex (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Vertex.IsWithin (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w hw
            hϖ).ne_zero) 1
          x₀ x₁ ∧ x₀ ≠ x₁ ∧ Vertex.twistedAct (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) x₀ = x₁
              ∧
            Vertex.twistedAct (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) x₁ = x₀ := by
  rcases twisted_eq_or_exists_swap K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD with ⟨heven,
      -⟩ | ⟨-, h⟩
  · exact absurd heven hk
  · exact h

private theorem finite_and_nonempty_twistedFixedVertexSet_of_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : Even kδ) :
    (twistedFixedVertexSet (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e)).Finite ∧
      (twistedFixedVertexSet (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e)).Nonempty := by
  obtain ⟨⟨⟨y, hy⟩⟩, hfin⟩ := Nat.card_ne_zero.1 (twistedUnitOrbitalCount_ne_zero_of_even' K L σ v w hdeg hσ1 e hw ϖ hϖ
      hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD hk)
  haveI := hfin
  exact ⟨Set.toFinite _, y, hy⟩

private theorem twisted_relIndex_ne_zero_of_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : Even kδ) (s : GL (Fin 2) (w.1.adicCompletion L)) :
    (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        s).relIndex
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠ 0
          :=
  TwistedTorusIndices.relIndex_twistedConjStabilizer_ne_zero _ _ (isClosed_sigmaCentralizer_glEquiv K L σ v w hdeg e δ)
    (TwistedTorusIndices.isCompact_integralUnitsSet_range L w.1) (TwistedTorusIndices.isOpen_integralUnitsSet_range L
        w.1)
    (twistedUnitOrbitalCount_ne_zero_of_even' K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD
        hk) s

private theorem twisted_relIndex_ne_zero_of_not_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : ¬ Even kδ) (s : GL (Fin 2) (w.1.adicCompletion L)) :
    (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        s).relIndex
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠ 0
          := by
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := exists_twisted_swap_of_not_even' K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u
      hdet δ hnorm kδ uδ hdetδ hD hk
  obtain ⟨hfinF, hcardF⟩ := (card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
      (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v w hw
        hϖ)
    (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) x₀ x₁ hadj hne h₀ h₁).2.2 0
  refine TwistedTorusIndices.relIndex_twistedConjStabilizer_ne_zero_of_stable _ _
    (isClosed_sigmaCentralizer_glEquiv K L σ v w hdeg e δ) (TwistedTorusIndices.isCompact_integralUnitsSet_range L w.1)
    (TwistedTorusIndices.isOpen_integralUnitsSet_range L w.1) hfinF ?_ ?_ s
  · have hcard0 : Nat.card
        ↥(twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w
            hw hϖ).ne_zero) (2 * 0 + 1)
            (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) \
          twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w
              hw hϖ).ne_zero) (2 * 0)
            (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e)) ≠ 0 := by
      rw [hcardF]
      simp
    obtain ⟨⟨⟨x, hx⟩⟩, -⟩ := Nat.card_ne_zero.1 hcard0
    exact ⟨x, hx⟩
  · intro t ht x hx
    have htc := TwistedTorusIndices.twistedUnitCentralizer_le _ _ ht
    exact ⟨(act_mem_twistedOrbitalBall_iff _ _ _ htc x).2 hx.1, fun h => hx.2 ((act_mem_twistedOrbitalBall_iff _ _ _
        htc x).1 h)⟩

private theorem exists_finset_comp_glEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    {χ : GL (Fin 2) (w.1.adicCompletion L) → ℂ}
    (hχ : ∃ F₀ : Finset (GL (Fin 2) (w.1.adicCompletion L)), ∀ g, χ g ≠ 0 → ∃ c ∈ F₀, c⁻¹ * g ∈ localIntegralSet L w.1)
        :
    ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ g, χ (glEquiv K L v w e g) ≠ 0 →
      ∃ c ∈ F₀, c⁻¹ * g ∈ semiLocalIntegralSet K L v := by
  classical
  obtain ⟨F₀, hF₀⟩ := hχ
  refine ⟨F₀.image (glEquiv K L v w e).symm, fun g hg => ?_⟩
  obtain ⟨c, hc, hcg⟩ := hF₀ _ hg
  refine ⟨(glEquiv K L v w e).symm c, Finset.mem_image_of_mem _ hc, ?_⟩
  rw [← glEquiv_mem_integralUnitsSet_range_iff K L v w e, map_mul, map_inv, MulEquiv.apply_symm_apply,
    TwistedTorusIndices.integralUnitsSet_range_eq_localIntegralSet]
  exact hcg

private theorem twisted_relIndex_sup_center_ne_zero_of_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hk : Even kδ) :
    (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := hk
  have hdet' : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
      (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ (2
            * b) := by
    rw [two_mul, ← hb]
    exact hdetδ
  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => ((heckeIndicator ℂ
      (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
          (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b *
        localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
      (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
      HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
          (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
    (exists_finset_comp_glEquiv K L v w e (hecke_finite_support L w.1 _))
  have h := twistedUnitOrbitalCount_eq_relIndex_mul_sum_filter' K L σ v w hdeg e ((InertTransport.iota K L v w).toBase
      ϖ)
    (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (InertTransport.thetaAut_toBase_iota K L σ v w hdeg e ϖ) δ
        uδ b hdet' _ S hS
    hcov
  intro h0
  rw [h0, zero_mul] at h
  exact twistedUnitOrbitalCount_ne_zero_of_even' K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD
      ⟨b, hb⟩ h

private theorem twisted_relIndex_sup_center_ne_zero_of_not_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hk : ¬ Even kδ) :
    (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := Int.not_even_iff_odd.mp hk
  have hdet' : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
      (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ (2
            * b + ((1 : ℕ) : ℤ)) := by
    rw [Nat.cast_one, ← hb]
    exact hdetδ
  obtain ⟨S, hS, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => ((heckeIndicator ℂ
      (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
          (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b *
        localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ (b + ((1 : ℕ) : ℤ)))
      (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
      HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
          (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
    (exists_finset_comp_glEquiv K L v w e (hecke_finite_support L w.1 _))
  have hplug := card_twisted_sdiff_eq_relIndex_mul_sum_filter K L σ v w hdeg e ((InertTransport.iota K L v w).toBase ϖ)
    (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (InertTransport.thetaAut_toBase_iota K L σ v w hdeg e ϖ) δ
        uδ b 1 le_rfl hdet' _
    S hS hcov
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := exists_twisted_swap_of_not_even' K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u
      hdet δ hnorm kδ uδ hdetδ hD hk
  have hcard := ((card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v w hw
        hϖ)
    (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) x₀ x₁ hadj hne h₀ h₁).2.2 0).2
  intro h0
  rw [h0, zero_mul] at hplug
  have h2 : 2 * Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) ^ 0 = 0
      := by
    rw [← hcard]
    simpa using hplug
  simp at h2

private theorem twistedUnitOrbitalCount_eq_zero_of_not_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : ¬ Even kδ) :
    twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) = 0 := by
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := exists_twisted_swap_of_not_even' K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u
      hdet δ hnorm kδ uδ hdetδ hD hk
  have h := (card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v w hw
        hϖ)
    (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) x₀ x₁ hadj hne h₀ h₁).1
  show Nat.card (twistedFixedVertexSet (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e)) = 0
  rw [h]
  simp

private theorem natCard_twisted_sphere_of_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : Even kδ) (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card
        ↥(twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w
            hw hϖ).ne_zero) m
            (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) \
          twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w
              hw hϖ).ne_zero) (m - 1)
            (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e)) : ℂ) =
      if Even m then
        ((twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ) *
              ((Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) : ℂ) - 1)
                  + 2) *
          (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) : ℂ) ^ (m / 2
              - 1)
      else 0 := by
  obtain ⟨hfin, hne⟩ := finite_and_nonempty_twistedFixedVertexSet_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u
      hdet δ hnorm kδ uδ hdetδ hD hk
  have hD3F := card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v w hw
        hϖ)
    (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) hfin hne
  split_ifs with hm2
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 2 := ⟨m / 2 - 1, by obtain ⟨c, rfl⟩ := hm2; omega⟩
    subst hr
    obtain ⟨-, hcard⟩ := hD3F.2 r
    have hq : 1 ≤ Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) :=
      Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega, hcard, show (2 * r + 2) / 2 - 1 = r by omega]
    push_cast [Nat.cast_sub hq]
    ring
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 1 := Nat.not_even_iff_odd.mp hm2
    subst hr
    rw [show 2 * r + 1 - 1 = 2 * r by omega, hD3F.1 r]
    simp

private theorem natCard_twisted_sphere_of_not_even (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ) (hk : ¬ Even kδ) (m : ℕ) (hm : 1 ≤ m) :
    (Nat.card
        ↥(twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w
            hw hϖ).ne_zero) m
            (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) \
          twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) (InertTransport.irreducible_iota_toBase K L v w
              hw hϖ).ne_zero) (m - 1)
            (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e)) : ℂ) =
      if Even m then 0 else 2 * (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v
          w).toBase ϖ}) : ℂ) ^ ((m - 1) / 2) := by
  obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := exists_twisted_swap_of_not_even' K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u
      hdet δ hnorm kδ uδ hdetδ hD hk
  have hD3I := card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v w hw
        hϖ)
    (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) x₀ x₁ hadj hne h₀ h₁
  split_ifs with hm2
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 2 := ⟨m / 2 - 1, by obtain ⟨c, rfl⟩ := hm2; omega⟩
    subst hr
    rw [show 2 * r + 2 - 1 = 2 * r + 1 by omega, hD3I.2.1 r]
    simp
  · obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 1 := Nat.not_even_iff_odd.mp hm2
    subst hr
    obtain ⟨-, hcard⟩ := hD3I.2.2 r
    rw [show 2 * r + 1 - 1 = 2 * r by omega, hcard, show 2 * r / 2 = r by omega]
    push_cast
    ring

end TwistedTypes

section TwistedBasisValue

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2 P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedValues"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem det_thetaAut_mapGL (hdeg : (Module.finrank K L).Prime) (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K]
    w.1.adicCompletion L) (y : GL (Fin 2) (w.1.adicCompletion L)) :
    Matrix.det (((InertTransport.thetaAut K L σ v w hdeg e).mapGL y : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin
        2) (Fin 2) (w.1.adicCompletion L)) =
      theta K L σ v w e (Matrix.det (y : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))) := by
  rw [thetaAut_mapGL_apply]
  exact (RingHom.map_det (theta K L σ v w e).toRingHom _).symm

private theorem det_coe_twistedConj (hdeg : (Module.finrank K L).Prime) (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K]
    w.1.adicCompletion L) (x δ' : GL (Fin 2) (w.1.adicCompletion L)) :
    Matrix.det ((x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      Matrix.det (δ' : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) *
        (theta K L σ v w e (Matrix.det (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))) *
          (Matrix.det (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))⁻¹) := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_thetaAut_mapGL, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  ring

private theorem exists_units_theta_mul_inv (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (ϖ' : (w.1.adicCompletionIntegers L))
    (hϖ' : Irreducible ϖ') (hθϖ' : (InertTransport.thetaAut K L σ v w hdeg e).toBase ϖ' = ϖ') {d : (w.1.adicCompletion
        L)}
    (hd : d ≠ 0) :
    ∃ w' : (w.1.adicCompletionIntegers L)ˣ, theta K L σ v w e d * d⁻¹ = ((w' : (w.1.adicCompletionIntegers L)) :
        (w.1.adicCompletion L)) := by
  have hint : ∀ x : (w.1.adicCompletionIntegers L), x ≠ 0 →
      ∃ w' : (w.1.adicCompletionIntegers L)ˣ,
        theta K L σ v w e (x : (w.1.adicCompletion L)) * (x : (w.1.adicCompletion L))⁻¹ = ((w' :
            (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L)) := by
    intro x hx
    obtain ⟨n, u₀, hxu⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.eq_pow_uniformizer_mul_unit L w.1 hx
      (InertTransport.valued_coe_eq_of_irreducible L w.1 hϖ')
    have hx0 : (x : (w.1.adicCompletion L)) ≠ 0 := fun h => hx (by exact_mod_cast h)
    have h1 : (InertTransport.thetaAut K L σ v w hdeg e).toBase x = ϖ' ^ n * (InertTransport.thetaAut K L σ v w hdeg
        e).toBase u₀ := by
      rw [hxu, map_mul, map_pow, hθϖ']
    have hθx : theta K L σ v w e (x : (w.1.adicCompletion L)) =
        (ϖ' : (w.1.adicCompletion L)) ^ n * (((InertTransport.thetaAut K L σ v w hdeg e).toBase u₀ :
            (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L)) := by
      rw [← InertTransport.thetaAut_toBase_coe K L σ v w hdeg e, h1]
      push_cast
      rfl
    have hxL : (x : (w.1.adicCompletion L)) = (ϖ' : (w.1.adicCompletion L)) ^ n * ((u₀ : (w.1.adicCompletionIntegers
        L)) : (w.1.adicCompletion L)) := by
      rw [hxu]
      push_cast
      rfl
    have hcast : (((u₀⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L))
        * ((u₀ : (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L)) = 1 := by
      exact_mod_cast u₀.inv_mul
    refine ⟨(u₀.isUnit.map (InertTransport.thetaAut K L σ v w hdeg e).toBase).unit * u₀⁻¹, ?_⟩
    rw [mul_inv_eq_iff_eq_mul₀ hx0, hθx, Units.val_mul, MulMemClass.coe_mul, IsUnit.unit_spec]
    conv_rhs => rw [hxL]
    rw [show (((InertTransport.thetaAut K L σ v w hdeg e).toBase u₀ : (w.1.adicCompletionIntegers L)) :
        (w.1.adicCompletion L)) * (((u₀⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : (w.1.adicCompletionIntegers L)) :
        (w.1.adicCompletion L)) *
        ((ϖ' : (w.1.adicCompletion L)) ^ n * ((u₀ : (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L))) =
        (ϖ' : (w.1.adicCompletion L)) ^ n * (((InertTransport.thetaAut K L σ v w hdeg e).toBase u₀ :
            (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L)) *
          ((((u₀⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L)) *
              ((u₀ : (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L))) by ring, hcast, mul_one]
  rcases ValuationSubring.mem_or_inv_mem (w.1.adicCompletionIntegers L) d with h | h
  · exact hint ⟨d, h⟩ fun h0 => hd (Subtype.ext_iff.mp h0)
  · obtain ⟨w', hw'⟩ := hint ⟨d⁻¹, h⟩ fun h0 => inv_ne_zero hd (Subtype.ext_iff.mp h0)
    refine ⟨w'⁻¹, ?_⟩
    have hw'' : theta K L σ v w e d * d⁻¹ = (((w' : (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L)))⁻¹ := by
      rw [← hw', map_inv₀, inv_inv, mul_inv_rev, inv_inv, mul_comm]
    rw [hw'']
    exact (eq_inv_of_mul_eq_one_left (by exact_mod_cast w'.inv_mul)).symm

open scoped Classical in

private theorem twistedRealisedValue_heckeIndicator (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (g : GL (Fin 2) (w.1.adicCompletion L)) (hfin) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (ι : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℕ) (m : ℝ) (hm : m ≠ 0)
    (hidx : ∀ s ∈ S, (ι s : ℝ) *
      (τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v}).toReal = m) :
    twistedRealisedValue K L v σ δ τ'
        (fun y => ((heckeIndicator ℂ g hfin : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L)
            (w.1.adicCompletion L)) ℂ) : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y)) S =
      (∑ s ∈ S with glEquiv K L v w e (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s) ∈
          doubleCoset (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) g,
        (ι s : ℂ)) / (m : ℂ) := by
  rw [twistedRealisedValue, Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  beta_reduce
  split_ifs with h
  · rw [heckeIndicator_apply_of_mem hfin h]
    have hidxs := hidx s hs
    have hτ0 : (τ' {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v}).toReal ≠
        0 := by
      intro h0
      rw [h0, mul_zero] at hidxs
      exact hm hidxs.symm
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hm), div_mul_eq_mul_div, one_mul,
      div_eq_iff (Complex.ofReal_ne_zero.mpr hτ0), ← hidxs, Complex.ofReal_mul, Complex.ofReal_natCast]
  · rw [heckeIndicator_apply_of_notMem hfin h, zero_div]

private theorem twistedRealisedValue_heckeIndicator_eq_zero (hdeg : (Module.finrank K L).Prime) (e : L ⊗[K] v.adicCompletion K
    ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (ϖ' : (w.1.adicCompletionIntegers L)) (hϖ' : Irreducible ϖ')
    (hθϖ' : (InertTransport.thetaAut K L σ v w hdeg e).toBase ϖ' = ϖ') (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (uδ
        : (w.1.adicCompletionIntegers L)ˣ) (kδ : ℤ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ * algebraMap (w.1.adicCompletionIntegers L)
          (w.1.adicCompletion L) ϖ' ^ kδ)
    (a c : ℤ) (hne : a + c ≠ kδ)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hfin) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :
    twistedRealisedValue K L v σ δ τ'
        (fun y => ((heckeIndicator ℂ
          (diagPi ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a *
            localRepInf ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ c) hfin :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y)) S = 0 := by
  rw [twistedRealisedValue]
  refine Finset.sum_eq_zero fun s _ => ?_
  beta_reduce
  rw [heckeIndicator_apply_of_notMem hfin ?_, zero_div]
  intro hmem
  obtain ⟨w₁, hw₁⟩ := exists_det_eq_mul_det_of_mem_doubleCoset L w.1 _ hmem
  have hs : Matrix.det ((glEquiv K L v w e s : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
      (w.1.adicCompletion L)) ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp (glEquiv K L v w e s).isUnit |>.ne_zero
  obtain ⟨w', hw'0⟩ := exists_units_theta_mul_inv K L σ v w hdeg e ϖ' hϖ' hθϖ' hs
  have hw' : theta K L σ v w e (Matrix.det ((glEquiv K L v w e s : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2)
      (Fin 2) (w.1.adicCompletion L))) *
      (Matrix.det ((glEquiv K L v w e s : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
          (w.1.adicCompletion L)))⁻¹ =
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) w' := hw'0
  rw [glEquiv_twistedConj_mapGL K L σ v w hdeg e, det_coe_twistedConj, hdetδ, hw',
    coe_diagPi_zpow_mul_localRepInf_zpow, Matrix.det_fin_two_of, mul_zero, sub_zero,
    ← zpow_add₀ (algebraMap_ne_zero_of_irreducible L w.1 hϖ')] at hw₁
  have h : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ↑(uδ * w') * algebraMap
      (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ' ^ kδ =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ↑w₁ * algebraMap (w.1.adicCompletionIntegers L)
          (w.1.adicCompletion L) ϖ' ^ (a + c) := by
    rw [← hw₁, Units.val_mul, map_mul]
    ring
  exact hne (zpow_exponent_unique L w.1 hϖ' (uδ * w') w₁ kδ (a + c) h).symm

open scoped Classical in

private theorem twistedRealisedValue_heckeIndicator_eq_card_div (hdeg : (Module.finrank K L).Prime) (e : L ⊗[K]
    v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (ϖ' : (w.1.adicCompletionIntegers L)) (hϖ' :
    Irreducible ϖ')
    (hθϖ' : (InertTransport.thetaAut K L σ v w hdeg e).toBase ϖ' = ϖ') [Finite (w.1.adicCompletionIntegers L ⧸
        Ideal.span {ϖ'})]
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (uδ : (w.1.adicCompletionIntegers L)ˣ) (a : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ * algebraMap (w.1.adicCompletionIntegers L)
          (w.1.adicCompletion L) ϖ' ^ (2 * a + (m : ℤ)))
    (hfin) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∀ u ∈ semiLocalIntegralSet K L v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a *
            localRepInf ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ (a + (m : ℤ))) hfin :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hidx : ∀ s' : GL (Fin 2) (w.1.adicCompletion L),
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          s').relIndex
        (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠
            0)
    (hTZ : (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) ≠ 0) :
    twistedRealisedValue K L v σ δ τ'
        (fun y => ((heckeIndicator ℂ
          (diagPi ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a *
            localRepInf ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ (a + (m : ℤ))) hfin :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y)) S =
      (Nat.card
          ↥(twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) hϖ'.ne_zero) m (glEquiv K L v w e δ)
              (InertTransport.thetaAut K L σ v w hdeg e) \
            twistedOrbitalBall (unitOfNeZero (K := w.1.adicCompletion L) hϖ'.ne_zero) (m - 1) (glEquiv K L v w e δ)
              (InertTransport.thetaAut K L σ v w hdeg e)) : ℂ) /
        (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
            ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ)) := by
  have hM := twisted_measureReal_ne_zero K L σ v w hdeg e δ τ' hτ' (hidx 1)
  have h1 := twistedRealisedValue_heckeIndicator K L σ v w e δ τ'
    (diagPi ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a *
      localRepInf ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ (a + (m : ℤ))) hfin S
    (fun s => (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
        δ)
        (glEquiv K L v w e s)).relIndex (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w
            hdeg e) (glEquiv K L v w e δ))) _ hM
    (fun s _ => twisted_relIndex_mul_measureReal_eq K L σ v w hdeg e δ τ' hτ' s (hidx _))
  have h2 := card_twisted_sdiff_eq_relIndex_mul_sum_filter K L σ v w hdeg e ϖ' hϖ' hθϖ' δ uδ a m hm hdetδ hfin S hS
      hcov
  have h0 : (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
      δ) ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hTZ
  rw [h1, h2, Nat.cast_mul, Nat.cast_sum, mul_div_mul_left _ _ h0]

open scoped Classical in

private theorem twistedRealisedValue_heckeIndicator_eq_twistedUnitOrbitalCount_div (hdeg : (Module.finrank K L).Prime) (e : L
    ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (ϖ' : (w.1.adicCompletionIntegers L)) (hϖ' :
    Irreducible ϖ')
    (hθϖ' : (InertTransport.thetaAut K L σ v w hdeg e).toBase ϖ' = ϖ') [Finite (w.1.adicCompletionIntegers L ⧸
        Ideal.span {ϖ'})]
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (uδ : (w.1.adicCompletionIntegers L)ˣ) (a : ℤ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ * algebraMap (w.1.adicCompletionIntegers L)
          (w.1.adicCompletion L) ϖ' ^ (2 * a))
    (hfin) (S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∀ u ∈ semiLocalIntegralSet K L v, s' = t * s * u → s' = s)
    (hcov : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ((heckeIndicator ℂ
          (diagPi ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a *
            localRepInf ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a) hfin :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) ≠ 0 →
        ∃ s ∈ S, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hidx : ∀ s' : GL (Fin 2) (w.1.adicCompletion L),
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          s').relIndex
        (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠
            0)
    (hTZ : (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) ≠ 0) :
    twistedRealisedValue K L v σ δ τ'
        (fun y => ((heckeIndicator ℂ
          (diagPi ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a *
            localRepInf ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a) hfin :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y)) S =
      (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ) /
        (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
            ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ)) := by
  have hM := twisted_measureReal_ne_zero K L σ v w hdeg e δ τ' hτ' (hidx 1)
  have h1 := twistedRealisedValue_heckeIndicator K L σ v w e δ τ'
    (diagPi ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a *
      localRepInf ϖ' (algebraMap_ne_zero_of_irreducible L w.1 hϖ') ^ a) hfin S
    (fun s => (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
        δ)
        (glEquiv K L v w e s)).relIndex (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w
            hdeg e) (glEquiv K L v w e δ))) _ hM
    (fun s _ => twisted_relIndex_mul_measureReal_eq K L σ v w hdeg e δ τ' hτ' s (hidx _))
  have h2 := twistedUnitOrbitalCount_eq_relIndex_mul_sum_filter' K L σ v w hdeg e ϖ' hϖ' hθϖ' δ uδ a hdetδ hfin S hS
      hcov
  have h0 : (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
      δ) ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hTZ
  rw [h1, h2, Nat.cast_mul, Nat.cast_sum, mul_div_mul_left _ _ h0]

end TwistedBasisValue

section TwistedShadowLink

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2 P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedValues AddMonoidAlgebra"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem measurable_glEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    @Measurable _ _ (glBorelOf (L ⊗[K] v.adicCompletion K)) (glBorelOf (w.1.adicCompletion L)) (glEquiv K L v w e) :=
        by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  letI := glBorelOf (w.1.adicCompletion L)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ⟨rfl⟩
  haveI : BorelSpace (GL (Fin 2) (w.1.adicCompletion L)) := ⟨rfl⟩
  exact (continuous_glEquiv K L v w e).measurable

variable (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)

private theorem twisted_hecke_measurable (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Measurable[glBorelOf (L ⊗[K] v.adicCompletion K)] fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L
        v w e y) :=
  (hecke_measurable L w.1 f).comp (measurable_glEquiv K L v w e)

private theorem twisted_hecke_bounded (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    ∃ C : ℝ, ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K), ‖(f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v
        w e y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := hecke_bounded L w.1 f
  exact ⟨C, fun y => hC _⟩

private theorem twisted_hecke_bi_invariant (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), ∀ u₁ ∈ semiLocalIntegralSet K L v, ∀ u₂ ∈ semiLocalIntegralSet K L v,
      (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e (u₁ * g * u₂)) = (f : GL (Fin 2)
          (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e g) := by
  intro g u₁ hu₁ u₂ hu₂
  have hU : ∀ u ∈ semiLocalIntegralSet K L v, glEquiv K L v w e u ∈ localIntegralSet L w.1 := fun u hu => by
    rw [← TwistedTorusIndices.integralUnitsSet_range_eq_localIntegralSet]
    exact (glEquiv_mem_integralUnitsSet_range_iff K L v w e u).2 hu
  rw [map_mul, map_mul]
  exact hecke_bi_invariant L w.1 f (glEquiv K L v w e g) _ (hU u₁ hu₁) _ (hU u₂ hu₂)

private theorem twisted_hecke_finite_support (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ g, (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K
        L v w e g) ≠ 0 →
      ∃ c ∈ F₀, c⁻¹ * g ∈ semiLocalIntegralSet K L v :=
  exists_finset_comp_glEquiv K L v w e (hecke_finite_support L w.1 f)

private theorem twistedOrbitalIntegral_zero (hσn : σ ^ Module.finrank K L = 1) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ') {J : ℂ}
    (hJ : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' (0 : GL (Fin 2) (L ⊗[K]
        v.adicCompletion K) → ℂ) J) :
    J = 0 := by
  have h0 := isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ'
    (0 : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (fun _ _ _ _ _ => rfl) ∅ (fun _ h => absurd h (Finset.notMem_empty
        _))
    (fun _ h => absurd rfl h)
  rw [IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ' _ measurable_const
      ⟨0, fun _ => le_of_eq norm_zero⟩ hJ h0,
    Finset.sum_empty]

private theorem twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_eq (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hσn : σ ^ Module.finrank K L = 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (a : ℤ) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      shadow kδ (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ)
        (SL (heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _))) :=
              by
  classical
  obtain ⟨S₀, hS₀, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
      (glEquiv K L v w e y))
    (twisted_hecke_finite_support K L v w
      (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a)
        (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) e)
  have hIval : I = twistedRealisedValue K L v σ δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) S₀ :=
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
        (glEquiv K L v w e y))
      (twisted_hecke_measurable K L v w _ e) (twisted_hecke_bounded K L v w _ e) hI
      (isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ'
        (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y))
        (twisted_hecke_bi_invariant K L v w _ e) S₀ hS₀ hcov)
  have hSχ := SatakeValues.S_basis_of_le ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
      w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) (InertTransport.irreducible_iota_toBase K L v w hw
      hϖ)
    (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) SL hST hSc
      (le_refl a)
  · rw [sub_self, Int.toNat_zero] at hSχ
    rw [hIval, hSχ, shadow_single_mul_sat_zero]
    by_cases hka : 2 * a = kδ
    · subst hka
      rw [if_pos rfl, twistedRealisedValue_heckeIndicator_eq_twistedUnitOrbitalCount_div K L σ v w hdeg e
          ((InertTransport.iota K L v w).toBase ϖ)
          (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (InertTransport.thetaAut_toBase_iota K L σ v w hdeg e
              ϖ) δ uδ a hdetδ _ S₀ hS₀ hcov τ' hτ'
          (fun s' => twisted_relIndex_ne_zero_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm (2 * a)
              uδ hdetδ hD (even_two_mul a) s')
          (twisted_relIndex_sup_center_ne_zero_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm (2 * a)
              uδ hdetδ hD hδ (even_two_mul a)),
        div_eq_inv_mul]
    · rw [if_neg hka, mul_zero]
      exact twistedRealisedValue_heckeIndicator_eq_zero K L σ v w hdeg e ((InertTransport.iota K L v w).toBase ϖ)
          (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (InertTransport.thetaAut_toBase_iota K L σ v w hdeg e
          ϖ) δ uδ kδ hdetδ a a
        (by rw [← two_mul]; exact hka) τ' _ S₀

private theorem
    twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt_ne
    (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hσn : σ ^ Module.finrank K L = 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (a b : ℤ) (hlt : a < b) (hne : a + b ≠ kδ) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      shadow kδ (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ)
        (SL (heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _))) :=
              by
  classical
  obtain ⟨S₀, hS₀, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
      (glEquiv K L v w e y))
    (twisted_hecke_finite_support K L v w
      (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
        (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) e)
  have hIval : I = twistedRealisedValue K L v σ δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) S₀ :=
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
        (glEquiv K L v w e y))
      (twisted_hecke_measurable K L v w _ e) (twisted_hecke_bounded K L v w _ e) hI
      (isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ'
        (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y))
        (twisted_hecke_bi_invariant K L v w _ e) S₀ hS₀ hcov)
  have hSχ := SatakeValues.S_basis_of_le ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
      w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) (InertTransport.irreducible_iota_toBase K L v w hw
      hϖ)
    (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) SL hST hSc
      hlt.le
  · obtain ⟨n, hn⟩ := Int.le.dest hlt.le
    have hn1 : 1 ≤ n := by omega
    subst hn
    rw [add_sub_cancel_left, Int.toNat_natCast] at hSχ
    rw [hIval, hSχ]
    have hkn : ¬ 2 * a + (n : ℤ) = kδ := fun h => hne (by rw [← h]; ring)
    rw [shadow_single_mul_sat, if_neg hkn, mul_zero]
    exact twistedRealisedValue_heckeIndicator_eq_zero K L σ v w hdeg e ((InertTransport.iota K L v w).toBase ϖ)
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (InertTransport.thetaAut_toBase_iota K L σ v w hdeg e
        ϖ) δ uδ kδ hdetδ a (a + n)
      (fun h => hkn (by rw [← h]; ring)) τ' _ S₀

private theorem
    twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt_even
    (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hσn : σ ^ Module.finrank K L = 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (a b : ℤ) (hlt : a < b) (hsum : a + b = kδ) (hev : Even (b - a)) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      shadow kδ (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ)
        (SL (heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _))) :=
              by
  classical
  obtain ⟨S₀, hS₀, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
      (glEquiv K L v w e y))
    (twisted_hecke_finite_support K L v w
      (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
        (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) e)
  have hIval : I = twistedRealisedValue K L v σ δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) S₀ :=
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
        (glEquiv K L v w e y))
      (twisted_hecke_measurable K L v w _ e) (twisted_hecke_bounded K L v w _ e) hI
      (isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ'
        (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y))
        (twisted_hecke_bi_invariant K L v w _ e) S₀ hS₀ hcov)
  have hSχ := SatakeValues.S_basis_of_le ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
      w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) (InertTransport.irreducible_iota_toBase K L v w hw
      hϖ)
    (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) SL hST hSc
      hlt.le
  · obtain ⟨n, hn⟩ := Int.le.dest hlt.le
    have hn1 : 1 ≤ n := by omega
    subst hn
    rw [add_sub_cancel_left, Int.toNat_natCast] at hSχ
    rw [hIval, hSχ]
    have hkn : 2 * a + (n : ℤ) = kδ := by rw [← hsum]; ring
    subst hkn
    have hk : Even (2 * a + (n : ℤ)) := Int.even_add.mpr ⟨fun _ => by simpa using hev, fun _ => even_two_mul a⟩
    have hidx : ∀ s' : GL (Fin 2) (w.1.adicCompletion L),
        (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
            s').relIndex (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
            (glEquiv K L v w e δ)) ≠ 0 := fun s' => by
      exact twisted_relIndex_ne_zero_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm _ uδ hdetδ hD
        hk s'
    have hTZ : (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v
        w e δ) ⊔
        Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
      (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) ≠ 0 := by
      exact twisted_relIndex_sup_center_ne_zero_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm _
        uδ hdetδ hD hδ hk
    have hval := twistedRealisedValue_heckeIndicator_eq_card_div K L σ v w hdeg e ((InertTransport.iota K L v
        w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (InertTransport.thetaAut_toBase_iota K L
        σ v w hdeg e ϖ) δ uδ a n hn1 hdetδ _ S₀ hS₀ hcov τ' hτ' hidx hTZ
    rw [shadow_single_mul_sat_of_eq _ _ a n hn1, hval, div_eq_inv_mul]
    congr 1
    have hne : Even n := (Int.even_coe_nat n).mp ((Int.even_add.mp hk).mp (even_two_mul a))
    have hcard := natCard_twisted_sphere_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm _ uδ hdetδ
        hD hk n hn1
    rw [hcard, if_pos hne, if_pos hne]
    obtain ⟨c, rfl⟩ : ∃ c, n = 2 * c := ⟨n / 2, by obtain ⟨r, rfl⟩ := hne; omega⟩
    rw [show 2 * c / 2 - 1 = c - 1 by omega, show (2 * c - 1) / 2 = c - 1 by omega]
    ring

private theorem
    twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt_odd
    (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hσn : σ ^ Module.finrank K L = 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (a b : ℤ) (hlt : a < b) (hsum : a + b = kδ) (hodd : ¬ Even (b - a)) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      shadow kδ (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ)
        (SL (heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _))) :=
              by
  classical
  obtain ⟨S₀, hS₀, hcov⟩ := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
      (glEquiv K L v w e y))
    (twisted_hecke_finite_support K L v w
      (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
        (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) e)
  have hIval : I = twistedRealisedValue K L v σ δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) S₀ :=
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
        (glEquiv K L v w e y))
      (twisted_hecke_measurable K L v w _ e) (twisted_hecke_bounded K L v w _ e) hI
      (isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ' hτ'
        (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
              HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y))
        (twisted_hecke_bi_invariant K L v w _ e) S₀ hS₀ hcov)
  have hSχ := SatakeValues.S_basis_of_le ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
      w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) (InertTransport.irreducible_iota_toBase K L v w hw
      hϖ)
    (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) SL hST hSc
      hlt.le
  · obtain ⟨n, hn⟩ := Int.le.dest hlt.le
    have hn1 : 1 ≤ n := by omega
    subst hn
    rw [add_sub_cancel_left, Int.toNat_natCast] at hSχ
    rw [hIval, hSχ]
    have hkn : 2 * a + (n : ℤ) = kδ := by rw [← hsum]; ring
    subst hkn
    have hk : ¬ Even (2 * a + (n : ℤ)) := fun h => hodd (by simpa using (Int.even_add.mp h).mp (even_two_mul a))
    have hidx : ∀ s' : GL (Fin 2) (w.1.adicCompletion L),
        (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
            s').relIndex (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
            (glEquiv K L v w e δ)) ≠ 0 := fun s' => by
      exact twisted_relIndex_ne_zero_of_not_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm _ uδ hdetδ
        hD hk s'
    have hTZ : (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v
        w e δ) ⊔
        Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
      (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) ≠ 0 := by
      exact twisted_relIndex_sup_center_ne_zero_of_not_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm
        _ uδ hdetδ hD hδ hk
    have hval := twistedRealisedValue_heckeIndicator_eq_card_div K L σ v w hdeg e ((InertTransport.iota K L v
        w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v w hw hϖ) (InertTransport.thetaAut_toBase_iota K L
        σ v w hdeg e ϖ) δ uδ a n hn1 hdetδ _ S₀ hS₀ hcov τ' hτ' hidx hTZ
    rw [shadow_single_mul_sat_of_eq _ _ a n hn1, hval, div_eq_inv_mul]
    congr 1
    have hno : ¬ Even n := fun hne =>
      hk (Int.even_add.mpr ⟨fun _ => (Int.even_coe_nat n).mpr hne, fun _ => even_two_mul a⟩)
    have hcard := natCard_twisted_sphere_of_not_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm _ uδ
        hdetδ hD hk n hn1
    rw [hcard, if_neg hno, if_neg hno, zero_add]

private theorem twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hσn : σ ^ Module.finrank K L = 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (a b : ℤ) (hlt : a < b) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      shadow kδ (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ)
        (SL (heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _))) :=
              by
  by_cases hsum : a + b = kδ
  · by_cases hev : Even (b - a)
    · exact twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet
        δ hnorm kδ uδ hdetδ hD hδ hσn SL hST hSc τ' hτ' a b hlt hsum hev hI
    · exact twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt_odd K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ
        hnorm kδ uδ hdetδ hD hδ hσn SL hST hSc τ' hτ' a b hlt hsum hev hI
  · exact twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt_ne K L σ v w hdeg e hw ϖ hϖ δ kδ uδ hdetδ hδ hσn SL hST
      hSc τ' hτ' a b hlt hsum hI

private theorem twistedOrbitalIntegral_heckeIndicator_eq_shadow (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hσn : σ ^ Module.finrank K L = 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (a b : ℤ) (hab : a ≤ b) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => ((heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _) :
          HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL (Fin 2)
              (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      shadow kδ (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ)
        (SL (heckeIndicator ℂ
          (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ a *
            localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
                (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) ^ b)
          (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _))) :=
              by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_eq K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm
      kδ uδ hdetδ hD hδ hσn SL hST hSc τ' hτ' _ hI
  · exact twistedOrbitalIntegral_heckeIndicator_eq_shadow_of_lt K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm
      kδ uδ hdetδ hD hδ hσn SL hST hSc τ' hτ' a b hlt hI

end TwistedShadowLink

section TwistedLinearExtension

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2 P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedValues AddMonoidAlgebra"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem twistedOrbitalIntegral_eq_of_basis (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (Φ : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₗ[ℂ] ℂ) {ι : Type}
        (bs : Module.Basis ι ℂ (HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
        ℂ))
    (hbasis : ∀ (i : ι) (I : ℂ), IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => ((bs i : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) : GL
          (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I → I = Φ (bs i))
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = Φ f := by
  classical
  suffices key : ∀ (s : Finset ι) (c : ι → ℂ) (J : ℂ),
      IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
        (fun y => ((∑ p ∈ s, c p • bs p : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L)
            (w.1.adicCompletion L)) ℂ) : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e y)) J →
      J = Φ (∑ p ∈ s, c p • bs p) by
    have hf : f = ∑ p ∈ (bs.repr f).support, bs.repr f p • bs p := by
      conv_lhs => rw [← bs.linearCombination_repr f, Finsupp.linearCombination_apply]
      rfl
    rw [hf] at hI ⊢
    exact key _ _ _ hI
  intro s c
  induction s using Finset.induction_on with
  | empty =>
    intro J hJ
    rw [Finset.sum_empty, map_zero]
    rw [Finset.sum_empty] at hJ
    exact twistedOrbitalIntegral_zero K L σ v hσn δ hδ τ' hτ' hJ
  | insert p s hp ih =>
    intro J hJ
    rw [Finset.sum_insert hp] at hJ ⊢
    obtain ⟨I₁, hI₁⟩ := exists_isTwistedOrbitalIntegralOn K L v σ δ hδ τ' hτ'
      (φ := fun y => ((c p • bs p : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion
          L)) ℂ) : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
      (twisted_hecke_bi_invariant K L v w (c p • bs p) e) (twisted_hecke_finite_support K L v w (c p • bs p) e)
    obtain ⟨I₂, hI₂⟩ := exists_isTwistedOrbitalIntegralOn K L v σ δ hδ τ' hτ'
      (φ := fun y => ((∑ p ∈ s, c p • bs p : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L)
          (w.1.adicCompletion L)) ℂ) : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
      (twisted_hecke_bi_invariant K L v w (∑ p ∈ s, c p • bs p) e)
      (twisted_hecke_finite_support K L v w (∑ p ∈ s, c p • bs p) e)
    obtain ⟨I₃, hI₃⟩ := exists_isTwistedOrbitalIntegralOn K L v σ δ hδ τ' hτ'
      (φ := fun y => ((bs p : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
          : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
      (twisted_hecke_bi_invariant K L v w (bs p) e) (twisted_hecke_finite_support K L v w (bs p) e)
    have hsum : J = I₁ + I₂ :=
      twistedOrbitalIntegral_add K L v σ hσn δ hδ τ' hτ'
        (φ := fun y => ((c p • bs p : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion
            L)) ℂ) : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
        (ψ := fun y => ((∑ p ∈ s, c p • bs p : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L)
            (w.1.adicCompletion L)) ℂ) : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
        (twisted_hecke_bi_invariant K L v w _ e) (twisted_hecke_bi_invariant K L v w _ e)
        (twisted_hecke_finite_support K L v w _ e) (twisted_hecke_finite_support K L v w _ e)
        (twisted_hecke_measurable K L v w _ e) (twisted_hecke_measurable K L v w _ e)
        (twisted_hecke_bounded K L v w _ e) (twisted_hecke_bounded K L v w _ e) hI₁ hI₂ hJ
    have hsmul : I₁ = c p * I₃ :=
      twistedOrbitalIntegral_smul K L v σ hσn δ hδ τ' hτ'
        (φ := fun y => ((bs p : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
            ℂ) : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) (c p)
        (twisted_hecke_bi_invariant K L v w _ e) (twisted_hecke_finite_support K L v w _ e)
        (twisted_hecke_measurable K L v w _ e) (twisted_hecke_bounded K L v w _ e) hI₃ hI₁
    rw [hsum, hsmul, hbasis p I₃ hI₃, ih I₂ hI₂, map_add, map_smul, smul_eq_mul]

private theorem twistedOrbitalIntegral_eq_shadow (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
    (hD : D = Module.finrank K L * kδ)
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ)) (hσn : σ ^ Module.finrank K L = 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I : ℂ}
    (hI : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ'
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I) :
    I = ((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        ⊔
          Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
        (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℕ) : ℂ) *
          ((τ' (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L
              v w e δ))).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) :
          Set (twistedCentralizer K L (v.adicCompletion K) σ δ))).toReal : ℂ))⁻¹ *
      shadow kδ (twistedUnitOrbitalCount (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e) : ℂ) (SL f)
          := by
  classical

  have hidx : (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
      δ) 1).relIndex (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K
      L v w e δ)) ≠ 0 := by
    by_cases hk : Even kδ
    · exact twisted_relIndex_ne_zero_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD hk
        1
    · exact twisted_relIndex_ne_zero_of_not_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD
        hk 1
  have hm := twisted_measureReal_ne_zero K L σ v w hdeg e δ τ' hτ' hidx
  have hTZ : (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
      δ) ⊔ Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex (sigmaCentralizer (InertTransport.thetaAut K L
      σ v w hdeg e).mapGL (glEquiv K L v w e δ)) ≠ 0 := by
    by_cases hk : Even kδ
    · exact twisted_relIndex_sup_center_ne_zero_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ
        hdetδ hD hδ hk
    · exact twisted_relIndex_sup_center_ne_zero_of_not_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ
        uδ hdetδ hD hδ hk
  have hC : (twistedFixedVertexSet (glEquiv K L v w e δ) (InertTransport.thetaAut K L σ v w hdeg e)).Finite := by
    by_cases hk : Even kδ
    · exact (finite_and_nonempty_twistedFixedVertexSet_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm
        kδ uδ hdetδ hD hk).1
    · obtain ⟨x₀, x₁, hadj, hne, h₀, h₁⟩ := exists_twisted_swap_of_not_even' K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u
        hdet δ hnorm kδ uδ hdetδ hD hk
      rw [(card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one (w.1.adicCompletionIntegers L)
          (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) (InertTransport.irreducible_iota_toBase K L v
          w hw hϖ) (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) x₀ x₁ hadj hne h₀ h₁).1]
      exact Set.finite_empty
  exact AutomorphicForm.twistedOrbitalIntegral_eq_shadow_of_irreducible_charpoly K L hdeg σ hσ1 hσn v w hw e
      (InertTransport.thetaAut K L σ v w hdeg e) (fun x => InertTransport.theta_apply K L σ v w e x) ϖ hϖ
      ((InertTransport.iota K L v w).toBase ϖ) (InertTransport.iota_toBase_coe K L v w ϖ)
      (algebraMap_ne_zero_of_irreducible L w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) hres
      (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) γ hγ δ
      (glEquiv K L v w e δ) (InertTransport.glEquiv_apply K L v w e δ) hnorm kδ uδ hdetδ SL hST hSc τ' hτ' hC hTZ hm f
      I hI

end TwistedLinearExtension

section UniformiserChange

open LocalGL2 HeckePair

variable (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

private noncomputable def unitDiag (ε : (v.adicCompletionIntegers K)ˣ) : GL (Fin 2) (v.adicCompletionIntegers K) :=
  ⟨!![(ε : v.adicCompletionIntegers K), 0; 0, 1], !![((ε⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers
      K), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private noncomputable def unitScalar (ε : (v.adicCompletionIntegers K)ˣ) : GL (Fin 2) (v.adicCompletionIntegers K) :=
  ⟨!![(ε : v.adicCompletionIntegers K), 0; 0, (ε : v.adicCompletionIntegers K)],
    !![((ε⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K), 0;
      0, ((ε⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem doubleCoset_mul_eq_of_mem {G : Type*} [Group G] (U : Subgroup G) (g : G) {u : G} (hu : u ∈ U) :
    doubleCoset U (g * u) = doubleCoset U g := by
  ext x
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, u * b, mul_mem hu hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, u⁻¹ * b, mul_mem (inv_mem hu) hb, by group⟩

private theorem heckeIndicator_eq_of_doubleCoset_eq {G : Type*} [Group G] {U : Subgroup G} {g g' : G}
    (h : doubleCoset U g = doubleCoset U g')
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite)
    (hfin' : (QuotientGroup.mk '' ((U : Set G) * {g'}) : Set (G ⧸ U)).Finite) :
    heckeIndicator ℂ g hfin = heckeIndicator ℂ g' hfin' := by
  apply Subtype.ext
  show (doubleCoset U g).indicator (1 : G → ℂ) = (doubleCoset U g').indicator 1
  rw [h]

private theorem diagPi_mul_unit (ϖ : v.adicCompletionIntegers K) (ε : (v.adicCompletionIntegers K)ˣ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖε0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ * ε) ≠ 0) :
    diagPi (ϖ * ε) hϖε0 =
      diagPi ϖ hϖ0 * Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) (unitDiag K v ε) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_diagPi, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitDiag, Matrix.mul_apply, Fin.sum_univ_two, map_mul]

private theorem diagPi_mul_localRepInf_mul_unit (ϖ : v.adicCompletionIntegers K) (ε : (v.adicCompletionIntegers K)ˣ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖε0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ * ε) ≠ 0) :
    diagPi (ϖ * ε) hϖε0 * localRepInf (ϖ * ε) hϖε0 =
      diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) (unitScalar K v ε) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_diagPi, coe_localRepInf, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitScalar, Matrix.mul_apply, Fin.sum_univ_two, map_mul]

private theorem doubleCoset_diagPi_eq (ϖ ϖ' : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ'0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ≠ 0) :
    doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) (diagPi ϖ' hϖ'0) =
      doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) (diagPi ϖ hϖ0) := by
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hϖ hϖ'
  have h0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ * ε) ≠ 0 := by rwa [hε]
  have key : diagPi ϖ' hϖ'0 = diagPi (ϖ * ε) h0 := by
    refine Units.ext ?_
    rw [coe_diagPi, coe_diagPi, hε]
  rw [key, diagPi_mul_unit K v ϖ ε hϖ0 h0]
  exact doubleCoset_mul_eq_of_mem _ _ (mem_integralSubgroup_iff.mpr ⟨unitDiag K v ε, rfl⟩)

private theorem doubleCoset_diagPi_mul_localRepInf_eq (ϖ ϖ' : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ'0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ≠ 0) :
    doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (diagPi ϖ' hϖ'0 * localRepInf ϖ' hϖ'0) =
      doubleCoset (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) := by
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hϖ hϖ'
  have h0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖ * ε) ≠ 0 := by rwa [hε]
  have key : diagPi ϖ' hϖ'0 * localRepInf ϖ' hϖ'0 = diagPi (ϖ * ε) h0 * localRepInf (ϖ * ε) h0 := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_diagPi, coe_diagPi, coe_localRepInf, coe_localRepInf, hε]
  rw [key, diagPi_mul_localRepInf_mul_unit K v ϖ ε hϖ0 h0]
  exact doubleCoset_mul_eq_of_mem _ _ (mem_integralSubgroup_iff.mpr ⟨unitScalar K v ε, rfl⟩)

private theorem natCard_quot_span_eq_of_irreducible (ϖ ϖ' : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ'}) = Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) :=
        by
  rw [natCard_quot_span_eq_absNorm v ϖ hϖ, natCard_quot_span_eq_absNorm v ϖ' hϖ']

end UniformiserChange

section UniformiserBridge

open NumberField LocalGL2 HeckePair
open scoped Pointwise

variable (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

private noncomputable def unitDiagPair (d₁ d₂ : (v.adicCompletionIntegers K)ˣ) :
    GL (Fin 2) (v.adicCompletionIntegers K) :=
  ⟨!![(d₁ : v.adicCompletionIntegers K), 0; 0, (d₂ : v.adicCompletionIntegers K)],
    !![((d₁⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K), 0;
      0, ((d₂⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem algebraMap_val_zpow (ε : (v.adicCompletionIntegers K)ˣ) (n : ℤ) :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        ((ε ^ n : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ε : v.adicCompletionIntegers K) ^ n := by
  have h1 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        ((ε ^ n : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) =
      ((Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom (ε ^ n) :
        (v.adicCompletion K)ˣ) : v.adicCompletion K) := rfl
  rw [h1]
  simp

private theorem upperTriangular_setOf_subset (d₁ d₂ : (v.adicCompletionIntegers K)ˣ) (x y : v.adicCompletion K) :
    {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
        ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
            x ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
            y} ⊆
      {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
          ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
              x * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (d₁ : v.adicCompletionIntegers K) ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
              y * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (d₂ : v.adicCompletionIntegers K)} := by
  rintro c ⟨g, rfl, h10, h00, h11⟩
  refine ⟨g * Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))
      (unitDiagPair K v d₁ d₂),
    QuotientGroup.mk_mul_of_mem g (mem_integralSubgroup_iff.mpr ⟨unitDiagPair K v d₁ d₂, rfl⟩), ?_, ?_, ?_⟩
  · simp [Units.val_mul, unitDiagPair, Matrix.mul_apply, Fin.sum_univ_two, h10]
  · simp [Units.val_mul, unitDiagPair, Matrix.mul_apply, Fin.sum_univ_two, h00]
  · simp [Units.val_mul, unitDiagPair, Matrix.mul_apply, Fin.sum_univ_two, h11]

private theorem upperTriangular_setOf_mul_unit_eq (x y : v.adicCompletion K) (d₁ d₂ : (v.adicCompletionIntegers K)ˣ) :
    {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
        ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
            x * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (d₁ : v.adicCompletionIntegers K) ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
            y * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (d₂ : v.adicCompletionIntegers K)} =
      {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
          ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
              x ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
              y} := by
  refine Set.Subset.antisymm ?_ (upperTriangular_setOf_subset K v d₁ d₂ x y)
  have h := upperTriangular_setOf_subset K v d₁⁻¹ d₂⁻¹
    (x * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (d₁ : v.adicCompletionIntegers K))
    (y * algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (d₂ : v.adicCompletionIntegers K))
  rwa [mul_assoc, mul_assoc, ← map_mul, ← map_mul, Units.mul_inv, Units.mul_inv, map_one, mul_one, mul_one] at h

private theorem upperTriangular_setOf_eq_of_irreducible (ϖ ϖ' : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (a b : ℤ) :
    {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
        ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ^ a ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ^ b} =
      {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
          ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
              algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a ∧
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
              algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b} := by
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hϖ hϖ'
  have h1 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ^ a =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          ((ε ^ a : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) := by
    rw [← hε, map_mul, mul_zpow, algebraMap_val_zpow]
  have h2 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ^ b =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
          ((ε ^ b : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) := by
    rw [← hε, map_mul, mul_zpow, algebraMap_val_zpow]
  rw [h1, h2]
  exact upperTriangular_setOf_mul_unit_eq K v _ _ (ε ^ a) (ε ^ b)

private theorem finsum_indicator_upperTriangular_eq_of_irreducible (ϖ ϖ' : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (a b : ℤ) :
    ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      Set.indicator
        {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' ^ b}
        (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c =
      ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
              ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
                (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
                (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                  algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a ∧
                (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                  algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c := by
  rw [upperTriangular_setOf_eq_of_irreducible K v ϖ ϖ' hϖ hϖ' a b]

private theorem constantTerm_transfer_of_irreducible (ϖ₁ ϖ₂ : v.adicCompletionIntegers K) (h₁ : Irreducible ϖ₁)
    (h₂ : Irreducible ϖ₂) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ₂})]
    {h₁0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ₁ ≠ 0}
    {hfinT : (QuotientGroup.mk ''
      ((integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Set (GL (Fin 2) (v.adicCompletion K))) *
        {diagPi ϖ₁ h₁0}) :
        Set (GL (Fin 2) (v.adicCompletion K) ⧸
          integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))).Finite}
    {hfinc : (QuotientGroup.mk ''
      ((integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Set (GL (Fin 2) (v.adicCompletion K))) *
        {diagPi ϖ₁ h₁0 * localRepInf ϖ₁ h₁0}) :
        Set (GL (Fin 2) (v.adicCompletion K) ⧸
          integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))).Finite}
    (S : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hS₁ : ∀ (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (a b : ℤ),
      (S f).coeff (a, b) =
        ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
          Set.indicator
            {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
                ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
                  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
                  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ₁ ^ a ∧
                  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ₁ ^ b}
            (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c)
    (hS₁T : S (heckeIndicator ℂ (diagPi ϖ₁ h₁0) hfinT) =
      AddMonoidAlgebra.single (1, 0) (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ₁}) : ℂ) +
        AddMonoidAlgebra.single (0, 1) 1)
    (hS₁c : S (heckeIndicator ℂ (diagPi ϖ₁ h₁0 * localRepInf ϖ₁ h₁0) hfinc) = AddMonoidAlgebra.single (1, 1) 1) :
    (∀ (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (a b : ℤ),
      (S f).coeff (a, b) =
        ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
          Set.indicator
            {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
                ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
                  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
                  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ₂ ^ a ∧
                  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ₂ ^ b}
            (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c) ∧
    S (heckeIndicator ℂ (diagPi ϖ₂ (algebraMap_ne_zero_of_irreducible K v h₂))
        (finite_image_integralSubgroup_mul_singleton h₂ _)) =
      (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ₂}) : ℂ) •
          AddMonoidAlgebra.single ((1 : ℤ), (0 : ℤ)) 1 +
        AddMonoidAlgebra.single ((0 : ℤ), (1 : ℤ)) 1 ∧
    S (heckeIndicator ℂ
        (diagPi ϖ₂ (algebraMap_ne_zero_of_irreducible K v h₂) *
          localRepInf ϖ₂ (algebraMap_ne_zero_of_irreducible K v h₂))
        (finite_image_integralSubgroup_mul_singleton h₂ _)) = AddMonoidAlgebra.single ((1 : ℤ), (1 : ℤ)) 1 := by
  refine ⟨fun f a b => (hS₁ f a b).trans
    (finsum_indicator_upperTriangular_eq_of_irreducible K v ϖ₁ ϖ₂ h₁ h₂ f a b).symm, ?_, ?_⟩
  · rw [heckeIndicator_eq_of_doubleCoset_eq
        (doubleCoset_diagPi_eq K v ϖ₁ ϖ₂ h₁ h₂ h₁0 (algebraMap_ne_zero_of_irreducible K v h₂))
        (finite_image_integralSubgroup_mul_singleton h₂ _) hfinT,
      hS₁T, natCard_quot_span_eq_of_irreducible K v ϖ₂ ϖ₁ h₂ h₁, AddMonoidAlgebra.smul_single', mul_one]
  · rw [heckeIndicator_eq_of_doubleCoset_eq
        (doubleCoset_diagPi_mul_localRepInf_eq K v ϖ₁ ϖ₂ h₁ h₂ h₁0 (algebraMap_ne_zero_of_irreducible K v h₂))
        (finite_image_integralSubgroup_mul_singleton h₂ _) hfinc,
      hS₁c]

end UniformiserBridge

section UniformiserBridgeUpstairs

open NumberField
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem natCard_quot_iota_eq_pow
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) {ϖ : v.adicCompletionIntegers K}
    (hϖ : Irreducible ϖ) :
    Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L := by
  rw [natCard_quot_span_eq_absNorm w.1 _ (InertTransport.irreducible_iota_toBase K L v w hw hϖ),
    natCard_quot_span_eq_absNorm v ϖ hϖ, absNorm_eq_pow K L v w hw e]

private theorem finite_quot_iota_toBase
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) :
    Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) :=
  finite_quotient_span L w.1 _ (InertTransport.irreducible_iota_toBase K L v w hw hϖ)

end UniformiserBridgeUpstairs

section NormalisingConstants

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem measurableSet_coe_of_relIndex_ne_zero {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    {H H' : Subgroup G} (hHK : H ≤ H') (hH : MeasurableSet (H : Set G)) (hidx : H.relIndex H' ≠ 0) :
    MeasurableSet (H' : Set G) := by
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hidx⟩
  have key : (H' : Set G) =
      ⋃ q : H' ⧸ H.subgroupOf H', (fun x => ((q.out : H') : G)⁻¹ * x) ⁻¹' (H : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      exact ⟨QuotientGroup.mk ⟨x, hx⟩, Subgroup.mem_subgroupOf.1
        (QuotientGroup.eq.1 (QuotientGroup.mk (s := H.subgroupOf H') (⟨x, hx⟩ : H')).out_eq')⟩
    · rintro ⟨q, hq⟩
      rw [← mul_inv_cancel_left ((q.out : H') : G) x]
      exact H'.mul_mem (q.out : H').2 (hHK hq)
  rw [key]
  exact MeasurableSet.iUnion fun q => measurable_const_mul _ hH

private theorem algebraMap_tensor_injective (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    Function.Injective (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) := by
  haveI : Nontrivial (L ⊗[K] v.adicCompletion K) := e.symm.injective.nontrivial
  exact (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)).injective

private theorem sigmaTensor_iterate_finrank (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (z : L ⊗[K] v.adicCompletion K) :
    (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[Module.finrank K L] z = z := by
  apply e.injective
  have key : ∀ (k : ℕ) (z : L ⊗[K] v.adicCompletion K),
      e ((⇑(sigmaTensor K L (v.adicCompletion K) σ))^[k] z) = (⇑(theta K L σ v w e))^[k] (e z) := by
    intro k
    induction k with
    | zero => intro z; rfl
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, theta_apply,
        AlgEquiv.symm_apply_apply]
  rw [key]
  exact InertTransport.theta_iterate_finrank K L σ v w hdeg e (e z)

private theorem mem_range_algebraMap_of_sigmaTensor_eq (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (z : L ⊗[K] v.adicCompletion K)
    (hz : sigmaTensor K L (v.adicCompletion K) σ z = z) :
    z ∈ Set.range (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) := by
  have hθ : InertTransport.thetaAlg K L σ v w e (e z) = e z := by
    rw [InertTransport.thetaAlg_apply, theta_apply, AlgEquiv.symm_apply_apply, hz]
  obtain ⟨c, hc⟩ := (InertTransport.thetaAlg_apply_eq_self_iff K L σ v w hdeg hσ1 e (e z)).1 hθ
  refine ⟨c, e.injective ?_⟩
  rw [AlgEquiv.commutes, hc]

private theorem det_glEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (g : GL (Fin 2) (L ⊗[K]
    v.adicCompletion K)) :
    Matrix.det ((glEquiv K L v w e g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion
        L)) =
      e (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
  have hcoe : ((glEquiv K L v w e g : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion
      L)) =
      (e.toAlgHom.toRingHom).mapMatrix (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    Matrix.ext fun i j => by rw [glEquiv_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply]
  rw [hcoe, ← RingHom.map_det]
  rfl

private theorem exists_units_eq_algebraMap_iff (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (d : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) d ∈
        {z : L ⊗[K] v.adicCompletion K | ∃ w' : (w.1.adicCompletionIntegers L)ˣ, e z = algebraMap
            (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) w'} ↔
      d ∈ {d : v.adicCompletion K | ∃ u : (v.adicCompletionIntegers K)ˣ, d = algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K) u} := by
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, AlgEquiv.commutes]
  constructor
  · rintro ⟨w', hw'⟩
    have hdesc : ∀ x : (w.1.adicCompletionIntegers L), (x : (w.1.adicCompletion L)) ∈ Set.range (algebraMap
        (v.adicCompletion K) (w.1.adicCompletion L)) →
        ∃ y : (v.adicCompletionIntegers K), (InertTransport.iota K L v w).toBase y = x := by
      rintro x ⟨c, hc⟩
      refine InertTransport.mem_range_iota_toBase_of_fixed K L σ v w hdeg hσ1 hw e x (Subtype.ext ?_)
      rw [InertTransport.thetaAut_toBase_coe, ← hc, InertTransport.theta_algebraMap]
    obtain ⟨y, hy⟩ := hdesc (w' : (w.1.adicCompletionIntegers L)) ⟨d, by rw [hw', ValuationSubring.algebraMap_apply]⟩
    have hW : (((w'⁻¹ : ((w.1.adicCompletionIntegers L))ˣ) : (w.1.adicCompletionIntegers L)) : (w.1.adicCompletion L))
        = (((w' : (w.1.adicCompletionIntegers L))) : (w.1.adicCompletion L))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by exact_mod_cast w'.inv_mul)
    obtain ⟨y', hy'⟩ := hdesc ((w'⁻¹ : ((w.1.adicCompletionIntegers L))ˣ) : (w.1.adicCompletionIntegers L))
      ⟨d⁻¹, by rw [map_inv₀, hw', ValuationSubring.algebraMap_apply, hW]⟩
    have hinjι : Function.Injective (InertTransport.iota K L v w).toBase := fun a b h =>
      Subtype.ext ((algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective
        (by rw [← InertTransport.iota_toBase_coe, ← InertTransport.iota_toBase_coe, h]))
    have hyy' : y * y' = 1 := hinjι (by rw [map_mul, hy, hy', map_one, Units.mul_inv])
    refine ⟨Units.mkOfMulEqOne y y' hyy', ?_⟩
    rw [Units.val_mkOfMulEqOne, ValuationSubring.algebraMap_apply]
    apply (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective
    rw [← InertTransport.iota_toBase_coe, hy]
    rw [ValuationSubring.algebraMap_apply] at hw'
    exact hw'
  · rintro ⟨u, rfl⟩
    exact ⟨Units.map ((InertTransport.iota K L v w).toBase : (v.adicCompletionIntegers K) →+*
        (w.1.adicCompletionIntegers L)).toMonoidHom u, by
      rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ValuationSubring.algebraMap_apply,
        ValuationSubring.algebraMap_apply, InertTransport.iota_toBase_coe]⟩

private theorem comap_twistedUnitCentralizer_eq_map (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (γ : GL (Fin 2) (v.adicCompletion K))
    (hrs : IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L
        (v.adicCompletion K) σ γ δ 1) :
    (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)).comap
        (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L)) =
      (TorusIndices.unitCentralizer K v γ).map (toTensorGL K L (v.adicCompletion K)) := by
  have hT := comap_sigmaCentralizer_glEquiv K L σ v w hdeg e δ
  ext t
  rw [Subgroup.mem_comap, MonoidHom.coe_coe, TwistedTorusIndices.mem_twistedUnitCentralizer_iff, Subgroup.mem_map]
  have h1 : glEquiv K L v w e t ∈ (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e
      δ)) ↔
      t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ := by
    rw [← hT, Subgroup.mem_comap, MonoidHom.coe_coe]
  have h2 : (∃ w' : ((w.1.adicCompletionIntegers L))ˣ, Matrix.det ((glEquiv K L v w e t : GL (Fin 2)
      (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) w') ↔
      Matrix.det (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
        {z : L ⊗[K] v.adicCompletion K | ∃ w' : (w.1.adicCompletionIntegers L)ˣ, e z = algebraMap
            (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) w'} := by
    rw [Set.mem_setOf_eq, det_glEquiv]
  rw [h1, h2, CoupledTransport.mem_twistedCentralizer_and_det_mem_iff (σ := σ)
    (mem_range_algebraMap_of_sigmaTensor_eq K L σ v w hdeg hσ1 e) (algebraMap_tensor_injective K L v w e)
    (sigmaTensor_iterate_finrank K L σ v w hdeg e) hrs hN (exists_units_eq_algebraMap_iff K L σ v w hdeg hσ1 hw e) t]
  constructor
  · rintro ⟨t₀, ht₀, hdet₀, rfl⟩
    exact ⟨t₀, (TorusIndices.mem_unitCentralizer_iff K v γ t₀).2 ⟨ht₀, hdet₀⟩, rfl⟩
  · rintro ⟨t₀, ht₀, rfl⟩
    obtain ⟨h₀, hdet₀⟩ := (TorusIndices.mem_unitCentralizer_iff K v γ t₀).1 ht₀
    exact ⟨t₀, h₀, hdet₀, rfl⟩

private theorem comap_center_glEquiv (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    (Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).comap
        (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L)) =
      Subgroup.center (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
  ext t
  rw [Subgroup.mem_comap, MonoidHom.coe_coe, Subgroup.mem_center_iff, Subgroup.mem_center_iff,
    (glEquiv K L v w e).surjective.forall]
  refine forall_congr' fun g => ?_
  rw [← map_mul, ← map_mul, (glEquiv K L v w e).injective.eq_iff]

private theorem twisted_relIndex_sup_center_eq (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (γ : GL (Fin 2) (v.adicCompletion K))
    (hrs : IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L
        (v.adicCompletion K) σ γ δ 1) :
    (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ⊔
            Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
          (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℂ) =
      ((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℂ) := by
  rw [← relIndex_comap_glEquiv K L v w e, comap_sigmaCentralizer_glEquiv K L σ v w hdeg e δ,
    ← Subgroup.comap_sup_eq (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →*
        GL (Fin 2) (w.1.adicCompletion L)) _ _ (glEquiv K L v w e).surjective, comap_center_glEquiv K L v w e,
    comap_twistedUnitCentralizer_eq_map K L σ v w hdeg hσ1 hw e γ hrs δ hN]
  exact_mod_cast CoupledTransport.relIndex_sup_center_eq (σ := σ)
    (mem_range_algebraMap_of_sigmaTensor_eq K L σ v w hdeg hσ1 e) (algebraMap_tensor_injective K L v w e)
    (sigmaTensor_iterate_finrank K L σ v w hdeg e) hrs hN (TorusIndices.unitCentralizer_le_centralizer K v γ) rfl

private theorem measurableSet_comap_twistedUnitCentralizer (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (δ : GL (Fin 2) (L ⊗[K]
        v.adicCompletion K))
    (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hidx : (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e s)).relIndex
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠
          0) :
    MeasurableSet[glBorelOf (L ⊗[K] v.adicCompletion K)]
      (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
          δ)).comap
          (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L)) : Subgroup (GL (Fin 2) (L ⊗[K]
              v.adicCompletion K))) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  refine measurableSet_coe_of_relIndex_ne_zero
    (H := (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e s)).comap
      (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L)))
    (Subgroup.comap_mono (TwistedTorusIndices.twistedConjStabilizer_le_twistedUnitCentralizer _ _ _)) ?_ ?_
  · rw [Subgroup.coe_comap]
    exact ((TwistedTorusIndices.isCompact_twistedConjStabilizer _ _ (isClosed_sigmaCentralizer_glEquiv K L σ v w hdeg e
        δ)
      (TwistedTorusIndices.isCompact_integralUnitsSet_range L w.1) _).isClosed.preimage
      (continuous_glEquiv K L v w e)).measurableSet
  · rwa [relIndex_comap_glEquiv]

private theorem twisted_measure_comap_twistedUnitCentralizer_eq (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (γ : GL (Fin 2) (v.adicCompletion K))
    (hrs : IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L
        (v.adicCompletion K) σ γ δ 1)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) (centralizerBorel
        (v.adicCompletion K) γ))
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ) (twistedCentralizerBorel K L (v.adicCompletion K)
        σ δ))
    (hc : Coupled K L (v.adicCompletion K) σ γ δ 1 τ τ₁) (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hidx : (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e s)).relIndex
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠
          0) :
    τ₁ (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e
        δ))).comap
          (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf (twistedCentralizer
              K L (v.adicCompletion K) σ δ) :
          Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) : Set (twistedCentralizer K L (v.adicCompletion
              K) σ δ)) =
      τ ((TorusIndices.unitCentralizer K v γ).subgroupOf (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion
          K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  have h := CoupledTransport.measure_preimage_eq_of_coupled_one (σ := σ) hc
    (measurableSet_comap_twistedUnitCentralizer K L σ v w hdeg e δ s hidx)
  rw [Subgroup.coe_subgroupOf, Subgroup.coe_subtype, Subgroup.coe_subgroupOf, Subgroup.coe_subtype]
  convert h using 2
  ext t₀
  rw [Set.mem_preimage, Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe,
    comap_twistedUnitCentralizer_eq_map K L σ v w hdeg hσ1 hw e γ hrs δ hN,
    Subgroup.mem_map_iff_mem (CoupledTransport.toTensorGL_injective (K := K) (L := L)
      (algebraMap_tensor_injective K L v w e))]

private theorem twisted_kappa_eq (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (γ : GL (Fin 2) (v.adicCompletion K))
    (hrs : IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L
        (v.adicCompletion K) σ γ δ 1)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) (centralizerBorel
        (v.adicCompletion K) γ))
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ) (twistedCentralizerBorel K L (v.adicCompletion K)
        σ δ))
    (hc : Coupled K L (v.adicCompletion K) σ γ δ 1 τ τ₁) (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hidx : (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e s)).relIndex
      (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ≠
          0) :
    (((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)) ⊔
            Subgroup.center (GL (Fin 2) (w.1.adicCompletion L))).relIndex
          (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e δ)) : ℂ) *
        ((τ₁ (((((TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v
            w e δ))).comap
            (glEquiv K L v w e :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf (twistedCentralizer
              K L (v.adicCompletion K) σ δ) :
            Subgroup (twistedCentralizer K L (v.adicCompletion K) σ δ)) : Set (twistedCentralizer K L (v.adicCompletion
                K) σ δ))).toReal : ℂ) =
      ((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℂ) *
        ((τ ((TorusIndices.unitCentralizer K v γ).subgroupOf (Subgroup.centralizer ({γ} : Set (GL (Fin 2)
            (v.adicCompletion K)))) :
            Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ) := by
  rw [twisted_relIndex_sup_center_eq K L σ v w hdeg hσ1 hw e γ hrs δ hN,
    twisted_measure_comap_twistedUnitCentralizer_eq K L σ v w hdeg hσ1 hw e γ hrs δ hN τ τ₁ hc s hidx]

end NormalisingConstants

section Comparison

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2 P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedValues AddMonoidAlgebra LT.TwistedNorm"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem exists_units_mul_zpow_of_ne_zero (F : Type) [Field F] [NumberField F]
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (ϖ : u.adicCompletionIntegers F) (hϖ : Irreducible ϖ)
    {d : u.adicCompletion F} (hd : d ≠ 0) :
    ∃ (D : ℤ) (w' : (u.adicCompletionIntegers F)ˣ),
      d = algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) w' *
        algebraMap (u.adicCompletionIntegers F) (u.adicCompletion F) ϖ ^ D := by
  have hint : ∀ x : u.adicCompletionIntegers F, x ≠ 0 → ∃ (n : ℕ) (w' : (u.adicCompletionIntegers F)ˣ),
      (x : u.adicCompletion F) =
        (ϖ : u.adicCompletion F) ^ n * ((w' : u.adicCompletionIntegers F) : u.adicCompletion F) := by
    intro x hx
    obtain ⟨n, u₀, hxu⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.eq_pow_uniformizer_mul_unit F u hx
      (InertTransport.valued_coe_eq_of_irreducible F u hϖ)
    refine ⟨n, u₀, ?_⟩
    rw [hxu]
    push_cast
    rfl
  rcases ValuationSubring.mem_or_inv_mem (u.adicCompletionIntegers F) d with h | h
  · obtain ⟨n, w', hn⟩ := hint ⟨d, h⟩ fun h0 => hd (Subtype.ext_iff.mp h0)
    have hn' : d = (ϖ : u.adicCompletion F) ^ n * ((w' : u.adicCompletionIntegers F) : u.adicCompletion F) := hn
    refine ⟨n, w', ?_⟩
    rw [ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply, zpow_natCast, mul_comm]
    exact hn'
  · obtain ⟨n, w', hn⟩ := hint ⟨d⁻¹, h⟩ fun h0 => inv_ne_zero hd (Subtype.ext_iff.mp h0)
    have hn' : d⁻¹ = (ϖ : u.adicCompletion F) ^ n * ((w' : u.adicCompletionIntegers F) : u.adicCompletion F) := hn
    have hW : (((w'⁻¹ : (u.adicCompletionIntegers F)ˣ) : u.adicCompletionIntegers F) : u.adicCompletion F) =
        (((w' : u.adicCompletionIntegers F)) : u.adicCompletion F)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by exact_mod_cast w'.inv_mul)
    refine ⟨-(n : ℤ), w'⁻¹, ?_⟩
    rw [ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply, zpow_neg, zpow_natCast, hW,
      ← mul_inv_rev, ← hn', inv_inv]

private theorem glEquiv_toTensorGL (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (g : GL (Fin 2) (v.adicCompletion K)) :
    glEquiv K L v w e (toTensorGL K L (v.adicCompletion K) g) = (InertTransport.iota K L v w).mapGL g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [IntegralHom.mapGL_coe, Matrix.map_apply, glEquiv_apply, Matrix.GeneralLinearGroup.map_apply, toTensorGL,
    Matrix.GeneralLinearGroup.map_apply]
  show e ((Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)
      ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)) =
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
  rw [Algebra.TensorProduct.includeRight_apply, ← TensorProduct.RightActions.algebraMap_eval K (v.adicCompletion K) L,
    AlgEquiv.commutes]

private theorem sigmaNormPow_glEquiv_eq_mapGL (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (γ : GL (Fin 2) (v.adicCompletion K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L (v.adicCompletion K) σ γ δ 1) :
    LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) (glEquiv K L v w
        e δ) =
      (InertTransport.iota K L v w).mapGL γ := by
  have h : normString K L (v.adicCompletion K) σ δ = toTensorGL K L (v.adicCompletion K) γ := by
    rw [IsNormConjugator, inv_one, one_mul, mul_one] at hN
    exact hN.symm
  rw [← InertTransport.glEquiv_normString K L σ v w hdeg e, h, glEquiv_toTensorGL]

omit [NumberField L] in

private theorem isRegularSemisimple_toTensorGL {γ : GL (Fin 2) (v.adicCompletion K)} (hrs : IsRegularSemisimple γ) :
    IsRegularSemisimple (toTensorGL K L (v.adicCompletion K) γ) := by
  have hcoe : ((toTensorGL K L (v.adicCompletion K) γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map
        ⇑(Algebra.TensorProduct.includeRight :
          v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom :=
    Matrix.ext fun i j => Matrix.GeneralLinearGroup.map_apply _ i j γ
  have hmap : ∀ (f : v.adicCompletion K →+* L ⊗[K] v.adicCompletion K) (x : v.adicCompletion K),
      f (x ^ 2 - 4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
        f x ^ 2 - 4 * f (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := fun f x => by
    rw [map_sub, map_pow, map_mul, map_ofNat]
  unfold IsRegularSemisimple at hrs ⊢
  rw [hcoe, ← AddMonoidHom.map_trace, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hmap]
  exact hrs.map _

omit [NumberField L] in

private theorem isRegularSemisimple_normString_of_isNormConjugator_one (γ : GL (Fin 2) (v.adicCompletion K))
    (hrs : IsRegularSemisimple γ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L
        (v.adicCompletion K) σ γ δ 1) :
    IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) := by
  rw [IsNormConjugator, inv_one, one_mul, mul_one] at hN
  rw [← hN]
  exact isRegularSemisimple_toTensorGL K L v hrs

private theorem iota_toField_apply (x : v.adicCompletion K) :
    (InertTransport.iota K L v w).toField x = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x := rfl

private theorem sigmaNormPow_unitsMap_mem_range (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (n : ℕ)
    (uδ : (w.1.adicCompletionIntegers L)ˣ) :
    LT.TwistedNorm.sigmaNormPow (Units.map ((theta K L σ v w e).toRingHom : (w.1.adicCompletion L) →*
        (w.1.adicCompletion L))) n ((Units.map ((algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
        (w.1.adicCompletionIntegers L) →+* (w.1.adicCompletion L)) : (w.1.adicCompletionIntegers L) →*
        (w.1.adicCompletion L))) uδ) ∈ (Units.map ((algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
        (w.1.adicCompletionIntegers L) →+* (w.1.adicCompletion L)) : (w.1.adicCompletionIntegers L) →*
        (w.1.adicCompletion L))).range := by

  have hstab : ∀ x ∈ (Units.map ((algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
      (w.1.adicCompletionIntegers L) →+* (w.1.adicCompletion L)) : (w.1.adicCompletionIntegers L) →*
      (w.1.adicCompletion L))).range, (Units.map ((theta K L σ v w e).toRingHom : (w.1.adicCompletion L) →*
      (w.1.adicCompletion L))) x ∈ (Units.map ((algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
      (w.1.adicCompletionIntegers L) →+* (w.1.adicCompletion L)) : (w.1.adicCompletionIntegers L) →*
      (w.1.adicCompletion L))).range := by
    rintro x ⟨W, rfl⟩
    refine ⟨Units.map ((InertTransport.thetaAut K L σ v w hdeg e).toBase : (w.1.adicCompletionIntegers L) →*
        (w.1.adicCompletionIntegers L)) W, Units.ext ?_⟩
    rw [Units.coe_map, Units.coe_map, Units.coe_map, Units.coe_map, MonoidHom.coe_coe, MonoidHom.coe_coe,
      MonoidHom.coe_coe, ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply,
      InertTransport.thetaAut_toBase_coe]
    rfl
  have hiter : ∀ i : ℕ, ((Units.map ((theta K L σ v w e).toRingHom : (w.1.adicCompletion L) →* (w.1.adicCompletion
      L))))^[i] ((Units.map ((algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
      (w.1.adicCompletionIntegers L) →+* (w.1.adicCompletion L)) : (w.1.adicCompletionIntegers L) →*
      (w.1.adicCompletion L))) uδ) ∈ (Units.map ((algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
      (w.1.adicCompletionIntegers L) →+* (w.1.adicCompletion L)) : (w.1.adicCompletionIntegers L) →*
      (w.1.adicCompletion L))).range := by
    intro i
    induction i with
    | zero => exact ⟨uδ, rfl⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hstab _ ih
  rw [sigmaNormPow_def, sigmaPartialNorm_eq_prod_range]
  exact prod_mem fun i _ => hiter i

private theorem eq_finrank_mul_of_sigmaNormPow_eq (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (γ : GL (Fin 2) (v.adicCompletion K)) (D : ℤ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ D)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hnorm : LT.TwistedNorm.sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
        (glEquiv K L v w e δ) = (InertTransport.iota K L v w).mapGL γ)
    (kδ : ℤ) (uδ : (w.1.adicCompletionIntegers L)ˣ)
    (hdetδ : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
        (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) uδ *
        algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ kδ)
            :
    D = Module.finrank K L * kδ := by
  have hϖ' := InertTransport.irreducible_iota_toBase K L v w hw hϖ
  have hP0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ)
      ≠ 0 :=
    algebraMap_ne_zero_of_irreducible L w.1 hϖ'
  have hθP : theta K L σ v w e (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota
      K L v w).toBase ϖ)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) := by
    rw [ValuationSubring.algebraMap_apply, ← InertTransport.thetaAut_toBase_coe K L σ v w hdeg e,
      InertTransport.thetaAut_toBase_iota K L σ v w hdeg e ϖ]
  have hmap : (InertTransport.thetaAut K L σ v w hdeg e).mapGL = Matrix.GeneralLinearGroup.map (theta K L σ v w
      e).toRingHom :=
    MonoidHom.ext (thetaAut_mapGL_apply K L σ v w hdeg e)

  have hdetN := congrArg Matrix.GeneralLinearGroup.det hnorm
  rw [hmap, det_sigmaNormPow, Matrix.GeneralLinearGroup.map_det] at hdetN
  have hdd : Matrix.GeneralLinearGroup.det (glEquiv K L v w e δ) =
      Units.mk0 (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase
          ϖ)) hP0 ^ kδ * Units.map ((algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
          (w.1.adicCompletionIntegers L) →+* (w.1.adicCompletion L)) : (w.1.adicCompletionIntegers L) →*
          (w.1.adicCompletion L)) uδ :=
    Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hdetδ, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0,
        Units.coe_map, MonoidHom.coe_coe, mul_comm])
  have hfix : Units.map ((theta K L σ v w e).toRingHom : (w.1.adicCompletion L) →* (w.1.adicCompletion L)) (Units.mk0
      (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ)) hP0 ^
      kδ) =
      Units.mk0 (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase
          ϖ)) hP0 ^ kδ :=
    Units.ext (by
      rw [Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀]
      exact congrArg (· ^ kδ) hθP)

  obtain ⟨W, hW⟩ := sigmaNormPow_unitsMap_mem_range K L σ v w hdeg e (Module.finrank K L) uδ
  rw [hdd, FixedOrInversion.sigmaNormPow_mul_of_central _ (fun g => Commute.all _ g) hfix, ← hW] at hdetN

  have hval := congrArg (fun z : ((w.1.adicCompletion L))ˣ => (z : (w.1.adicCompletion L))) hdetN
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.coe_map,
    MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply, hdet, map_mul, map_zpow₀, iota_toField_apply,
    ValuationSubring.algebraMap_apply, InertTransport.iota_toBase_coe] at hval
  rw [← zpow_natCast, ← zpow_mul, mul_comm kδ] at hval
  refine zpow_exponent_unique L w.1 hϖ' (Units.map ((InertTransport.iota K L v w).toBase : (v.adicCompletionIntegers K)
      →* (w.1.adicCompletionIntegers L)) u) W D
    (Module.finrank K L * kδ) ?_
  rw [Units.coe_map, MonoidHom.coe_coe, ValuationSubring.algebraMap_apply, ValuationSubring.algebraMap_apply,
    ValuationSubring.algebraMap_apply, InertTransport.iota_toBase_coe, InertTransport.iota_toBase_coe]
  linear_combination hval.symm

private theorem shadow_congr_of_not_even {R₀ : Type*} [CommRing R₀] (D : ℤ) (C C' : R₀) (F : AddMonoidAlgebra R₀ (ℤ × ℤ))
    (hD : ¬ Even D) : shadow D C F = shadow D C' F := by
  unfold shadow
  rw [if_neg hD, if_neg hD]

private theorem twistedOrbitalIntegral_eq_orbitalIntegral_of_isNormConjugator_one (hdeg : (Module.finrank K L).Prime)
    (hσ1 : σ ≠ 1) (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (hrs : IsRegularSemisimple
        γ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L (v.adicCompletion K) σ γ δ 1)
    (SK : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hSKT : SK (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) =
      (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) • single ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSKc : SK (heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) = single ((1 : ℤ), (1 : ℤ)) 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (b : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
      HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (hcomp : SK.comp b = (mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁)
    (hc : Coupled K L (v.adicCompletion K) σ γ δ 1 τ τ₁)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I I' : ℂ}
    (hI' : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ₁
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I')
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      ((b f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) : GL (Fin 2)
          (v.adicCompletion K) → ℂ) I) :
    I' = I := by
  classical
  have hdet0 : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det γ).ne_zero
  obtain ⟨D, u, hdet⟩ := exists_units_mul_zpow_of_ne_zero K v ϖ hϖ hdet0
  have hϖ' := InertTransport.irreducible_iota_toBase K L v w hw hϖ
  have hdetδ0 : Matrix.det ((glEquiv K L v w e δ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
      (w.1.adicCompletion L)) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det (glEquiv K L v w e δ)).ne_zero
  obtain ⟨kδ, uδ, hdetδ⟩ := exists_units_mul_zpow_of_ne_zero L w.1 ((InertTransport.iota K L v w).toBase ϖ) hϖ' hdetδ0
  have hnorm := sigmaNormPow_glEquiv_eq_mapGL K L σ v w hdeg e γ δ hN
  have hD := eq_finrank_mul_of_sigmaNormPow_eq K L σ v w hdeg e hw ϖ hϖ γ D u hdet δ hnorm kδ uδ hdetδ
  have hδ := isRegularSemisimple_normString_of_isNormConjugator_one K L σ v γ hrs δ hN
  have hidx : ∀ s : GL (Fin 2) (w.1.adicCompletion L),
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
            s).relIndex
          (TwistedTorusIndices.twistedUnitCentralizer (InertTransport.thetaAut K L σ v w hdeg e)
            (glEquiv K L v w e δ)) ≠ 0 := by
    intro s
    by_cases hk : Even kδ
    · exact twisted_relIndex_ne_zero_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ
        hdetδ hD hk s
    · exact twisted_relIndex_ne_zero_of_not_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ
        uδ hdetδ hD hk s
  have hκ := (twisted_kappa_eq K L σ v w hdeg hσ1 hw e γ hrs δ hN τ τ₁ hc 1 (hidx _)).symm
  have h1 := orbitalIntegral_eq_shadow K v ϖ hϖ γ hγ hrs u D hdet SK hSKT hSKc τ hτ (b f) hI
  have h2 := twistedOrbitalIntegral_eq_shadow K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD
    hδ hσn SL hST hSc τ₁ hτ₁ f hI'
  have hSb : SK (b f) = mapDomain (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ)) (SL f) := by
    have hc := AlgHom.congr_fun hcomp f
    rw [AlgHom.comp_apply, AlgHom.comp_apply, mapDomainAlgHom_apply] at hc
    exact hc
  rw [h1, h2, hSb, hD, shadow_mapDomain _ hdeg.pos, hκ]
  congr 1
  by_cases hk : Even kδ
  · rw [twistedUnitOrbitalCount_eq_of_even K L σ v w hdeg hσ1 e hw ϖ hϖ hres γ hγ D u hdet δ hnorm kδ uδ hdetδ hD hk]
  · exact shadow_congr_of_not_even kδ _ _ _ hk

end Comparison

section IntegralitySeam

open scoped TensorProduct TensorProduct.RightActions
open AutomorphicForm LocalGL2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem toTensorGL_mem_semiLocalIntegralSet_iff
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (t : GL (Fin 2) (v.adicCompletion K)) :
    toTensorGL K L (v.adicCompletion K) t ∈ semiLocalIntegralSet K L v ↔ t ∈ localIntegralSet K v := by
  have hc : ∀ c : v.adicCompletion K,
      (InertTransport.iota K L v w).toField c ∈ ((w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))) ↔
        c ∈ ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := by
    intro c
    rw [SetLike.mem_coe, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.mem_adicCompletionIntegers, iota_toField_apply]
    change Valued.v (w.adicCompletionSemialgHom K L c) ≤ 1 ↔ _
    rw [w.valued_adicCompletionSemialgHom K L, hw, pow_one]
  rw [mem_semiLocalIntegralSet_iff_glEquiv_mem K L v w e, glEquiv_toTensorGL, ← SetLike.mem_coe,
    ← integralUnitsSet_eq_integralSubgroup (w.1.adicCompletion L) (w.1.adicCompletionIntegers L)]
  show Matrix.GeneralLinearGroup.map (InertTransport.iota K L v w).toField t ∈ _ ↔ _
  rw [map_mem_integralUnitsSet_iff, localIntegralSet, mem_integralUnitsSet]
  exact Iff.and (forall₂_congr fun a b => hc _) (forall₂_congr fun a b => hc _)

end IntegralitySeam

section NonNorms

open NumberField IsDedekindDomain HeckePair LocalGL2 AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2 P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedValues AddMonoidAlgebra LT.TwistedNorm"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem nonNorm_shadow_mapDomain_eq_zero_of_not_dvd {R₀ : Type*} [CommRing R₀] (n : ℕ) (hn : 0 < n) (D : ℤ)
    (hD : ¬ ((n : ℤ) ∣ D)) (C : R₀) (F : AddMonoidAlgebra R₀ (ℤ × ℤ)) :
    InertBaseChange.shadow D C (AddMonoidAlgebra.mapDomain (n • AddMonoidHom.id (ℤ × ℤ)) F) = 0 := by
  have hid : ∀ a : ℤ × ℤ, (n • AddMonoidHom.id (ℤ × ℤ)) a = ((n : ℤ) * a.1, (n : ℤ) * a.2) := fun a => by
    simp [Prod.ext_iff]
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hinj : Function.Injective (n • AddMonoidHom.id (ℤ × ℤ)) := by
    intro a b hab
    rw [hid, hid, Prod.mk.injEq] at hab
    exact Prod.ext (mul_left_cancel₀ hn0 hab.1) (mul_left_cancel₀ hn0 hab.2)
  have hA : (if Even D then C * Finsupp.mapDomain (n • AddMonoidHom.id (ℤ × ℤ)) F.coeff (D / 2, D / 2) else 0) =
      0 := by
    split_ifs with hE
    · rw [Finsupp.mapDomain_notin_range, mul_zero]
      rintro ⟨⟨a, _⟩, hab⟩
      rw [hid, Prod.mk.injEq] at hab
      obtain ⟨j, hj⟩ := hE
      have hj2 : D / 2 = j := by rw [hj, ← two_mul, Int.mul_ediv_cancel_left _ two_ne_zero]
      have ha : (n : ℤ) * a = j := by rw [← hj2]; exact hab.1
      exact hD ⟨a + a, by rw [mul_add, ha, hj]⟩
    · rfl
  have hS : ((Finsupp.mapDomain (n • AddMonoidHom.id (ℤ × ℤ)) F.coeff).sum fun (x : ℤ × ℤ) (r : R₀) =>
      if x.1 < x.2 ∧ x.1 + x.2 = D then r else 0) = 0 := by
    rw [Finsupp.sum_mapDomain_index_inj hinj]
    refine Eq.trans ?_ (Finsupp.sum_fun_zero F.coeff)
    apply Finsupp.sum_congr
    intro x _
    simp only [hid]
    refine if_neg ?_
    rintro ⟨-, hsum⟩
    have hsum' : (n : ℤ) * x.1 + (n : ℤ) * x.2 = D := hsum
    exact hD ⟨x.1 + x.2, by rw [mul_add, hsum']⟩
  simp only [InertBaseChange.shadow, AddMonoidAlgebra.coeff_mapDomain]
  rw [hA, hS, mul_zero, add_zero]

private theorem nonNorm_eq_zero_of_not_isNormOf (hdeg : (Module.finrank K L).Prime)
    (hσ1 : σ ≠ 1) (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) (hrs : IsRegularSemisimple
        γ)
    (SK : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hSKT : SK (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) =
      (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) • single ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSKc : SK (heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) = single ((1 : ℤ), (1 : ℤ)) 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (b : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
      HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (hcomp : SK.comp b = (mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (hnn : ¬ ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I : ℂ}
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      ((b f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) : GL (Fin 2)
          (v.adicCompletion K) → ℂ) I) :
    I = 0 := by
  have _ := hσn
  have _ := hres
  have _ := hST
  have _ := hSc
  have hdet0 : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det γ).ne_zero
  obtain ⟨D, u, hdet⟩ := exists_units_mul_zpow_of_ne_zero K v ϖ hϖ hdet0
  have hval : Valued.v (Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      ((Multiplicative.ofAdd (-D) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [hdet, map_mul, map_zpow₀]
    change Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
      Valued.v ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ D = _
    rw [InertTransport.valued_coe_unit, one_mul, InertTransport.valued_coe_eq_of_irreducible K v hϖ,
      ← WithZero.coe_zpow, ← ofAdd_zsmul, smul_neg, zsmul_one, Int.cast_id]
  have hv' : ∀ w' : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w' = v →
        Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1 := by
    intro w' hw'
    rw [eq_of_under_eq K L v w e w' w.1 hw' w.2]
    exact hw
  have hndvd : ¬ ((Module.finrank K L : ℤ) ∣ D) := by
    rintro ⟨k, hk⟩
    refine hnn
      (AutomorphicForm.exists_isNormOf_of_not_isSquare_discr_of_finrank_dvd_of_ramificationIdx_eq_one K L hdeg σ hσ1 v
        hv' γ ((QuadraticIrreducibility.irreducible_charpoly_iff K v γ).1 hγ) ⟨-k, ?_⟩)
    rw [hval, hk, mul_neg]
  have h1 := orbitalIntegral_eq_shadow K v ϖ hϖ γ hγ hrs u D hdet SK hSKT hSKc τ hτ (b f) hI
  have hSb : SK (b f) = AddMonoidAlgebra.mapDomain (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ)) (SL f) := by
    have hc := AlgHom.congr_fun hcomp f
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at hc
    exact hc
  rw [h1, hSb, nonNorm_shadow_mapDomain_eq_zero_of_not_dvd (Module.finrank K L) hdeg.pos D hndvd, mul_zero]

end NonNorms

section SplitClasses

open scoped TensorProduct TensorProduct.RightActions Pointwise
p2m_open "NumberField IsDedekindDomain HeckePair AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2 P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedValues AddMonoidAlgebra LT.TwistedNorm"

open InertTransport (theta theta_apply glEquiv glEquiv_apply glEquiv_sigmaGL)

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem split_exists_conj_eq_diagonal {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (γ : GL (Fin 2) F)
    (hsq : IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) F)))
    (hrs : IsRegularSemisimple γ) :
    ∃ (g : GL (Fin 2) F) (α β : Fˣ), α ≠ β ∧
      ((g⁻¹ * γ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(α : F), 0; 0, (β : F)] := by

  have key : ∀ (G : Matrix (Fin 2) (Fin 2) F) (α β : F), G.det ≠ 0 → α ≠ 0 → β ≠ 0 → α ≠ β →
      (γ : Matrix (Fin 2) (Fin 2) F) * G = G * !![α, 0; 0, β] →
      ∃ (g : GL (Fin 2) F) (α β : Fˣ), α ≠ β ∧
        ((g⁻¹ * γ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(α : F), 0; 0, (β : F)] := by
    intro G α β hG hα hβ hαβ hγG
    obtain ⟨g, hgv⟩ : ∃ g : GL (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) = G :=
      ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, rfl⟩
    refine ⟨g, Units.mk0 α hα, Units.mk0 β hβ, fun h => hαβ (congrArg Units.val h), ?_⟩
    rw [Units.val_mul, Units.val_mul, Units.val_mk0, Units.val_mk0, mul_assoc, hgv, hγG, ← mul_assoc, ← hgv,
      Units.inv_mul, one_mul]
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (γ : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨r, hr⟩ := hsq
  rw [isRegularSemisimple_iff_ne_zero] at hrs
  rw [hM, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at hr hrs
  have hr0 : r ≠ 0 := fun h => hrs (by rw [hr, h, mul_zero])
  have hdet : a * d - b * c ≠ 0 := by
    rw [← Matrix.det_fin_two_of, ← hM, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det γ).ne_zero
  have h4 : (4 : F) ≠ 0 := by
    have h22 : (4 : F) = 2 * 2 := by norm_num
    rw [h22]
    exact mul_ne_zero h2 h2
  by_cases hb : b = 0
  ·
    have had : a ≠ d := by
      intro h
      apply hrs
      rw [h, hb]
      ring
    have ha : a ≠ 0 := fun h => hdet (by rw [h, hb]; ring)
    have hd : d ≠ 0 := fun h => hdet (by rw [h, hb]; ring)
    refine key !![a - d, 0; c, 1] a d ?_ ha hd had ?_
    · rw [Matrix.det_fin_two_of]
      intro h
      apply had
      linear_combination h
    · rw [hM, hb]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  ·
    obtain ⟨α, hα2⟩ : ∃ α : F, 2 * α = a + d + r := ⟨(a + d + r) / 2, mul_div_cancel₀ _ h2⟩
    obtain ⟨β, hβ2⟩ : ∃ β : F, 2 * β = a + d - r := ⟨(a + d - r) / 2, mul_div_cancel₀ _ h2⟩
    have hαβ : α ≠ β := by
      intro h
      apply hr0
      have h2r : 2 * r = 0 := by linear_combination (-1 : F) * hα2 + hβ2 + 2 * h
      exact (mul_eq_zero.mp h2r).resolve_left h2
    have hroot : ∀ x : F, 2 * x = a + d + r ∨ 2 * x = a + d - r → x ^ 2 - (a + d) * x + (a * d - b * c) = 0 := by
      intro x hx
      have h4x : 4 * (x ^ 2 - (a + d) * x + (a * d - b * c)) = 0 := by
        rcases hx with hx | hx
        · linear_combination (2 * x - (a + d) + r) * hx - hr
        · linear_combination (2 * x - (a + d) - r) * hx - hr
      exact (mul_eq_zero.mp h4x).resolve_left h4
    have hprod : α * β = a * d - b * c := by
      have h4p : 4 * (α * β) = 4 * (a * d - b * c) := by
        linear_combination (2 * β) * hα2 + (a + d + r) * hβ2 + hr
      exact mul_left_cancel₀ h4 h4p
    have hα0 : α ≠ 0 := fun h => hdet (by rw [← hprod, h, zero_mul])
    have hβ0 : β ≠ 0 := fun h => hdet (by rw [← hprod, h, mul_zero])
    refine key !![b, b; α - a, β - a] α β ?_ hα0 hβ0 hαβ ?_
    · rw [Matrix.det_fin_two_of]
      have hfac : b * (β - a) - b * (α - a) = b * (β - α) := by ring
      rw [hfac]
      exact mul_ne_zero hb (sub_ne_zero.mpr hαβ.symm)
    · rw [hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · ring
      · ring
      · linear_combination (-1 : F) * hroot α (Or.inl hα2)
      · linear_combination (-1 : F) * hroot β (Or.inr hβ2)

private theorem split_exists_valuation_one_sub_div_eq (α β : (v.adicCompletion K)ˣ) (hαβ : α ≠ β) :
    ∃ m : ℤ, Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hx : (1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K) ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq α.ne_zero]
    exact fun h => hαβ (Units.val_injective h).symm
  have hv0 : (Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) :
      WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hv0
  exact ⟨-Multiplicative.toAdd u, by rw [neg_neg, ofAdd_toAdd, hu]⟩

private theorem split_exists_rep_diag_mul {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    (d₁ d₂ : Rˣ) {x y : F} {c : GL (Fin 2) F ⧸ integralSubgroup R F}
    (h : ∃ g : GL (Fin 2) F, QuotientGroup.mk g = c ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 = x ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = y) :
    ∃ g : GL (Fin 2) F, QuotientGroup.mk g = c ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 = x * algebraMap R F d₁ ∧
      (g : Matrix (Fin 2) (Fin 2) F) 1 1 = y * algebraMap R F d₂ := by
  obtain ⟨g, hgc, h10, h00, h11⟩ := h
  obtain ⟨dR, hdR⟩ : ∃ dR : GL (Fin 2) R, (dR : Matrix (Fin 2) (Fin 2) R) = !![(d₁ : R), 0; 0, (d₂ : R)] :=
    ⟨⟨!![(d₁ : R), 0; 0, (d₂ : R)], !![((d₁⁻¹ : Rˣ) : R), 0; 0, ((d₂⁻¹ : Rˣ) : R)], by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩, rfl⟩
  refine ⟨g * Matrix.GeneralLinearGroup.map (algebraMap R F) dR, ?_, ?_, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul_of_mem g (mem_integralSubgroup_iff.mpr ⟨dR, rfl⟩), hgc]
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
      Matrix.GeneralLinearGroup.map_apply, hdR, h10]
    simp
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
      Matrix.GeneralLinearGroup.map_apply, hdR, h00]
    simp
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply,
      Matrix.GeneralLinearGroup.map_apply, hdR, h10, h11]
    simp

private theorem split_setOf_exists_rep_diag_mul {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    (d₁ d₂ : Rˣ) (x y : F) :
    {c : GL (Fin 2) F ⧸ integralSubgroup R F |
        ∃ g : GL (Fin 2) F, QuotientGroup.mk g = c ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
          (g : Matrix (Fin 2) (Fin 2) F) 0 0 = x * algebraMap R F d₁ ∧
          (g : Matrix (Fin 2) (Fin 2) F) 1 1 = y * algebraMap R F d₂} =
      {c : GL (Fin 2) F ⧸ integralSubgroup R F |
        ∃ g : GL (Fin 2) F, QuotientGroup.mk g = c ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
          (g : Matrix (Fin 2) (Fin 2) F) 0 0 = x ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = y} := by
  ext c
  refine ⟨fun h => ?_, fun h => split_exists_rep_diag_mul d₁ d₂ h⟩
  simpa only [Set.mem_setOf_eq, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] using
    split_exists_rep_diag_mul d₁⁻¹ d₂⁻¹ h

private theorem split_coe_prod_map_pow_of_coe_eq_diagonal {F R : Type*} [CommSemiring F] [CommRing R] [Algebra F R]
    (θ : R ≃ₐ[F] R) (x : GL (Fin 2) R) (a b : R) (hx : (x : Matrix (Fin 2) (Fin 2) R) = !![a, 0; 0, b]) (N : ℕ) :
    ((((List.range N).map fun i => Matrix.GeneralLinearGroup.map (θ ^ i).toAlgHom.toRingHom x).prod :
        GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![∏ i ∈ Finset.range N, (θ ^ i).toAlgHom.toRingHom a, 0;
        0, ∏ i ∈ Finset.range N, (θ ^ i).toAlgHom.toRingHom b] := by
  induction N with
  | zero =>
    rw [List.range_zero, List.map_nil, List.prod_nil, Finset.prod_range_zero, Finset.prod_range_zero, Units.val_one]
    exact Matrix.one_fin_two
  | succ N ih =>
    have hN : ((Matrix.GeneralLinearGroup.map (θ ^ N).toAlgHom.toRingHom x : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R) = !![(θ ^ N).toAlgHom.toRingHom a, 0; 0, (θ ^ N).toAlgHom.toRingHom b] := by
      ext i j
      rw [Matrix.GeneralLinearGroup.map_apply, hx]
      fin_cases i <;> fin_cases j <;> simp
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_singleton,
      Units.val_mul, ih, hN, Finset.prod_range_succ, Finset.prod_range_succ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem split_conj_mem_centralizer {G : Type*} [Group G] {γ : G} (g : G) {t : G}
    (ht : t ∈ Subgroup.centralizer ({γ} : Set G)) :
    g⁻¹ * t * g ∈ Subgroup.centralizer ({g⁻¹ * γ * g} : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at ht ⊢
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hγt : γ * t = t * γ := ht γ (Set.mem_singleton γ)
  calc g⁻¹ * γ * g * (g⁻¹ * t * g) = g⁻¹ * (γ * t) * g := by group
    _ = g⁻¹ * (t * γ) * g := by rw [hγt]
    _ = g⁻¹ * t * g * (g⁻¹ * γ * g) := by group

omit [NumberField L] in

private theorem split_coe_toTensorGL (t : GL (Fin 2) (v.adicCompletion K)) :
    (toTensorGL K L (v.adicCompletion K) t : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map
        (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) := by
  ext i j
  rfl

private theorem split_continuous_toTensorGL : Continuous (toTensorGL K L (v.adicCompletion K)) := by
  have hf : Continuous (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) :=
    continuous_algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ toTensorGL K L (v.adicCompletion K)) = fun g : GL (Fin 2) (v.adicCompletion K) =>
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map
          (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) :=
      funext fun g => split_coe_toTensorGL K L v g
    rw [h]
    exact Units.continuous_val.matrix_map hf
  · have h : (fun g : GL (Fin 2) (v.adicCompletion K) =>
        (((toTensorGL K L (v.adicCompletion K) g)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = fun g : GL (Fin 2) (v.adicCompletion K) =>
        ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).map
          (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) := by
      funext g
      rw [← map_inv, split_coe_toTensorGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map hf

private theorem split_measure_conj_eq_of_coupled
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (γ : GL (Fin 2) (v.adicCompletion K)) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hc : Coupled K L (v.adicCompletion K) σ γ δ 1 τ τ₁) (g : GL (Fin 2) (v.adicCompletion K)) :
    τ₁ {t | (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
          toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v} =
      τ {t | g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈ localIntegralSet K v} := by
  unfold Coupled at hc
  simp only [inv_one, one_mul, mul_one] at hc
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  letI := centralizerBorel (v.adicCompletion K) γ
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI hTG := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := hTG.toContinuousMul
  have hcont : Continuous fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (toTensorGL K L (v.adicCompletion K) g)⁻¹ * x * toTensorGL K L (v.adicCompletion K) g :=
    (continuous_const.mul continuous_id).mul continuous_const
  have h1 : Measurable fun t : twistedCentralizer K L (v.adicCompletion K) σ δ =>
      (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    continuous_subtype_val.measurable
  have h2 : Measurable fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) =>
      toTensorGL K L (v.adicCompletion K) (t : GL (Fin 2) (v.adicCompletion K)) :=
    ((split_continuous_toTensorGL K L v).comp continuous_subtype_val).measurable
  have hB : MeasurableSet {x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
      (toTensorGL K L (v.adicCompletion K) g)⁻¹ * x * toTensorGL K L (v.adicCompletion K) g ∈
        semiLocalIntegralSet K L v} :=
    ((isOpen_semiLocalIntegralSet K L v).preimage hcont).measurableSet
  have h := congrArg (fun μ : Measure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =>
    μ {x | (toTensorGL K L (v.adicCompletion K) g)⁻¹ * x * toTensorGL K L (v.adicCompletion K) g ∈
      semiLocalIntegralSet K L v}) hc
  beta_reduce at h
  rw [Measure.map_apply h1 hB, Measure.map_apply h2 hB] at h
  have h' : τ₁ {t | (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
      toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v} =
      τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
        (toTensorGL K L (v.adicCompletion K) g)⁻¹ *
            toTensorGL K L (v.adicCompletion K) (t : GL (Fin 2) (v.adicCompletion K)) *
          toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v} := h
  rw [h']
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  rw [← map_inv, ← map_mul, ← map_mul, toTensorGL_mem_semiLocalIntegralSet_iff K L v w hw e]

private theorem split_measureReal_conj_ne_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (g : GL (Fin 2) (v.adicCompletion K)) :
    (τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
        g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈ localIntegralSet K v}).toReal ≠ 0 := by
  letI := centralizerBorel (v.adicCompletion K) γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI := hτ
  refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
  · exact (IsOpen.measure_pos τ ((isOpen_localIntegralSet K v).preimage (by fun_prop))
      ⟨1, by simp [OneMemClass.coe_one, one_mem_localIntegralSet]⟩).ne'
  · rw [setOf_mem_localIntegralSet_eq, Subgroup.coe_subgroupOf, Subgroup.coe_subtype]
    exact ((TorusIndices.isClosed_centralizer K v γ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (TorusIndices.isCompact_conjStabilizer K v γ g)).measure_lt_top.ne

private theorem split_mass_mul_eq (ϖ : v.adicCompletionIntegers K)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    (γ : GL (Fin 2) (v.adicCompletion K))
    (SK : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hSK : ∀ (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (a b : ℤ),
      (SK f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
          integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c)
    (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ) {I : ℂ}
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I)
    (g : GL (Fin 2) (v.adicCompletion K)) (α β : (v.adicCompletion K)ˣ)
    (hg : ((g⁻¹ * γ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (kα kβ : ℤ) (uα uβ : (v.adicCompletionIntegers K)ˣ)
    (hα : (α : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uα *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kα)
    (hβ : (β : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uβ *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kβ) :
    ((τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
          g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈ localIntegralSet K v}).toReal : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) * I = (SK f).coeff (kα, kβ) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := glBorelOf (v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := ⟨rfl⟩
  letI := centralizerBorel (v.adicCompletion K) γ
  letI := centralizerBorel (v.adicCompletion K) (g⁻¹ * γ * g)
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({g⁻¹ * γ * g} : Set (GL (Fin 2) (v.adicCompletion K)))) := ⟨rfl⟩
  haveI := hτ
  haveI := isHaarMeasure_localHaar K v

  let ε : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ≃*
      Subgroup.centralizer ({g⁻¹ * γ * g} : Set (GL (Fin 2) (v.adicCompletion K))) :=
    { toFun := fun t => ⟨g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g, split_conj_mem_centralizer g t.2⟩
      invFun := fun t => ⟨g * (t : GL (Fin 2) (v.adicCompletion K)) * g⁻¹, by
        have h := split_conj_mem_centralizer g⁻¹ t.2
        rwa [inv_inv, show g * (g⁻¹ * γ * g) * g⁻¹ = γ by group] at h⟩
      left_inv := fun t => Subtype.ext (by
        show g * (g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g) * g⁻¹ = t
        group)
      right_inv := fun t => Subtype.ext (by
        show g⁻¹ * (g * (t : GL (Fin 2) (v.adicCompletion K)) * g⁻¹) * g = t
        group)
      map_mul' := fun s t => Subtype.ext (by
        show g⁻¹ * ((s : GL (Fin 2) (v.adicCompletion K)) * t) * g =
          g⁻¹ * (s : GL (Fin 2) (v.adicCompletion K)) * g * (g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g)
        group) }
  have hε : Continuous ε := by
    show Continuous fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) =>
      (⟨g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g, split_conj_mem_centralizer g t.2⟩ :
        Subgroup.centralizer ({g⁻¹ * γ * g} : Set (GL (Fin 2) (v.adicCompletion K))))
    exact Continuous.subtype_mk (by fun_prop) _
  have hεs : Continuous ε.symm := by
    show Continuous fun t : Subgroup.centralizer ({g⁻¹ * γ * g} : Set (GL (Fin 2) (v.adicCompletion K))) =>
      (ε.symm t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
    refine Continuous.subtype_mk (f := fun t : Subgroup.centralizer
      ({g⁻¹ * γ * g} : Set (GL (Fin 2) (v.adicCompletion K))) => g * (t : GL (Fin 2) (v.adicCompletion K)) * g⁻¹)
      (by fun_prop) _
  have hemb : MeasurableEmbedding ε := (Homeomorph.mk ε.toEquiv hε hεs).measurableEmbedding
  haveI hτ₀ : (Measure.map ε τ).IsHaarMeasure := ε.isHaarMeasure_map τ hε hεs

  have hI₀ : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) (g⁻¹ * γ * g) (Measure.map ε τ)
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I := by
    obtain ⟨w₀, ⟨hw0, hwm, hwc, hsec⟩, hIw⟩ := hI
    refine ⟨fun x => w₀ (g * x), ⟨fun x => hw0 _, hwm.comp (measurable_const_mul g),
      hwc.comp_homeomorph (Homeomorph.mulLeft g), fun x hx => ?_⟩, ?_⟩
    · have hx' : (f : GL (Fin 2) (v.adicCompletion K) → ℂ) ((g * x)⁻¹ * γ * (g * x)) ≠ 0 := by
        rwa [mul_inv_rev, show x⁻¹ * g⁻¹ * γ * (g * x) = x⁻¹ * (g⁻¹ * γ * g) * x by group]
      rw [hemb.integral_map]
      show ∫ t, w₀ (g * (g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g * x)) ∂τ = 1
      have hsimp : ∀ t : GL (Fin 2) (v.adicCompletion K), g * (g⁻¹ * t * g * x) = t * (g * x) := fun t => by group
      simp_rw [hsimp]
      exact hsec (g * x) hx'
    · rw [hIw]
      have h := integral_mul_left_eq_self (μ := localHaar K v)
        (fun y => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (y⁻¹ * γ * y) * ((w₀ y : ℝ) : ℂ)) g
      simp only [mul_inv_rev] at h
      rw [← h]
      congr 1
      funext x
      simp only [mul_assoc]

  have hUo : IsOpen ((integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
      Set (GL (Fin 2) (v.adicCompletion K)))) := by
    rw [← localIntegralSet_eq K v]
    exact isOpen_localIntegralSet K v
  have hfin : τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
      g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈ localIntegralSet K v} ≠ ⊤ := by
    rw [setOf_mem_localIntegralSet_eq, Subgroup.coe_subgroupOf, Subgroup.coe_subtype]
    exact ((TorusIndices.isClosed_centralizer K v γ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (TorusIndices.isCompact_conjStabilizer K v γ g)).measure_lt_top.ne
  have hmτ : Measure.map ε τ (Subtype.val ⁻¹' (integralSubgroup (v.adicCompletionIntegers K)
      (v.adicCompletion K) : Set (GL (Fin 2) (v.adicCompletion K)))) =
      ENNReal.ofReal (τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
        g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈ localIntegralSet K v}).toReal := by
    rw [ENNReal.ofReal_toReal hfin,
      Measure.map_apply hε.measurable (hUo.preimage continuous_subtype_val).measurableSet]
    show τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
        g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈
          (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
            Set (GL (Fin 2) (v.adicCompletion K)))} = _
    rw [← localIntegralSet_eq K v]

  have h1 := isOrbitalIntegralOn_localHaar_mul_eq_finsum_indicator_of_heckeAlgebra_of_diagonal K v f α β m hm
    (g⁻¹ * γ * g) hg (Measure.map ε τ) hτ₀ _ hmτ I hI₀
  rw [h1, hSK f kα kβ]
  have hα' : (α : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kα *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uα := by
    rw [hα, mul_comm]
  have hβ' : (β : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kβ *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uβ := by
    rw [hβ, mul_comm]
  rw [hα', hβ', split_setOf_exists_rep_diag_mul]

private theorem split_thetaAut_mapGL (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (y : GL (Fin 2) (w.1.adicCompletion L)) :
    (InertTransport.thetaAut K L σ v w hdeg e).mapGL y =
      Matrix.GeneralLinearGroup.map (InertTransport.thetaAlg K L σ v w e).toAlgHom.toRingHom y := by
  have h := InertTransport.thetaAut_mapGL_iterate K L σ v w hdeg e 1 y
  rwa [Function.iterate_one, pow_one] at h

private theorem split_thetaAut_mapGL_eq (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :
    (InertTransport.thetaAut K L σ v w hdeg e).mapGL =
      Matrix.GeneralLinearGroup.map (InertTransport.thetaAlg K L σ v w e).toAlgHom.toRingHom :=
  MonoidHom.ext (split_thetaAut_mapGL K L σ v w hdeg e)

private theorem split_thetaAut_mapGL_iterate_finrank (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (y : GL (Fin 2) (w.1.adicCompletion L)) :
    (⇑(InertTransport.thetaAut K L σ v w hdeg e).mapGL)^[Module.finrank K L] y = y := by
  rw [InertTransport.thetaAut_mapGL_iterate, ← InertTransport.finrank_adicCompletion_eq K L v w hdeg e,
    InertTransport.pow_finrank_eq_one]
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private theorem split_mul_sigmaNormPow_of_mem (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' t : GL (Fin 2) (w.1.adicCompletion L))
    (ht : t ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL δ') :
    t * sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) δ' =
      sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) δ' * t := by
  have h1 := mem_sigmaCentralizer_iff_inv.1 ht
  have h2 := sigmaNormPow_sigmaConjElt (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
    (split_thetaAut_mapGL_iterate_finrank K L σ v w hdeg e t) δ'
  rw [h1] at h2
  conv_lhs => rw [h2]
  group

private theorem split_offDiag_eq_zero_of_commute (α β : (v.adicCompletion K)ˣ) (hαβ : α ≠ β)
    (t : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))
    (ht : t * !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)] =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)] * t) :
    t 0 1 = 0 ∧ t 1 0 = 0 := by
  have hne : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) -
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) ≠ 0 := by
    intro h
    apply hαβ
    exact (Units.ext ((algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective (sub_eq_zero.1 h))).symm
  have h01 : t 0 1 * algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) * t 0 1 := by
    have h := congrFun (congrFun ht 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have h10 : t 1 0 * algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) * t 1 0 := by
    have h := congrFun (congrFun ht 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  constructor
  · have h : t 0 1 * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) -
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K)) = 0 := by
      rw [mul_sub, h01]; ring
    exact (mul_eq_zero.1 h).resolve_right hne
  · have h : t 1 0 * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) -
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K)) = 0 := by
      rw [mul_sub, h10]; ring
    exact (mul_eq_zero.1 h).resolve_right hne

private theorem split_val_le_one_of_add_of_mul (r s : w.1.adicCompletion L) (hrs0 : r * s ≠ 0)
    (hadd : Valued.v (r + s) ≤ (1 : WithZero (Multiplicative ℤ)))
    (hmul : Valued.v (r * s) ≤ (1 : WithZero (Multiplicative ℤ)))
    (hinv : Valued.v (r * s)⁻¹ ≤ (1 : WithZero (Multiplicative ℤ))) :
    Valued.v r ≤ (1 : WithZero (Multiplicative ℤ)) ∧ Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) ∧
      Valued.v r⁻¹ ≤ (1 : WithZero (Multiplicative ℤ)) ∧ Valued.v s⁻¹ ≤ (1 : WithZero (Multiplicative ℤ)) := by
  have hne : Valued.v (r * s) ≠ (0 : WithZero (Multiplicative ℤ)) := (map_ne_zero _).2 hrs0
  have hone : Valued.v (r * s) = (1 : WithZero (Multiplicative ℤ)) := by
    refine le_antisymm hmul ?_
    rw [map_inv₀] at hinv
    have h := mul_le_mul_right hinv (Valued.v (r * s))
    rwa [mul_inv_cancel₀ hne, mul_one] at h
  rw [map_mul] at hone hne
  have hr0 : Valued.v r ≠ (0 : WithZero (Multiplicative ℤ)) := left_ne_zero_of_mul hne
  have hs0 : Valued.v s ≠ (0 : WithZero (Multiplicative ℤ)) := right_ne_zero_of_mul hne
  have key : ∀ x y : w.1.adicCompletion L, Valued.v x * Valued.v y = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (x + y) ≤ (1 : WithZero (Multiplicative ℤ)) → Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := by
    intro x y hxy hxy1
    by_contra hlt
    push Not at hlt
    have hy : Valued.v y < Valued.v x := by
      refine lt_of_lt_of_le ?_ hlt.le
      by_contra hy1
      push Not at hy1
      have h := mul_le_mul_right hy1 (Valued.v x)
      rw [mul_one, hxy] at h
      exact absurd h (not_le.2 hlt)
    rw [Valuation.map_add_eq_of_lt_left (v := Valued.v) hy] at hxy1
    exact absurd hxy1 (not_le.2 hlt)
  have hr : Valued.v r ≤ (1 : WithZero (Multiplicative ℤ)) := key r s hone hadd
  have hs : Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) :=
    key s r (by rw [mul_comm]; exact hone) (by rwa [add_comm])
  have hr1 : Valued.v r = (1 : WithZero (Multiplicative ℤ)) := by
    refine le_antisymm hr ?_
    have h := mul_le_mul_right hs (Valued.v r)
    rwa [mul_one, hone] at h
  have hs1 : Valued.v s = (1 : WithZero (Multiplicative ℤ)) := by
    rw [hr1, one_mul] at hone
    exact hone
  refine ⟨hr, hs, ?_, ?_⟩
  · rw [map_inv₀, hr1, inv_one]
  · rw [map_inv₀, hs1, inv_one]

private theorem split_mem_range_algebraMap_iff (x : w.1.adicCompletion L) :
    x ∈ Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ↔
      Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem split_val_trace_le_one_of_mem (u : GL (Fin 2) (w.1.adicCompletion L))
    (hu : u ∈ integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)))) :
    Valued.v (Matrix.trace (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))) ≤ (1 : WithZero (Multiplicative ℤ)) ∧
      Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))) ≤ (1 : WithZero (Multiplicative ℤ)) ∧
      Valued.v (Matrix.det (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))⁻¹ ≤
        (1 : WithZero (Multiplicative ℤ)) := by
  rw [mem_integralUnitsSet] at hu
  obtain ⟨h₁, h₂⟩ := hu
  have e₁ : ∀ i j, Valued.v ((u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j) ≤
      (1 : WithZero (Multiplicative ℤ)) := fun i j => (split_mem_range_algebraMap_iff K L v w _).1 (h₁ i j)
  have e₂ : ∀ i j, Valued.v (((u⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2)
      (w.1.adicCompletion L)) i j) ≤ (1 : WithZero (Multiplicative ℤ)) :=
    fun i j => (split_mem_range_algebraMap_iff K L v w _).1 (h₂ i j)
  have hdet2 : ∀ A : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L),
      (∀ i j, Valued.v (A i j) ≤ (1 : WithZero (Multiplicative ℤ))) →
        Valued.v A.det ≤ (1 : WithZero (Multiplicative ℤ)) := by
    intro A hA
    rw [Matrix.det_fin_two]
    refine (Valuation.map_sub Valued.v _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; exact mul_le_one' (hA 0 0) (hA 1 1)
    · rw [map_mul]; exact mul_le_one' (hA 0 1) (hA 1 0)
  refine ⟨?_, hdet2 _ e₁, ?_⟩
  · rw [Matrix.trace_fin_two]
    exact (Valuation.map_add Valued.v _ _).trans (max_le (e₁ 0 0) (e₁ 1 1))
  · have hprod : Matrix.det (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) *
        Matrix.det ((u⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
          1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [← eq_inv_of_mul_eq_one_right hprod]
    exact hdet2 _ e₂

private theorem split_mem_integralUnitsSet_of_entries (g : GL (Fin 2) (w.1.adicCompletion L))
    (hent : ∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j) ≤
      (1 : WithZero (Multiplicative ℤ)))
    (hdet : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))⁻¹ ≤
      (1 : WithZero (Multiplicative ℤ))) :
    g ∈ integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) := by
  have hadj : ∀ i j, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)).adjugate i j) ≤
      (1 : WithZero (Multiplicative ℤ)) := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [hent]
  rw [mem_integralUnitsSet]
  refine ⟨fun i j => (split_mem_range_algebraMap_iff K L v w _).2 (hent i j), fun i j => ?_⟩
  rw [split_mem_range_algebraMap_iff, Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    smul_eq_mul, map_mul]
  exact mul_le_one' hdet (hadj i j)

private theorem split_twistedConjStabilizer_le (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' : GL (Fin 2) (w.1.adicCompletion L)) (α β : (v.adicCompletion K)ˣ) (hαβ : α ≠ β)
    (y₀ : GL (Fin 2) (w.1.adicCompletion L))
    (hy₀ : ((y₀⁻¹ * sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) δ' * y₀ :
        GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)])
    (s' : GL (Fin 2) (w.1.adicCompletion L)) :
    TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' s' ≤
      TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' y₀ := by
  intro t ht
  rw [TwistedTorusIndices.mem_twistedConjStabilizer_iff] at ht ⊢
  obtain ⟨htc, hts⟩ := ht
  refine ⟨htc, ?_⟩
  have hcomm := split_mul_sigmaNormPow_of_mem K L σ v w hdeg e δ' t htc
  generalize hN : sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) δ' = N
    at hy₀ hcomm
  have hconj : (y₀⁻¹ * t * y₀) * (y₀⁻¹ * N * y₀) = (y₀⁻¹ * N * y₀) * (y₀⁻¹ * t * y₀) := by
    calc (y₀⁻¹ * t * y₀) * (y₀⁻¹ * N * y₀) = y₀⁻¹ * (t * N) * y₀ := by group
      _ = y₀⁻¹ * (N * t) * y₀ := by rw [hcomm]
      _ = (y₀⁻¹ * N * y₀) * (y₀⁻¹ * t * y₀) := by group
  have hcm : ((y₀⁻¹ * t * y₀ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) *
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)] =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)] *
        ((y₀⁻¹ * t * y₀ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) := by
    rw [← hy₀, ← Units.val_mul, ← Units.val_mul, hconj]
  obtain ⟨h01, h10⟩ := split_offDiag_eq_zero_of_commute K L v w α β hαβ _ hcm

  have hmat : ((y₀⁻¹ * t * y₀ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      ((y₀⁻¹ * s' : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) *
        ((s'⁻¹ * t * s' : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) *
        (((y₀⁻¹ * s')⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  obtain ⟨htr, hdt, hdi⟩ := split_val_trace_le_one_of_mem K L v w _ hts
  have htrace : Matrix.trace ((y₀⁻¹ * t * y₀ : GL (Fin 2) (w.1.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      Matrix.trace ((s'⁻¹ * t * s' : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) := by
    rw [hmat, Matrix.trace_units_conj]
  have hdet : Matrix.det ((y₀⁻¹ * t * y₀ : GL (Fin 2) (w.1.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      Matrix.det ((s'⁻¹ * t * s' : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) := by
    rw [hmat, Matrix.det_units_conj]
  generalize hM : ((y₀⁻¹ * t * y₀ : GL (Fin 2) (w.1.adicCompletion L)) :
    Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) = M at h01 h10 htrace hdet
  have hdet' : M.det = M 0 0 * M 1 1 := by rw [Matrix.det_fin_two, h01, zero_mul, sub_zero]
  have hdet0 : M.det ≠ 0 := by
    have hprod : M.det * Matrix.det (((y₀⁻¹ * t * y₀)⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) = 1 := by
      rw [← hM, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one hprod
  obtain ⟨hr, hs, -, -⟩ := split_val_le_one_of_add_of_mul K L v w (M 0 0) (M 1 1) (hdet' ▸ hdet0)
    (by rw [← Matrix.trace_fin_two, htrace]; exact htr) (by rw [← hdet', hdet]; exact hdt)
    (by rw [← hdet', hdet]; exact hdi)
  refine split_mem_integralUnitsSet_of_entries K L v w _ ?_ ?_
  · rw [hM]
    intro i j
    fin_cases i <;> fin_cases j
    · exact hr
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, h01, map_zero]; exact zero_le'
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, h10, map_zero]; exact zero_le'
    · exact hs
  · rw [hM, hdet]
    exact hdi

private theorem split_mem_integralUnitsSet_iff (y : GL (Fin 2) (w.1.adicCompletion L)) :
    y ∈ integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) ↔
      y ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :=
  TwistedTorusIndices.mem_integralUnitsSet_range_iff y

private theorem split_mem_sigmaCentralizer_twistedConj (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' x t : GL (Fin 2) (w.1.adicCompletion L)) :
    t ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL δ' ↔
      x⁻¹ * t * x ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL
        (x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) := by
  rw [mem_sigmaCentralizer_iff_inv, mem_sigmaCentralizer_iff_inv]
  have key : (x⁻¹ * t * x)⁻¹ * (x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) *
      (InertTransport.thetaAut K L σ v w hdeg e).mapGL (x⁻¹ * t * x) =
      x⁻¹ * (t⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL t) *
        (InertTransport.thetaAut K L σ v w hdeg e).mapGL x := by
    simp only [map_mul, map_inv]
    group
  rw [key, mul_left_inj, mul_right_inj]

private theorem split_mem_twistedConjStabilizer_twistedConj (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' x s' t : GL (Fin 2) (w.1.adicCompletion L)) :
    t ∈ TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' s' ↔
      x⁻¹ * t * x ∈ TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) (x⁻¹ * s') := by
  rw [TwistedTorusIndices.mem_twistedConjStabilizer_iff, TwistedTorusIndices.mem_twistedConjStabilizer_iff,
    ← split_mem_sigmaCentralizer_twistedConj K L σ v w hdeg e δ' x t]
  have key : (x⁻¹ * s')⁻¹ * (x⁻¹ * t * x) * (x⁻¹ * s') = s'⁻¹ * t * s' := by group
  rw [key]

private theorem split_twistedConjStabilizer_eq_comap (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' x s' : GL (Fin 2) (w.1.adicCompletion L)) :
    TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' s' =
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) (x⁻¹ * s')).comap
          (MulAut.conj x⁻¹).toMonoidHom := by
  ext t
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact split_mem_twistedConjStabilizer_twistedConj K L σ v w hdeg e δ' x s' t

private theorem split_relIndex_twistedConj (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' x s' y₀ : GL (Fin 2) (w.1.adicCompletion L)) :
    (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' s').relIndex
        (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' y₀) =
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
          (x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) (x⁻¹ * s')).relIndex
        (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
          (x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) (x⁻¹ * y₀)) := by
  rw [split_twistedConjStabilizer_eq_comap K L σ v w hdeg e δ' x s',
    split_twistedConjStabilizer_eq_comap K L σ v w hdeg e δ' x y₀, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective]
  exact (MulAut.conj x⁻¹).surjective

private theorem split_relIndex_twistedConjStabilizer_ne_zero (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (s' y₀ : GL (Fin 2) (w.1.adicCompletion L)) :
    (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        s').relIndex
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        y₀) ≠ 0 := by
  haveI : CompactSpace (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) y₀) :=
    isCompact_iff_compactSpace.1 (TwistedTorusIndices.isCompact_twistedConjStabilizer _ _
      (isClosed_sigmaCentralizer_glEquiv K L σ v w hdeg e δ)
      (TwistedTorusIndices.isCompact_integralUnitsSet_range L w.1) y₀)
  have hopen : IsOpen (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) s').subgroupOf (TwistedTorusIndices.twistedConjStabilizer
        (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) y₀) :
      Subgroup (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) y₀)) :
      Set (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) y₀)) := by
    have hset : (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) s').subgroupOf (TwistedTorusIndices.twistedConjStabilizer
          (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ) y₀) :
        Subgroup (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
          (glEquiv K L v w e δ) y₀)) :
        Set (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
          (glEquiv K L v w e δ) y₀)) =
        (fun t : TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
            (glEquiv K L v w e δ) y₀ => s'⁻¹ * (t : GL (Fin 2) (w.1.adicCompletion L)) * s') ⁻¹'
          integralUnitsSet (Set.range (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))) := by
      ext t
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, TwistedTorusIndices.mem_twistedConjStabilizer_iff,
        Set.mem_preimage]
      exact ⟨fun h => h.2, fun h => ⟨((TwistedTorusIndices.mem_twistedConjStabilizer_iff _ _ _ _).1 t.2).1, h⟩⟩
    rw [hset]
    exact (TwistedTorusIndices.isOpen_integralUnitsSet_range L w.1).preimage
      ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  haveI := Subgroup.quotient_finite_of_isOpen _ hopen
  show ((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
      s').subgroupOf (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) y₀)).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

private theorem split_measureReal_eq_relIndex_mul (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁)
    (g' s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hle : TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e s) ≤
      TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e g')) :
    (τ₁ {t | g'⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * g' ∈ semiLocalIntegralSet K L v}).toReal =
      ((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e s)).relIndex
        (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e g')) : ℝ) *
        (τ₁ {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v}).toReal := by
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    (isTopologicalGroup_tensorGL K L (v.adicCompletion K)).toContinuousMul
  haveI := hτ₁
  have hKT : (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) (glEquiv K L v w e g')).comap
        (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L)) ≤
      twistedCentralizer K L (v.adicCompletion K) σ δ := by
    rw [← comap_sigmaCentralizer_glEquiv K L σ v w hdeg e δ]
    exact Subgroup.comap_mono fun t ht => ((TwistedTorusIndices.mem_twistedConjStabilizer_iff _ _ _ _).1 ht).1
  have hle' : ((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) (glEquiv K L v w e s)).comap
        (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ) ≤
      ((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) (glEquiv K L v w e g')).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
            (twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    fun t ht => Subgroup.mem_subgroupOf.2 (Subgroup.comap_mono hle (Subgroup.mem_subgroupOf.1 ht))
  have hidx' : (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) (glEquiv K L v w e s)).comap
        (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ)).relIndex
      (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) (glEquiv K L v w e g')).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
            (twistedCentralizer K L (v.adicCompletion K) σ δ)) =
      (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e s)).relIndex
        (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e g')) := by
    rw [Subgroup.relIndex_subgroupOf hKT, relIndex_comap_glEquiv]
  have hfin : (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
      (glEquiv K L v w e δ) (glEquiv K L v w e s)).comap
        (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
          (twistedCentralizer K L (v.adicCompletion K) σ δ)).relIndex
      (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
        (glEquiv K L v w e δ) (glEquiv K L v w e g')).comap
          (glEquiv K L v w e : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L))).subgroupOf
            (twistedCentralizer K L (v.adicCompletion K) σ δ)) ≠ 0 := by
    rw [hidx']
    exact split_relIndex_twistedConjStabilizer_ne_zero K L σ v w hdeg e δ _ _
  have hmeas := measurableSet_subgroupOf_comap_twistedConjStabilizer K L σ v w hdeg e δ (glEquiv K L v w e s)
  have hm := TwistedTorusIndices.measure_coe_eq_relIndex_mul τ₁ hle' hfin hmeas
  rw [coe_subgroupOf_comap_twistedConjStabilizer K L σ v w hdeg e δ s,
    coe_subgroupOf_comap_twistedConjStabilizer K L σ v w hdeg e δ g', hidx'] at hm
  rw [hm, ENNReal.toReal_mul, ENNReal.toReal_natCast]

private theorem split_measureReal_ne_zero (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁)
    (g' : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (τ₁ {t | g'⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * g' ∈ semiLocalIntegralSet K L v}).toReal ≠ 0 := by
  letI := twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
    (isTopologicalGroup_tensorGL K L (v.adicCompletion K)).toContinuousMul
  haveI := hτ₁
  refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
  · have hopen : IsOpen {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
        g'⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * g' ∈ semiLocalIntegralSet K L v} :=
      (isOpen_semiLocalIntegralSet K L v).preimage
        ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    refine (IsOpen.measure_pos τ₁ hopen ⟨1, ?_⟩).ne'
    show g'⁻¹ * ((1 : twistedCentralizer K L (v.adicCompletion K) σ δ) : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
      g' ∈ semiLocalIntegralSet K L v
    rw [OneMemClass.coe_one, mul_one, inv_mul_cancel]
    exact one_mem_semiLocalIntegralSet K L v
  · have hsub : {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
        g'⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * g' ∈ semiLocalIntegralSet K L v} ⊆
        Subtype.val ⁻¹' ((fun u : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => g' * u * g'⁻¹) ''
          semiLocalIntegralSet K L v) := by
      intro t ht
      refine ⟨g'⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * g', ht, ?_⟩
      show g' * (g'⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * g') * g'⁻¹ =
        (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      group
    refine ((measure_mono hsub).trans_lt ?_).ne
    exact ((isClosed_twistedCentralizer K L σ v w hdeg e δ).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((isCompact_semiLocalIntegralSet K L v).image
        ((continuous_const.mul continuous_id).mul continuous_const))).measure_lt_top

private theorem split_prod_range_succ (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (a : w.1.adicCompletion L) (r : ℕ) :
    ∏ i ∈ Finset.range (r + 1), (θ ^ i) a = a * θ (∏ i ∈ Finset.range r, (θ ^ i) a) := by
  rw [Finset.prod_range_succ', map_prod, pow_zero, AlgEquiv.one_apply, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_succ', AlgEquiv.mul_apply]

private theorem split_coe_sigmaPartialNorm_diagonal (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (a b : w.1.adicCompletion L)
    (D : GL (Fin 2) (w.1.adicCompletion L))
    (hD : (D : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) = !![a, 0; 0, b]) (r : ℕ) :
    ((sigmaPartialNorm (InertTransport.thetaAut K L σ v w hdeg e).mapGL D r : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![∏ i ∈ Finset.range r, (InertTransport.thetaAlg K L σ v w e ^ i) a, 0;
        0, ∏ i ∈ Finset.range r, (InertTransport.thetaAlg K L σ v w e ^ i) b] := by
  induction r with
  | zero => simp [Matrix.one_fin_two]
  | succ r ih =>
    rw [sigmaPartialNorm_succ', Units.val_mul, split_thetaAut_mapGL K L σ v w hdeg e, coe_generalLinearGroup_map, ih,
      hD, split_prod_range_succ K L v w, split_prod_range_succ K L v w]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

private theorem split_conj_sigmaNormPow_twistedConj (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' y x : GL (Fin 2) (w.1.adicCompletion L)) :
    (x⁻¹ * y)⁻¹ *
        sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
          (x⁻¹ * δ' * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) *
        (x⁻¹ * y) =
      y⁻¹ * sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) δ' * y := by
  rw [sigmaNormPow_sigmaConjElt _ _ (split_thetaAut_mapGL_iterate_finrank K L σ v w hdeg e x)]
  group

private theorem split_twistedConjStabilizer_eq_one (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' : GL (Fin 2) (w.1.adicCompletion L)) (α β : (v.adicCompletion K)ˣ) (hαβ : α ≠ β)
    (hN : ((sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) δ' :
        GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)])
    (y : GL (Fin 2) (w.1.adicCompletion L))
    (hy : ((y⁻¹ * sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) δ' * y :
        GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)]) :
    TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' y =
      TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' 1 :=
  le_antisymm
    (split_twistedConjStabilizer_le K L σ v w hdeg e δ' α β hαβ 1 (by rw [inv_one, one_mul, mul_one]; exact hN) y)
    (split_twistedConjStabilizer_le K L σ v w hdeg e δ' α β hαβ y hy 1)

private theorem split_twistedConjStabilizer_one (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' : GL (Fin 2) (w.1.adicCompletion L)) :
    TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' 1 =
      sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL δ' ⊓
        LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) := by
  ext z
  rw [TwistedTorusIndices.mem_twistedConjStabilizer_iff, Subgroup.mem_inf, inv_one, one_mul, mul_one,
    split_mem_integralUnitsSet_iff K L v w]

private theorem split_inf_map_eq_twistedConjStabilizer (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ' : GL (Fin 2) (w.1.adicCompletion L)) (y : GL (Fin 2) (w.1.adicCompletion L)) :
    sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL δ' ⊓
        (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)).map
          (MulAut.conj y).toMonoidHom =
      TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) δ' y :=
  rfl

private theorem split_coe_conj_sigmaNormPow_glEquiv (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (γ : GL (Fin 2) (v.adicCompletion K)) (g : GL (Fin 2) (v.adicCompletion K)) (α β : (v.adicCompletion K)ˣ)
    (hg : ((g⁻¹ * γ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L (v.adicCompletion K) σ γ δ 1) :
    ((((InertTransport.iota K L v w).mapGL g)⁻¹ *
      sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L) (glEquiv K L v w e δ) *
        (InertTransport.iota K L v w).mapGL g : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)] := by
  have hnorm := sigmaNormPow_glEquiv_eq_mapGL K L σ v w hdeg e γ δ hN
  rw [hnorm, ← map_inv, ← map_mul, ← map_mul]
  ext i j
  rw [InertTransport.generalLinearGroup_map_coe_apply, hg]
  fin_cases i <;> fin_cases j <;> simp [iota_toField_apply]

private theorem split_exists_twistedConj_eq_diagonal (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (γ : GL (Fin 2) (v.adicCompletion K)) (g : GL (Fin 2) (v.adicCompletion K)) (α β : (v.adicCompletion K)ˣ)
    (hαβ : α ≠ β)
    (hg : ((g⁻¹ * γ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L (v.adicCompletion K) σ γ δ 1) :
    ∃ (x : GL (Fin 2) (w.1.adicCompletion L)) (a b : (w.1.adicCompletion L)ˣ),
      ((x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x :
            GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
          !![(a : w.1.adicCompletion L), 0; 0, (b : w.1.adicCompletion L)] ∧
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
          ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
            (InertTransport.thetaAlg K L σ v w e ^ i) (a : w.1.adicCompletion L) ∧
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
          ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
            (InertTransport.thetaAlg K L σ v w e ^ i) (b : w.1.adicCompletion L) := by
  have hdiag := split_coe_conj_sigmaNormPow_glEquiv K L σ v w hdeg e γ g α β hg δ hN
  have hdiag' := hdiag
  rw [← InertTransport.glEquiv_normString K L σ v w hdeg e δ,
    InertTransport.glEquiv_normString_eq_prod K L σ v w hdeg e δ] at hdiag'
  have hdock :=
    AutomorphicForm.exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne K v L w
      (InertTransport.thetaAlg K L σ v w e) α β hαβ (glEquiv K L v w e δ) ((InertTransport.iota K L v w).mapGL g)
      hdiag'
  obtain ⟨x, a, b, hxD, ha, hb⟩ := hdock
  rw [← split_thetaAut_mapGL_eq K L σ v w hdeg e] at hxD
  exact ⟨x, a, b, hxD, ha, hb⟩

private theorem split_inv_mul_mul_map_eq {G : Type*} [Group G] (φ : G →* G) (S D x : G) :
    S⁻¹ * D * φ S = (x⁻¹ * S)⁻¹ * (x⁻¹ * D * φ x) * φ (x⁻¹ * S) := by
  rw [map_mul, map_inv]
  group

private theorem split_mass_mul_div_eq (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
    (g : GL (Fin 2) (v.adicCompletion K)) (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hles : TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e s) ≤
      TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
        (glEquiv K L v w e (toTensorGL K L (v.adicCompletion K) g))) :
    ((τ₁ {t | (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
        toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v}).toReal : ℂ) *
      ((f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s)) /
        ((τ₁ {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈ semiLocalIntegralSet K L v}).toReal :
          ℂ)) =
    (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e s)).relIndex
        (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
          (glEquiv K L v w e δ) (glEquiv K L v w e (toTensorGL K L (v.adicCompletion K) g))) : ℕ) : ℂ) *
      (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
        (glEquiv K L v w e (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s)) := by
  have hMne := split_measureReal_ne_zero K L σ v w hdeg e δ τ₁ hτ₁ (toTensorGL K L (v.adicCompletion K) g)
  have hmass := split_measureReal_eq_relIndex_mul K L σ v w hdeg e δ τ₁ hτ₁ _ s hles
  have hms : (τ₁ {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈
      semiLocalIntegralSet K L v}).toReal ≠ 0 := by
    intro h0
    apply hMne
    rw [hmass, h0, mul_zero]
  have hms' : (((τ₁ {t | s⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * s ∈
      semiLocalIntegralSet K L v}).toReal : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hms
  rw [hmass]
  push_cast
  field_simp

private theorem split_exists_finset_mass_mul_eq_sum (hdeg : (Module.finrank K L).Prime)
    (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ))
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I' : ℂ}
    (hI' : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ₁
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I')
    (g : GL (Fin 2) (v.adicCompletion K))
    (hle : ∀ s : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e s) ≤
        TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e (toTensorGL K L (v.adicCompletion K) g))) :
    ∃ S₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (∀ s ∈ S₀, ∀ s' ∈ S₀, ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
        ∀ u ∈ semiLocalIntegralSet K L v, s' = t * s * u → s' = s) ∧
      (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
            (glEquiv K L v w e (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x)) ≠ 0 →
          ∃ s ∈ S₀, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
            ∃ u ∈ semiLocalIntegralSet K L v, x = t * s * u) ∧
      ((τ₁ {t | (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
      toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v}).toReal : ℂ) * I' =
      ∑ s ∈ S₀,
        (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
              (glEquiv K L v w e δ) (glEquiv K L v w e s)).relIndex
            (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
              (glEquiv K L v w e δ) (glEquiv K L v w e (toTensorGL K L (v.adicCompletion K) g))) : ℕ) : ℂ) *
          (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
            (glEquiv K L v w e (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s)) := by
  have hreps := exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString K L v σ δ hδ
    (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
    (twisted_hecke_finite_support K L v w f e)
  obtain ⟨S₀, hS₀, hcov⟩ := hreps
  have hIval : I' = twistedRealisedValue K L v σ δ τ₁
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) S₀ :=
    IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
      (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ₁ hτ₁
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
      (twisted_hecke_measurable K L v w f e) (twisted_hecke_bounded K L v w f e) hI'
      (isTwistedOrbitalIntegralOn_semiLocalHaar_sum_div_of_forall_eq_of_forall_exists K L v σ δ hδ τ₁ hτ₁
        (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y))
        (twisted_hecke_bi_invariant K L v w f e) S₀ hS₀ hcov)

  have hsum : ((τ₁ {t | (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
      toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v}).toReal : ℂ) * I' =
      ∑ s ∈ S₀,
        (((TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
              (glEquiv K L v w e δ) (glEquiv K L v w e s)).relIndex
            (TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e)
              (glEquiv K L v w e δ) (glEquiv K L v w e (toTensorGL K L (v.adicCompletion K) g))) : ℕ) : ℂ) *
          (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
            (glEquiv K L v w e (s⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ s)) := by
    rw [hIval, twistedRealisedValue, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => split_mass_mul_div_eq K L σ v w hdeg e δ τ₁ hτ₁ f g s (hle s)
  exact ⟨S₀, hS₀, hcov, hsum⟩

private theorem split_forall_image_eq_of_eq_mul (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (x : GL (Fin 2) (w.1.adicCompletion L))
    (S₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (S' : Finset (GL (Fin 2) (w.1.adicCompletion L)))
    (hS' : ∀ y : GL (Fin 2) (w.1.adicCompletion L), y ∈ S' ↔ ∃ s ∈ S₀, x⁻¹ * glEquiv K L v w e s = y)
    (hS₀ : ∀ s ∈ S₀, ∀ s' ∈ S₀, ∀ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∀ u ∈ semiLocalIntegralSet K L v, s' = t * s * u → s' = s) :
    ∀ y ∈ S', ∀ y' ∈ S',
      ∀ t ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL
        (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x),
        ∀ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
          y' = t * y * u → y' = y := by
  classical
  have hS₁ := forall_image_glEquiv_of_forall K L σ v w hdeg e δ S₀ hS₀
  intro y hy y' hy' t ht u hu hEq
  rw [hS'] at hy hy'
  obtain ⟨s₁, hs₁, rfl⟩ := hy
  obtain ⟨s₂, hs₂, rfl⟩ := hy'
  have ht' : x * t * x⁻¹ ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL
      (glEquiv K L v w e δ) := by
    rw [split_mem_sigmaCentralizer_twistedConj K L σ v w hdeg e _ x]
    have hx : x⁻¹ * (x * t * x⁻¹) * x = t := by group
    rw [hx]
    exact ht
  have h := hS₁ (glEquiv K L v w e s₁) (Finset.mem_image_of_mem _ hs₁) (glEquiv K L v w e s₂)
    (Finset.mem_image_of_mem _ hs₂) (x * t * x⁻¹) ht' u ((split_mem_integralUnitsSet_iff K L v w u).2 hu)
    (by
      calc glEquiv K L v w e s₂ = x * (x⁻¹ * glEquiv K L v w e s₂) := by group
        _ = x * (t * (x⁻¹ * glEquiv K L v w e s₁) * u) := by rw [hEq]
        _ = x * t * x⁻¹ * glEquiv K L v w e s₁ * u := by group)
  rw [h]

private theorem split_forall_ne_zero_exists_image (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (x : GL (Fin 2) (w.1.adicCompletion L))
    (S₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (S' : Finset (GL (Fin 2) (w.1.adicCompletion L)))
    (hS' : ∀ y : GL (Fin 2) (w.1.adicCompletion L), y ∈ S' ↔ ∃ s ∈ S₀, x⁻¹ * glEquiv K L v w e s = y)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
    (hcov : ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (glEquiv K L v w e (y⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ y)) ≠ 0 →
        ∃ s ∈ S₀, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∃ u ∈ semiLocalIntegralSet K L v, y = t * s * u) :
    ∀ z : GL (Fin 2) (w.1.adicCompletion L),
      (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (z⁻¹ * (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) *
            Matrix.GeneralLinearGroup.map (InertTransport.thetaAlg K L σ v w e).toAlgHom.toRingHom z) ≠ 0 →
        ∃ s ∈ S',
          ∃ t ∈ sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL
            (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x),
            ∃ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
              z = t * s * u := by
  classical
  have hcov' := exists_image_glEquiv_of_exists K L σ v w hdeg e δ S₀
    (fun z => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) z ≠ 0) hcov
  rw [← split_thetaAut_mapGL_eq K L σ v w hdeg e]
  intro z hz
  have hz' : (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) ((x * z)⁻¹ * glEquiv K L v w e δ *
      (InertTransport.thetaAut K L σ v w hdeg e).mapGL (x * z)) ≠ 0 := by
    have hxz : (x * z)⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL (x * z) =
        z⁻¹ * (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) *
          (InertTransport.thetaAut K L σ v w hdeg e).mapGL z := by
      rw [map_mul]
      group
    rw [hxz]
    exact hz
  obtain ⟨s', hs', t, ht, u, hu, hEq⟩ := hcov' (x * z) hz'
  rw [Finset.mem_image] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  refine ⟨x⁻¹ * glEquiv K L v w e s, (hS' _).2 ⟨s, hs, rfl⟩, x⁻¹ * t * x,
    (split_mem_sigmaCentralizer_twistedConj K L σ v w hdeg e _ x t).1 ht, u,
    (split_mem_integralUnitsSet_iff K L v w u).1 hu, ?_⟩
  calc z = x⁻¹ * (x * z) := by group
    _ = x⁻¹ * (t * glEquiv K L v w e s * u) := by rw [hEq]
    _ = x⁻¹ * t * x * (x⁻¹ * glEquiv K L v w e s) * u := by group

private theorem split_twisted_mass_mul_eq_finsum (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (γ : GL (Fin 2) (v.adicCompletion K)) (hrs : IsRegularSemisimple γ) (g : GL (Fin 2) (v.adicCompletion K))
    (α β : (v.adicCompletion K)ˣ) (hαβ : α ≠ β)
    (hg : ((g⁻¹ * γ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L (v.adicCompletion K) σ γ δ 1)
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I' : ℂ}
    (hI' : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ₁
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I') :
    ∃ a b : (w.1.adicCompletion L)ˣ,
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
          ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
            (InertTransport.thetaAlg K L σ v w e ^ i) (a : w.1.adicCompletion L) ∧
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
          ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
            (InertTransport.thetaAlg K L σ v w e ^ i) (b : w.1.adicCompletion L) ∧
        ((τ₁ {t | (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v}).toReal : ℂ) * I' =
          (Ideal.absNorm v.asIdeal : ℂ) ^ m *
            ∑ᶠ c : GL (Fin 2) (w.1.adicCompletion L) ⧸
              LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
            Set.indicator
              {c : GL (Fin 2) (w.1.adicCompletion L) ⧸
                  LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) |
                ∃ g : GL (Fin 2) (w.1.adicCompletion L), QuotientGroup.mk g = c ∧
                  (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 ∧
                  (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 = (a : w.1.adicCompletion L) ∧
                  (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 = (b : w.1.adicCompletion L)}
              (fun c => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Quotient.out c)) c := by
  classical
  have hδ : IsRegularSemisimple (normString K L (v.adicCompletion K) σ δ) :=
    isRegularSemisimple_normString_of_isNormConjugator_one K L σ v γ hrs δ hN
  have hdiag := split_coe_conj_sigmaNormPow_glEquiv K L σ v w hdeg e γ g α β hg δ hN
  have hA := split_exists_twistedConj_eq_diagonal K L σ v w hdeg e γ g α β hαβ hg δ hN
  obtain ⟨x, a, b, hxD, ha, hb⟩ := hA
  refine ⟨a, b, ha, hb, ?_⟩

  have ha' := ha
  have hb' := hb
  rw [InertTransport.finrank_adicCompletion_eq K L v w hdeg e] at ha' hb'
  have hND : ((sigmaNormPow (InertTransport.thetaAut K L σ v w hdeg e).mapGL (Module.finrank K L)
      (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) :
        GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)] := by
    rw [sigmaNormPow_def, split_coe_sigmaPartialNorm_diagonal K L σ v w hdeg e _ _ _ hxD, ← ha', ← hb']

  have hgd := split_conj_sigmaNormPow_twistedConj K L σ v w hdeg e (glEquiv K L v w e δ)
    ((InertTransport.iota K L v w).mapGL g) x
  have hstab := split_twistedConjStabilizer_eq_one K L σ v w hdeg e _ α β hαβ hND
    (x⁻¹ * (InertTransport.iota K L v w).mapGL g) (by rw [hgd]; exact hdiag)

  have hle : ∀ s : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e s) ≤
        TwistedTorusIndices.twistedConjStabilizer (InertTransport.thetaAut K L σ v w hdeg e) (glEquiv K L v w e δ)
          (glEquiv K L v w e (toTensorGL K L (v.adicCompletion K) g)) := fun s => by
    rw [glEquiv_toTensorGL K L v w e g]
    exact split_twistedConjStabilizer_le K L σ v w hdeg e _ α β hαβ _ hdiag _

  have hB := split_exists_finset_mass_mul_eq_sum K L σ v w hdeg hσn e δ hδ τ₁ hτ₁ f hI' g hle
  obtain ⟨S₀, hS₀, hcov, hsum⟩ := hB

  have hT1 := split_twistedConjStabilizer_one K L σ v w hdeg e
    (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x)
  have hTy := split_inf_map_eq_twistedConjStabilizer K L σ v w hdeg e
    (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x)
  have hinj : Set.InjOn (fun s : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => x⁻¹ * glEquiv K L v w e s) ↑S₀ :=
    fun s₁ _ s₂ _ h => (glEquiv K L v w e).injective (mul_left_cancel h)
  have hmain :=
    AutomorphicForm.sum_relIndex_mul_twistedConj_diagonal_eq_zpow_absNorm_mul_finsum_of_ramificationIdx_eq_one
      K v L w hw (InertTransport.thetaAlg K L σ v w e)
    (fun z => InertTransport.thetaAlg_apply_eq_self_iff K L σ v w hdeg hσ1 e z) f a b α β ha hb m hm
    (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x) hxD
    (sigmaCentralizer (InertTransport.thetaAut K L σ v w hdeg e).mapGL
      (x⁻¹ * glEquiv K L v w e δ * (InertTransport.thetaAut K L σ v w hdeg e).mapGL x))
    (by
      rw [← split_thetaAut_mapGL_eq K L σ v w hdeg e]
      exact fun z => mem_sigmaCentralizer_iff_inv)
    (S₀.image fun s => x⁻¹ * glEquiv K L v w e s)
    (split_forall_image_eq_of_eq_mul K L σ v w hdeg e δ x S₀ (S₀.image fun s => x⁻¹ * glEquiv K L v w e s)
      (fun _ => Finset.mem_image) hS₀)
    (split_forall_ne_zero_exists_image K L σ v w hdeg e δ x S₀ (S₀.image fun s => x⁻¹ * glEquiv K L v w e s)
      (fun _ => Finset.mem_image) f hcov)
  rw [← split_thetaAut_mapGL_eq K L σ v w hdeg e] at hmain
  rw [hsum, ← hmain, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun s _ => ?_
  try dsimp only
  congr 2
  · rw [hTy, ← hT1, ← hstab, ← split_relIndex_twistedConj K L σ v w hdeg e _ x, glEquiv_toTensorGL K L v w e g]
  · rw [glEquiv_twistedConj_mapGL K L σ v w hdeg e s δ]
    exact congrArg (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
      (split_inv_mul_mul_map_eq (InertTransport.thetaAut K L σ v w hdeg e).mapGL (glEquiv K L v w e s)
        (glEquiv K L v w e δ) x)

private noncomputable def split_diagUnit {F : Type*} [Field F] (c : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(c : F), 0; 0, 1] (by rw [Matrix.det_fin_two_of]; simp)

private theorem split_coe_diagUnit {F : Type*} [Field F] (c : Fˣ) :
    ((split_diagUnit c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, 1] :=
  rfl

private theorem split_exponent_eq (hdeg : (Module.finrank K L).Prime)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (α : (v.adicCompletion K)ˣ) (a : (w.1.adicCompletion L)ˣ)
    (ha : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (InertTransport.thetaAlg K L σ v w e ^ i) (a : w.1.adicCompletion L))
    (k : ℤ) (u : (v.adicCompletionIntegers K)ˣ)
    (hα : (α : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k)
    (k' : ℤ) (u' : (w.1.adicCompletionIntegers L)ˣ)
    (ha' : (a : w.1.adicCompletion L) = algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) u' *
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ((InertTransport.iota K L v w).toBase ϖ) ^ k') :
    k = Module.finrank K L * k' := by
  have ha₁ := ha
  rw [InertTransport.finrank_adicCompletion_eq K L v w hdeg e] at ha₁
  refine eq_finrank_mul_of_sigmaNormPow_eq K L σ v w hdeg e hw ϖ hϖ (split_diagUnit α) k u ?_
    ((glEquiv K L v w e).symm (split_diagUnit a)) ?_ k' u' ?_
  · rw [split_coe_diagUnit, Matrix.det_fin_two_of]
    simp [hα]
  · rw [MulEquiv.apply_symm_apply]
    have hone : ∏ i ∈ Finset.range (Module.finrank K L),
        (InertTransport.thetaAlg K L σ v w e ^ i) (1 : w.1.adicCompletion L) = 1 :=
      Finset.prod_eq_one fun i _ => map_one _
    have hL := split_coe_sigmaPartialNorm_diagonal K L σ v w hdeg e _ _ _ (split_coe_diagUnit a) (Module.finrank K L)
    rw [← ha₁, hone] at hL
    ext i j
    rw [sigmaNormPow_def, hL, InertTransport.generalLinearGroup_map_coe_apply, split_coe_diagUnit]
    fin_cases i <;> fin_cases j <;> simp [iota_toField_apply]
  · rw [MulEquiv.apply_symm_apply, split_coe_diagUnit, Matrix.det_fin_two_of]
    simp [ha']

private theorem split_twisted_mass_mul_eq (hdeg : (Module.finrank K L).Prime)
    (hσ1 : σ ≠ 1) (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hrs : IsRegularSemisimple γ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L (v.adicCompletion K) σ γ δ 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hSL : ∀ (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
        (a b : ℤ),
      (SL f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) (w.1.adicCompletion L) ⧸
          integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Set.indicator
          {c : GL (Fin 2) (w.1.adicCompletion L) ⧸
              integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) |
            ∃ g : GL (Fin 2) (w.1.adicCompletion L), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 =
                algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)
                  ((InertTransport.iota K L v w).toBase ϖ) ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 =
                algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)
                  ((InertTransport.iota K L v w).toBase ϖ) ^ b}
          (fun c => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Quotient.out c)) c)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁) {I' : ℂ}
    (hI' : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ₁
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I')
    (g : GL (Fin 2) (v.adicCompletion K)) (α β : (v.adicCompletion K)ˣ)
    (hg : ((g⁻¹ * γ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (hαβ : α ≠ β) (m : ℤ)
    (hm : Valued.v ((1 : v.adicCompletion K) - (β : v.adicCompletion K) / (α : v.adicCompletion K)) =
      ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (kα kβ : ℤ) (uα uβ : (v.adicCompletionIntegers K)ˣ)
    (hα : (α : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uα *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kα)
    (hβ : (β : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uβ *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kβ) :
    ((τ₁ {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
          (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v}).toReal : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) * I' =
      (((mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL) f).coeff (kα, kβ) := by
  have _ := hres
  have _ := hγ
  obtain ⟨a, b, ha, hb, hmass⟩ :=
    split_twisted_mass_mul_eq_finsum K L σ v w hdeg hσ1 hσn e hw γ hrs g α β hαβ hg m hm δ hN τ₁ hτ₁ f hI'
  have hϖ' := InertTransport.irreducible_iota_toBase K L v w hw hϖ
  obtain ⟨ka, ua, hua⟩ := exists_units_mul_zpow_of_ne_zero L w.1 _ hϖ' a.ne_zero
  obtain ⟨kb, ub, hub⟩ := exists_units_mul_zpow_of_ne_zero L w.1 _ hϖ' b.ne_zero
  have hka := split_exponent_eq K L σ v w hdeg e hw ϖ hϖ α a ha kα uα hα ka ua hua
  have hkb := split_exponent_eq K L σ v w hdeg e hw ϖ hϖ β b hb kβ uβ hβ kb ub hub
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

  rw [hua, hub,
    mul_comm (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) (ua : w.1.adicCompletionIntegers L)),
    mul_comm (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) (ub : w.1.adicCompletionIntegers L)),
    split_setOf_exists_rep_diag_mul, ← hSL f ka kb] at hmass

  have hid : ∀ p : ℤ × ℤ, (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ)) p =
      ((Module.finrank K L : ℤ) * p.1, (Module.finrank K L : ℤ) * p.2) := fun p => by
    simp [Prod.ext_iff]
  have hn0 : (Module.finrank K L : ℤ) ≠ 0 := by exact_mod_cast hdeg.ne_zero
  have hinj : Function.Injective (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ)) := by
    intro p q hpq
    rw [hid, hid, Prod.mk.injEq] at hpq
    exact Prod.ext (mul_left_cancel₀ hn0 hpq.1) (mul_left_cancel₀ hn0 hpq.2)
  have hpt : (kα, kβ) = (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ)) (ka, kb) := by
    rw [hid, hka, hkb]
  have heval : (((mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL) f).coeff (kα, kβ) =
      (SL f).coeff (ka, kb) := by
    rw [AlgHom.comp_apply, hpt]
    exact Finsupp.mapDomain_apply hinj (SL f).coeff (ka, kb)
  rw [heval]
  calc ((τ₁ {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
          (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v}).toReal : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) * I' =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) *
        (((τ₁ {t : twistedCentralizer K L (v.adicCompletion K) σ δ |
          (toTensorGL K L (v.adicCompletion K) g)⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) *
            toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v}).toReal : ℂ) * I') := by ring
    _ = (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) * ((Ideal.absNorm v.asIdeal : ℂ) ^ m * (SL f).coeff (ka, kb)) := by
      rw [hmass]
    _ = (SL f).coeff (ka, kb) := by
      rw [← mul_assoc, zpow_neg, inv_mul_cancel₀ (zpow_ne_zero m hN0), one_mul]

private theorem split_isGalois (F E : Type) [Field F] [Field E] [Algebra F E] (hdeg : (Module.finrank F E).Prime)
    (θ : E ≃ₐ[F] E) (hθ : θ ≠ 1) : IsGalois F E := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hdeg.pos
  exact IsGalois.of_fixedField_eq_bot F E (le_bot_iff.mp
    ((IntermediateField.fixedField_le le_top).trans_eq (InertTransport.fixedField_zpowers_eq_bot F E hdeg θ hθ)))

private theorem split_prod_pow_apply_eq_algebraMap_norm (F E : Type) [Field F] [Field E] [Algebra F E]
    (hdeg : (Module.finrank F E).Prime) (θ : E ≃ₐ[F] E) (hθ : θ ≠ 1) (y : E) :
    ∏ i ∈ Finset.range (Module.finrank F E), (θ ^ i) y = algebraMap F E (Algebra.norm F y) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hdeg.pos
  haveI : IsGalois F E := split_isGalois F E hdeg θ hθ
  have hbot := InertTransport.fixedField_zpowers_eq_bot F E hdeg θ hθ

  have horder : orderOf θ = Module.finrank F E := by
    have htower := Module.finrank_mul_finrank F (IntermediateField.fixedField (Subgroup.zpowers θ)) E
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers] at htower
    rw [hbot, IntermediateField.finrank_bot, one_mul] at htower
    exact htower
  have hinj : Function.Injective fun i : Fin (Module.finrank F E) => θ ^ (i : ℕ) := by
    intro i j hij
    refine Fin.ext (pow_injOn_Iio_orderOf ?_ ?_ hij)
    · rw [Set.mem_Iio, horder]
      exact i.2
    · rw [Set.mem_Iio, horder]
      exact j.2
  have hcard : Fintype.card (Fin (Module.finrank F E)) = Fintype.card (E ≃ₐ[F] E) := by
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  have hbij : Function.Bijective fun i : Fin (Module.finrank F E) => θ ^ (i : ℕ) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
  rw [Algebra.norm_eq_prod_automorphisms, Finset.prod_range fun i => (θ ^ i) y]
  exact Fintype.prod_bijective (fun i : Fin (Module.finrank F E) => θ ^ (i : ℕ)) hbij (fun i => (θ ^ (i : ℕ)) y)
    (fun ρ => ρ y) fun _ => rfl

private theorem split_inertia_eq_bot [IsGalois K L]
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1) :
    w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ := by
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨asIdeal_eq_under K L v w⟩
  haveI : w.1.asIdeal.IsMaximal := w.1.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Module.Finite (𝓞 K) (𝓞 L) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field (𝓞 L ⧸ w.1.asIdeal) := Ideal.Quotient.field w.1.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have hcard : Nat.card (w.1.asIdeal.inertia (L ≃ₐ[K] L)) = Ideal.ramificationIdxIn v.asIdeal (𝓞 L) :=
    Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal w.1.asIdeal
  have hidx : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = v.asIdeal.ramificationIdx' w.1.asIdeal :=
    (Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.1.asIdeal (L ≃ₐ[K] L)).trans
      (Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.1.asIdeal v.ne_bot).symm
  have hw' : v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
    rw [asIdeal_eq_under K L v w]
    exact hw
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hcard, hidx, hw'])

private theorem split_isNormOf_of_dvd (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (γ g : GL (Fin 2) (v.adicCompletion K))
    (α β : (v.adicCompletion K)ˣ)
    (hg : ((g⁻¹ * γ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      !![(α : v.adicCompletion K), 0; 0, (β : v.adicCompletion K)])
    (kα kβ : ℤ) (uα uβ : (v.adicCompletionIntegers K)ˣ)
    (hα : (α : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uα *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kα)
    (hβ : (β : v.adicCompletion K) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uβ *
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ kβ)
    (hkα : (Module.finrank K L : ℤ) ∣ kα) (hkβ : (Module.finrank K L : ℤ) ∣ kβ) :
    ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ := by
  classical
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  haveI : IsGalois K L := split_isGalois K L hdeg σ hσ1
  have hIw : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ := split_inertia_eq_bot K L v w hw
  have hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime := by
    rw [InertTransport.finrank_adicCompletion_eq K L v w hdeg e]
    exact hdeg
  have hθ1 : InertTransport.thetaAlg K L σ v w e ≠ 1 := InertTransport.thetaAlg_ne_one K L σ v w hσ1 e

  obtain ⟨yα, hyα1, hyα⟩ := IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot K L v w hIw
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uα) (InertTransport.valued_coe_unit K v uα)
  obtain ⟨yβ, hyβ1, hyβ⟩ := IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot K L v w hIw
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) uβ) (InertTransport.valued_coe_unit K v uβ)
  have hyα0 : yα ≠ 0 := fun h => by
    rw [h, map_zero] at hyα1
    exact zero_ne_one hyα1
  have hyβ0 : yβ ≠ 0 := fun h => by
    rw [h, map_zero] at hyβ1
    exact zero_ne_one hyβ1
  obtain ⟨a', ha'⟩ := hkα
  obtain ⟨b', hb'⟩ := hkβ
  obtain ⟨P, hP⟩ : ∃ P : w.1.adicCompletion L, P = algebraMap (v.adicCompletion K) (w.1.adicCompletion L)
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) := ⟨_, rfl⟩
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact (map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible K v hϖ)

  have hnorm : ∀ (y : w.1.adicCompletion L) (u : (v.adicCompletionIntegers K)ˣ) (k k' : ℤ),
      Algebra.norm (v.adicCompletion K) y = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u →
      k = Module.finrank K L * k' →
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
          (InertTransport.thetaAlg K L σ v w e ^ i).toAlgHom.toRingHom (y * P ^ k') =
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L)
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ k) := by
    intro y u k k' hy hk
    have happ : ∀ i : ℕ, ((InertTransport.thetaAlg K L σ v w e ^ i).toAlgHom.toRingHom :
        w.1.adicCompletion L →+* w.1.adicCompletion L) (y * P ^ k') =
        (InertTransport.thetaAlg K L σ v w e ^ i) y * P ^ k' := by
      intro i
      show (InertTransport.thetaAlg K L σ v w e ^ i) _ = _
      rw [map_mul, map_zpow₀, hP, AlgEquiv.commutes]
    simp_rw [happ]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      split_prod_pow_apply_eq_algebraMap_norm (v.adicCompletion K) (w.1.adicCompletion L) hprime
        (InertTransport.thetaAlg K L σ v w e) hθ1 y,
      hy, hk, map_mul, map_zpow₀, ← hP, InertTransport.finrank_adicCompletion_eq K L v w hdeg e, ← zpow_natCast,
      ← zpow_mul, mul_comm k']

  obtain ⟨δ', hδ'⟩ : ∃ δ' : GL (Fin 2) (w.1.adicCompletion L),
      (δ' : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) = !![yα * P ^ a', 0; 0, yβ * P ^ b'] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![yα * P ^ a', 0; 0, yβ * P ^ b'] (by
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
      exact mul_ne_zero (mul_ne_zero hyα0 (zpow_ne_zero _ hP0)) (mul_ne_zero hyβ0 (zpow_ne_zero _ hP0))), rfl⟩
  refine ⟨(glEquiv K L v w e).symm δ', (toTensorGL K L (v.adicCompletion K) g)⁻¹, ?_⟩
  unfold IsNormConjugator
  apply (glEquiv K L v w e).injective
  rw [inv_inv, map_mul, map_mul, map_inv, InertTransport.glEquiv_normString_eq_prod K L σ v w hdeg e,
    MulEquiv.apply_symm_apply, glEquiv_toTensorGL, glEquiv_toTensorGL]
  have hγ' : γ = g * (g⁻¹ * γ * g) * g⁻¹ := by group
  rw [hγ', map_mul, map_mul, map_inv]
  congr 2

  refine Units.ext ?_
  rw [split_coe_prod_map_pow_of_coe_eq_diagonal (InertTransport.thetaAlg K L σ v w e) δ' _ _ hδ'
      (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
    hnorm yα uα kα a' hyα ha', hnorm yβ uβ kβ b' hyβ hb', IntegralHom.mapGL_coe, hg, ← hα, ← hβ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iota_toField_apply]

private theorem split_eq_of_isNormConjugator_one (hdeg : (Module.finrank K L).Prime)
    (hσ1 : σ ≠ 1) (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hrs : IsRegularSemisimple γ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hN : IsNormConjugator K L (v.adicCompletion K) σ γ δ 1)
    (SK : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hSKT : SK (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) =
      (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) • single ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSKc : SK (heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) = single ((1 : ℤ), (1 : ℤ)) 1)
    (hSK : ∀ (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (a b : ℤ),
      (SK f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
          integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (hSL : ∀ (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
        (a b : ℤ),
      (SL f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) (w.1.adicCompletion L) ⧸
          integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Set.indicator
          {c : GL (Fin 2) (w.1.adicCompletion L) ⧸
              integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) |
            ∃ g : GL (Fin 2) (w.1.adicCompletion L), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 =
                algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)
                  ((InertTransport.iota K L v w).toBase ϖ) ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 =
                algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)
                  ((InertTransport.iota K L v w).toBase ϖ) ^ b}
          (fun c => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Quotient.out c)) c)
    (b : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
      HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (hcomp : SK.comp b = (mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (τ₁ : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ₁)
    (hc : Coupled K L (v.adicCompletion K) σ γ δ 1 τ τ₁)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I I' : ℂ}
    (hI' : IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ₁
      (fun y => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y)) I')
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      ((b f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) : GL (Fin 2)
          (v.adicCompletion K) → ℂ) I) :
    I' = I := by
  classical
  have _ := hSKT
  have _ := hSKc
  have _ := hST
  have _ := hSc
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨g, α, β, hαβ, hg⟩ := split_exists_conj_eq_diagonal two_ne_zero γ hγ hrs
  obtain ⟨kα, uα, hα⟩ := exists_units_mul_zpow_of_ne_zero K v ϖ hϖ α.ne_zero
  obtain ⟨kβ, uβ, hβ⟩ := exists_units_mul_zpow_of_ne_zero K v ϖ hϖ β.ne_zero
  obtain ⟨m, hm⟩ := split_exists_valuation_one_sub_div_eq K v α β hαβ
  have h1 := split_mass_mul_eq K v ϖ γ SK hSK (b f) τ hτ hI g α β hg m hm kα kβ uα uβ hα hβ
  have h2 := split_twisted_mass_mul_eq K L σ v w hdeg hσ1 hσn e hw ϖ hϖ hres γ hγ hrs δ hN SL hSL f τ₁ hτ₁ hI' g α β
    hg hαβ m hm kα kβ uα uβ hα hβ
  have hSb : (SK (b f)).coeff (kα, kβ) = (((mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL) f).coeff
      (kα, kβ) := by
    rw [← AlgHom.comp_apply, hcomp]
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hne : ((τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
      g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈ localIntegralSet K v}).toReal : ℂ) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (split_measureReal_conj_ne_zero K v γ τ hτ g)) hN0
  rw [split_measure_conj_eq_of_coupled K L σ v w e hw γ δ τ τ₁ hc g] at h2
  rw [hSb, ← h2] at h1
  exact (mul_left_cancel₀ hne h1).symm

private theorem split_eq_zero_of_not_isNormOf (hdeg : (Module.finrank K L).Prime)
    (hσ1 : σ ≠ 1) (hσn : σ ^ Module.finrank K L = 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (hrs : IsRegularSemisimple γ)
    (SK : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
      AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hSKT : SK (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) =
      (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) • single ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSKc : SK (heckeIndicator ℂ
        (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) *
          localRepInf ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) = single ((1 : ℤ), (1 : ℤ)) 1)
    (hSK : ∀ (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (a b : ℤ),
      (SK f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
          integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 +
        single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ
        (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
            (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) *
          localRepInf ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L w.1
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
              (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      single ((1 : ℤ), (1 : ℤ)) 1)
    (b : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
      HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (hcomp : SK.comp b = (mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
      (centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel (v.adicCompletion K) γ) τ)
    (hnn : ¬ ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K), IsNormOf K L (v.adicCompletion K) σ γ δ)
    (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) {I : ℂ}
    (hI : IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ
      ((b f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) : GL (Fin 2)
          (v.adicCompletion K) → ℂ) I) :
    I = 0 := by
  classical
  have _ := hσn
  have _ := hres
  have _ := hSKT
  have _ := hSKc
  have _ := hST
  have _ := hSc
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨g, α, β, hαβ, hg⟩ := split_exists_conj_eq_diagonal two_ne_zero γ hγ hrs
  obtain ⟨kα, uα, hα⟩ := exists_units_mul_zpow_of_ne_zero K v ϖ hϖ α.ne_zero
  obtain ⟨kβ, uβ, hβ⟩ := exists_units_mul_zpow_of_ne_zero K v ϖ hϖ β.ne_zero
  obtain ⟨m, hm⟩ := split_exists_valuation_one_sub_div_eq K v α β hαβ
  have h1 := split_mass_mul_eq K v ϖ γ SK hSK (b f) τ hτ hI g α β hg m hm kα kβ uα uβ hα hβ
  have hSb : (SK (b f)).coeff (kα, kβ) =
      (AddMonoidAlgebra.mapDomain (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ)) (SL f)).coeff (kα, kβ) := by
    have hc := AlgHom.congr_fun hcomp f
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at hc
    rw [hc]
    rfl
  by_cases hdvd : (Module.finrank K L : ℤ) ∣ kα ∧ (Module.finrank K L : ℤ) ∣ kβ
  · exact absurd (split_isNormOf_of_dvd K L σ v w hdeg hσ1 e hw ϖ hϖ γ g α β hg kα kβ uα uβ hα hβ hdvd.1 hdvd.2) hnn
  ·
    have h0 : (AddMonoidAlgebra.mapDomain (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ)) (SL f)).coeff (kα, kβ) = 0 := by
      refine Finsupp.mapDomain_notin_range _ _ fun hmem => hdvd ?_
      obtain ⟨⟨i, j⟩, hij⟩ := hmem
      simp only [AddMonoidHom.coe_smul, Pi.smul_apply, AddMonoidHom.id_apply, Prod.smul_mk, nsmul_eq_mul,
        Prod.mk.injEq] at hij
      exact ⟨⟨i, hij.1.symm⟩, ⟨j, hij.2.symm⟩⟩
    have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.mpr fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
    have hne : ((τ {t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) |
        g⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * g ∈ localIntegralSet K v}).toReal : ℂ) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-m) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (split_measureReal_conj_ne_zero K v γ τ hτ g)) hN0
    rw [hSb, h0] at h1
    exact (mul_eq_zero.mp h1).resolve_left hne

end SplitClasses

section ConstantTermHom

open LocalGL2 HeckePair
open scoped Pointwise

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem exists_constantTermHom (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (hϖ : Irreducible ϖ)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    (hfin : (QuotientGroup.mk ''
      ((integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Set (GL (Fin 2) (v.adicCompletion K))) *
        {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) :
        Set (GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion
            K))).Finite) :
    ∃ S : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ
        (ℤ × ℤ),
      (∀ (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (a b : ℤ),
        (S f).coeff (a, b) =
          ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
            Set.indicator
              {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)
                  |
                  ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
                    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
                    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = algebraMap (v.adicCompletionIntegers K)
                        (v.adicCompletion K) ϖ ^ a ∧
                    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = algebraMap (v.adicCompletionIntegers K)
                        (v.adicCompletion K) ϖ ^ b}
              (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c) ∧
      S (heckeIndicator ℂ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) =
        AddMonoidAlgebra.single (1, 0) (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) : ℂ) +
          AddMonoidAlgebra.single (0, 1) 1 ∧
      S (heckeIndicator ℂ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin) = AddMonoidAlgebra.single (1, 1) 1 :=
  exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq ϖ hϖ0 hϖ hfin (R₀ := ℂ)

end ConstantTermHom

section Matching

open scoped TensorProduct TensorProduct.RightActions
p2m_open "AutomorphicForm MeasureTheory LT.LatticeTree~exists_act_stdVertex_eq LocalGL2 P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime.TwistedValues AddMonoidAlgebra LT.TwistedNorm"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum.Extension (𝓞 L) v)

private theorem map_mul_left_semiLocalHaar (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    @Measure.map _ _ (glBorelOf (L ⊗[K] v.adicCompletion K)) (glBorelOf (L ⊗[K] v.adicCompletion K)) (fun z => g * z)
        (semiLocalHaar K L v) = semiLocalHaar K L v := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := isHaarMeasure_semiLocalHaar K L v
  exact map_mul_left_eq_self _ g

private theorem areMatchingLocal_comp (hdeg : (Module.finrank K L).Prime) (hσ1 : σ ≠ 1)
    (e : L ⊗[K] v.adicCompletion K ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hw : Ideal.ramificationIdx' (IsDedekindDomain.HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ})]
    [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ})]
    (hres : Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {(InertTransport.iota K L v w).toBase ϖ}) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖ}) ^ Module.finrank K L)
    (SK : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ
        (ℤ × ℤ))
    (hSK : ∀ (f : HeckeAlgebra (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (a b : ℤ),
      (SK f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) (v.adicCompletion K) ⧸
          integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        Set.indicator
          {c : GL (Fin 2) (v.adicCompletion K) ⧸ integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) |
            ∃ g : GL (Fin 2) (v.adicCompletion K), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
                algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b}
          (fun c => (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (Quotient.out c)) c)
    (hSKT : SK (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) =
      (Nat.card ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ}) : ℂ) • single ((1 : ℤ), (0 : ℤ)) 1 + single ((0 : ℤ),
          (1 : ℤ)) 1)
    (hSKc : SK (heckeIndicator ℂ (diagPi ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) * localRepInf ϖ
        (algebraMap_ne_zero_of_irreducible K v hϖ))
        (finite_image_integralSubgroup_mul_singleton hϖ _)) = single ((1 : ℤ), (1 : ℤ)) 1)
    (SL : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hSL : ∀ (f : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ)
        (a b : ℤ),
      (SL f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) (w.1.adicCompletion L) ⧸
          integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L),
        Set.indicator
          {c : GL (Fin 2) (w.1.adicCompletion L) ⧸
              integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) |
            ∃ g : GL (Fin 2) (w.1.adicCompletion L), QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 =
                algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)
                  ((InertTransport.iota K L v w).toBase ϖ) ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1 =
                algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)
                  ((InertTransport.iota K L v w).toBase ϖ) ^ b}
          (fun c => (f : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (Quotient.out c)) c)
    (hST : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ))) (finite_image_integralSubgroup_mul_singleton
        (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
      (Nat.card ((w.1.adicCompletionIntegers L) ⧸ Ideal.span {((InertTransport.iota K L v w).toBase ϖ)}) : ℂ) • single
          ((1 : ℤ), (0 : ℤ)) 1 + single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : SL (heckeIndicator ℂ (diagPi ((InertTransport.iota K L v w).toBase ϖ) (algebraMap_ne_zero_of_irreducible L
        w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ)) * localRepInf ((InertTransport.iota K L v w).toBase
        ϖ) (algebraMap_ne_zero_of_irreducible L w.1 (InertTransport.irreducible_iota_toBase K L v w hw hϖ)))
        (finite_image_integralSubgroup_mul_singleton (InertTransport.irreducible_iota_toBase K L v w hw hϖ) _)) =
            single ((1 : ℤ), (1 : ℤ)) 1)
    (b : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ] HeckeAlgebra
        (integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (hcomp : SK.comp b = (mapDomainAlgHom ℂ ℂ (Module.finrank K L • AddMonoidHom.id (ℤ × ℤ))).comp SL)
    (φ : HeckeAlgebra (integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ) :
    AreMatchingLocal K L v σ
      (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
          (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g))
      (b φ : GL (Fin 2) (v.adicCompletion K) → ℂ) := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  have hσn : σ ^ Module.finrank K L = 1 := InertTransport.pow_finrank_eq_one K L σ
  have hfun : (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
      (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g)) =
      fun y => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e y) := rfl
  rw [hfun]
  refine ⟨?_, ?_⟩
  · intro δ hδ γ hrs y hy τ τ' hτ hτ' hcy I I' hI' hI

    obtain ⟨τ₁, hτ₁, hc₁, htrans⟩ := exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate K L (v.adicCompletion
        K) σ
      (semiLocalHaar K L v) (map_mul_left_semiLocalHaar K L v) γ δ y τ τ' hτ' hcy
    have hN₁ : IsNormConjugator K L (v.adicCompletion K) σ γ (y⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ y) 1 :=
      CoupledTransport.isNormConjugator_one_of_isNormConjugator (σ := σ) (sigmaTensor_iterate_finrank K L σ v w hdeg e)
        hy
    have hδ₁ := isRegularSemisimple_normString_of_isNormConjugator_one K L σ v γ hrs _ hN₁
    obtain ⟨J, hJ⟩ := exists_isTwistedOrbitalIntegralOn K L v σ _ hδ₁ τ₁ hτ₁
      (φ := fun z => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e z))
      (twisted_hecke_bi_invariant K L v w φ e) (twisted_hecke_finite_support K L v w φ e)
    have hIJ : I' = J :=
      IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (v.adicCompletion K) σ hσn
        (semiLocalHaar K L v) (isHaarMeasure_semiLocalHaar K L v) δ hδ τ' hτ'
        (fun z => (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (glEquiv K L v w e z))
        (twisted_hecke_measurable K L v w φ e) (twisted_hecke_bounded K L v w φ e) hI' (htrans _ _ hJ)
    rw [hIJ]
    by_cases hsq : IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    ·
      exact split_eq_of_isNormConjugator_one K L σ v w hdeg hσ1 hσn e hw ϖ hϖ hres γ hsq hrs _ hN₁ SK hSKT hSKc hSK SL
          hST hSc
        hSL b hcomp τ hτ τ₁ hτ₁ hc₁ φ hJ hI
    · have hγ := ((QuadraticIrreducibility.irreducible_charpoly_iff K v γ).2 hsq)
      exact twistedOrbitalIntegral_eq_orbitalIntegral_of_isNormConjugator_one K L σ v w hdeg hσ1 hσn e hw ϖ hϖ hres γ
          hγ
        hrs _ hN₁ SK hSKT hSKc SL hST hSc b hcomp τ hτ τ₁ hτ₁ hc₁ φ hJ hI
  · intro γ hrs hnn τ hτ I hI
    by_cases hsq : IsSquare (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
        4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    ·
      exact split_eq_zero_of_not_isNormOf K L σ v w hdeg hσ1 hσn e hw ϖ hϖ hres γ hsq hrs SK hSKT hSKc hSK SL hST hSc
        b hcomp τ hτ hnn φ hI
    ·
      have hγ := ((QuadraticIrreducibility.irreducible_charpoly_iff K v γ).2 hsq)
      exact nonNorm_eq_zero_of_not_isNormOf K L σ v w hdeg hσ1 hσn e hw ϖ hϖ hres γ hγ hrs SK hSKT hSKc SL hST hSc b
        hcomp τ hτ hnn φ hI

end Matching

end InertBaseChange

open NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct

open scoped TensorProduct.RightActions in

private theorem InertBaseChange.exists_baseChangeHom_apply
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (ϖK : v.adicCompletionIntegers K)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (ϖL : w.1.adicCompletionIntegers L) (hϖL : Irreducible ϖL)
    (hϖL0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL ≠ 0)
    [Finite (v.adicCompletionIntegers K ⧸ Ideal.span {ϖK})] [Finite (w.1.adicCompletionIntegers L ⧸ Ideal.span {ϖL})]
    (hfinK : (QuotientGroup.mk '' (((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
        Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) * {LocalGL2.diagPi ϖK hϖK0
        * LocalGL2.localRepInf ϖK hϖK0}) : Set (GL (Fin 2) (v.adicCompletion K) ⧸ LocalGL2.integralSubgroup
        (v.adicCompletionIntegers K) (v.adicCompletion K))).Finite)
    (hfinL : (QuotientGroup.mk '' (((LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) :
        Subgroup (GL (Fin 2) (w.1.adicCompletion L))) : Set (GL (Fin 2) (w.1.adicCompletion L))) * {LocalGL2.diagPi ϖL
        hϖL0 * LocalGL2.localRepInf ϖL hϖL0}) : Set (GL (Fin 2) (w.1.adicCompletion L) ⧸ LocalGL2.integralSubgroup
        (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))).Finite)
    (EK : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (hEK : (EK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) •
        ({x : GL (Fin 2) (v.adicCompletion K) | ∃ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K)
            (v.adicCompletion K),
            (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
              algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
                (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}.indicator fun _ => (1 : ℂ)))
    (TL EL : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
        ℂ)
    (hTL : (TL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (HeckePair.doubleCoset (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
          (LocalGL2.diagPi ϖL hϖL0)).indicator fun _ => (1 : ℂ))
    (hEL : (EL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (Ideal.absNorm w.1.asIdeal : ℂ) •
        ({x : GL (Fin 2) (w.1.adicCompletion L) | ∃ u ∈ LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L)
            (w.1.adicCompletion L),
            (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
              algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL •
                (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))}.indicator fun _ => (1 : ℂ)))
    (p : ℕ → HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) :
    ∃ b : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ
        →ₐ[ℂ] HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ,
      b TL = p (Module.finrank K L) ∧ b EL = EK ^ Module.finrank K L ∧
      b (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖL hϖL0 * LocalGL2.localRepInf ϖL hϖL0) hfinL) =
          (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖK hϖK0 * LocalGL2.localRepInf ϖK hϖK0) hfinK) ^ Module.finrank
          K L ∧ EK = (Ideal.absNorm v.asIdeal : ℂ) • HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖK hϖK0 *
          LocalGL2.localRepInf ϖK hϖK0) hfinK := by
  classical

  letI : CommRing (HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      ℂ) :=
    { toRing := inferInstance, mul_comm := LocalGL2.localHeckeMul_comm }
  set cK := HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖK hϖK0 * LocalGL2.localRepInf ϖK hϖK0) hfinK with hcK
  set cL := HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖL hϖL0 * LocalGL2.localRepInf ϖL hϖL0) hfinL with hcL

  have hTL' : TL = HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖL hϖL0)
      (LocalGL2.finite_image_mul_diagPi ϖL hϖL0 hϖL) := Subtype.ext hTL
  have hEK' : EK = (Ideal.absNorm v.asIdeal : ℂ) • cK := by
    apply Subtype.ext
    rw [hEK, hcK]
    show _ = (Ideal.absNorm v.asIdeal : ℂ) • Set.indicator _ 1
    rw [InertBaseChange.doubleCoset_central_eq]
    rfl
  have hEL' : EL = (Ideal.absNorm w.1.asIdeal : ℂ) • cL := by
    apply Subtype.ext
    rw [hEL, hcL]
    show _ = (Ideal.absNorm w.1.asIdeal : ℂ) • Set.indicator _ 1
    rw [InertBaseChange.doubleCoset_central_eq]
    rfl

  have hNv : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hNw : (Ideal.absNorm w.1.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr w.1.ne_bot)
  have hcKu : IsUnit cK := (LocalGL2.heckeIndicator_diagPi_mul_localRepInf_central_isUnit ϖK hϖK0 hfinK).2
  have hEKu : IsUnit EK := by
    rw [hEK', Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hNv).map _).mul hcKu
  have hu : IsUnit ((Ideal.absNorm w.1.asIdeal : ℂ)⁻¹ • EK ^ Module.finrank K L) := by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hNw)).map _).mul (hEKu.pow _)
  obtain ⟨b, hbT, hbC⟩ := (LocalGL2.existsUnique_algHom_heckeIndicator_eq ϖL hϖL0 hϖL hfinL (R₀ := ℂ)
    (A := HeckePair.HeckeAlgebra
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ)
    (p (Module.finrank K L)) hu.unit).exists
  have hNvw : (Ideal.absNorm v.asIdeal : ℂ) ^ Module.finrank K L = Ideal.absNorm w.1.asIdeal := by
    rw [InertBaseChange.absNorm_eq_pow K L v w hw e, Nat.cast_pow]
  have hsm := map_smul b (Ideal.absNorm w.1.asIdeal : ℂ) cL
  refine ⟨b, ?_, ?_, ?_, hEK'⟩
  · rw [hTL', hbT]
  · rw [hEL', hsm, hcL, hbC, IsUnit.unit_spec, smul_smul, mul_inv_cancel₀ hNw, one_smul]
  · rw [hbC, IsUnit.unit_spec, hEK', smul_pow, smul_smul, hNvw, inv_mul_cancel₀ hNw, one_smul]

set_option maxHeartbeats 1600000 in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (ϖL : w.1.adicCompletionIntegers L) (hϖL : Irreducible ϖL)
    (hϖL0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL ≠ 0)
    (UK : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hUK : UK = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
    (UL : Subgroup (GL (Fin 2) (w.1.adicCompletion L)))
    (hUL : UL = LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
    (TK EK : HeckePair.HeckeAlgebra UK ℂ)
    (hTK : (TK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (HeckePair.doubleCoset UK (LocalGL2.diagPi ϖK hϖK0)).indicator fun _ => (1 : ℂ))
    (hEK : (EK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) •
        ({x : GL (Fin 2) (v.adicCompletion K) | ∃ u ∈ UK,
            (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
              algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
                (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}.indicator fun _ => (1 : ℂ)))
    (TL EL : HeckePair.HeckeAlgebra UL ℂ)
    (hTL : (TL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (HeckePair.doubleCoset UL (LocalGL2.diagPi ϖL hϖL0)).indicator fun _ => (1 : ℂ))
    (hEL : (EL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
      (Ideal.absNorm w.1.asIdeal : ℂ) •
        ({x : GL (Fin 2) (w.1.adicCompletion L) | ∃ u ∈ UL,
            (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
              algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL •
                (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))}.indicator fun _ => (1 : ℂ)))
    (p : ℕ → HeckePair.HeckeAlgebra UK ℂ) (hp0 : p 0 = 2) (hp1 : p 1 = TK)
    (hp : ∀ k : ℕ, p (k + 2) = TK * p (k + 1) - EK * p k) :
    ∃ b : HeckePair.HeckeAlgebra UL ℂ →ₐ[ℂ] HeckePair.HeckeAlgebra UK ℂ,
      b TL = p (Module.finrank K L) ∧ b EL = EK ^ Module.finrank K L ∧
      ∀ φ : HeckePair.HeckeAlgebra UL ℂ,
        AreMatchingLocal K L v σ
          (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
              (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g))
          (b φ : GL (Fin 2) (v.adicCompletion K) → ℂ) := by
  classical
  subst hUK
  subst hUL
  haveI := InertBaseChange.finite_quotient_span K v ϖK hϖK
  haveI := InertBaseChange.finite_quotient_span L w.1 ϖL hϖL

  have hfinK := InertBaseChange.finite_image_mul_central ϖK hϖK0
    (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
  have hfinL := InertBaseChange.finite_image_mul_central ϖL hϖL0
    (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))

  have hB := InertBaseChange.exists_baseChangeHom_apply K L v w hw e ϖK hϖK0 ϖL hϖL hϖL0 hfinK hfinL EK hEK TL EL hTL
    hEL p
  obtain ⟨b, hb₁, hb₂, hbc', hEK'⟩ := hB
  set cK := HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖK hϖK0 * LocalGL2.localRepInf ϖK hϖK0) hfinK
    with hcK
  set cL := HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖL hϖL0 * LocalGL2.localRepInf ϖL hϖL0) hfinL
    with hcL
  have hTL' : TL = HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖL hϖL0)
      (LocalGL2.finite_image_mul_diagPi ϖL hϖL0 hϖL) := Subtype.ext hTL

  have hSK' := InertBaseChange.exists_constantTermHom K v ϖK hϖK0 hϖK hfinK
  obtain ⟨SK, hSK, hSKT, hSKc⟩ := hSK'
  have hSL' := InertBaseChange.exists_constantTermHom L w.1 ϖL hϖL0 hϖL hfinL
  obtain ⟨SL, hSL, hSLT, hSLc⟩ := hSL'
  have hqK : (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {ϖK}) : ℂ) = Ideal.absNorm v.asIdeal := by
    rw [InertBaseChange.natCard_quot_span_eq_absNorm v ϖK hϖK]
  have hqL : (Nat.card (w.1.adicCompletionIntegers L ⧸ Ideal.span {ϖL}) : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ Module.finrank K L := by
    rw [InertBaseChange.natCard_quot_span_eq_absNorm w.1 ϖL hϖL, InertBaseChange.absNorm_eq_pow K L v w hw e,
      Nat.cast_pow]
  have hcLu : IsUnit cL := (LocalGL2.heckeIndicator_diagPi_mul_localRepInf_central_isUnit ϖL hϖL0 hfinL).2
  have huniq : ∀ χ₁ χ₂ : HeckePair.HeckeAlgebra
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ), χ₁ TL = χ₂ TL → χ₁ cL = χ₂ cL → χ₁ = χ₂ := by
    intro χ₁ χ₂ hT hc
    rw [hTL'] at hT
    exact InertBaseChange.algHom_eq_of_existsUnique _ cL
      (LocalGL2.existsUnique_algHom_heckeIndicator_eq ϖL hϖL0 hϖL hfinL (R₀ := ℂ)) hcLu χ₁ χ₂ hT hc

  have hTK' : TK = HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖK hϖK0)
      (LocalGL2.finite_image_mul_diagPi ϖK hϖK0 hϖK) := Subtype.ext hTK
  have hSLT' : SL TL = AddMonoidAlgebra.single (1, 0) ((Ideal.absNorm v.asIdeal : ℂ) ^ Module.finrank K L) +
      AddMonoidAlgebra.single (0, 1) 1 := by
    rw [hTL', hSLT, hqL]
  have hSKT' : SK TK = AddMonoidAlgebra.single (1, 0) (Ideal.absNorm v.asIdeal : ℂ) +
      AddMonoidAlgebra.single (0, 1) 1 := by
    rw [hTK', hSKT, hqK]
  have hcomp := InertBaseChange.constantTerm_comp_eq_of_rec SL SK b TL cL TK cK EK (Ideal.absNorm v.asIdeal : ℂ)
    ((Ideal.absNorm v.asIdeal : ℂ) ^ Module.finrank K L) (Module.finrank K L) rfl hSLT' hSLc hSKT' hSKc hEK' p hp0 hp1
    hp hb₁ hbc' huniq
  refine ⟨b, hb₁, hb₂, ?_⟩
  ·
    intro φ
    haveI := InertBaseChange.finite_quot_iota_toBase K L v w hw hϖK
    obtain ⟨hSK₂, hSKT₂, hSKc₂⟩ :=
      InertBaseChange.constantTerm_transfer_of_irreducible K v ϖK ϖK hϖK hϖK SK hSK hSKT hSKc
    obtain ⟨hSL₂, hSLT₂, hSLc₂⟩ :=
      InertBaseChange.constantTerm_transfer_of_irreducible L w.1 ϖL ((InertTransport.iota K L v
          w).toBase ϖK)
        hϖL (InertTransport.irreducible_iota_toBase K L v w hw hϖK) SL hSL hSLT hSLc
    exact InertBaseChange.areMatchingLocal_comp K L σ v w hdeg hσ e hw ϖK hϖK
      (InertBaseChange.natCard_quot_iota_eq_pow K L v w hw e hϖK) SK hSK₂ hSKT₂ hSKc₂ SL hSL₂ hSLT₂ hSLc₂ b hcomp φ

end S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime (solution)
