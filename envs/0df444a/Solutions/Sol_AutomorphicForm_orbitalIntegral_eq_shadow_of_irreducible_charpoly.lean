-- Prove2me | solution 1 for AutomorphicForm.orbitalIntegral_eq_shadow_of_irreducible_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1491d08a-e7c1-55fb-a908-c173cedcb2cd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetLocal
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
import Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
import Theorems.Thm_LT_LatticeTree_card_orbitalBall_sdiff_of_act_swap_of_isWithin_one
import Theorems.Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton
import Theorems.Thm_LocalGL2_exists_basis_heckeIndicator_zpow
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Mathlib.Algebra.Module.Lattice
import Theorems.Thm_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly

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

end SatakeValues

open NumberField IsDedekindDomain AutomorphicForm
open scoped ENNReal

namespace TorusIndices

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

private theorem _root_.TorusIndices.act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g v) = v := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

p2m_export "TorusIndices" "act_inv_act"
private theorem act_act_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g (Vertex.act g⁻¹ v) = v := by
  rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

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
  ext
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

end Local

end TorusIndices

namespace TwistedTreeTransport

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private theorem _root_.TwistedTreeTransport.act_inv_act (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act g⁻¹ (Vertex.act g v) = v := by
  rw [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

p2m_export "TwistedTreeTransport" "act_inv_act"
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

end NormScalars

section ScalarPowers

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq"

variable {K : Type*} [Field K]

end ScalarPowers

section Transport

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq LT.TwistedNorm"

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {RE : Type*} [CommRing RE] {E : Type*} [Field E] [Algebra RE E]
variable (ι : IntegralHom R K RE E) (σ : IntegralAut RE E)

end Transport

section TwistedPlace

p2m_open "LT.LatticeTree~exists_act_stdVertex_eq LT.TwistedNorm"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

end TwistedPlace

end FixedOrInversion

namespace InertBaseChange

open NumberField IsDedekindDomain HeckePair LocalGL2 AutomorphicForm
open scoped Pointwise

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

end IntegralCarrier

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

p2m_open "LocalGL2 LT.LatticeTree~exists_act_stdVertex_eq P2MW.S_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly.TwistedTreeTransport"

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
  obtain ⟨bs, hbs⟩ := exists_basis_heckeIndicator_zpow ϖ (algebraMap_ne_zero_of_irreducible K v hϖ) hϖ
    (R₀ := ℂ) (finite_image_integralSubgroup_mul_singleton hϖ)
  refine (orbitalIntegral_eq_of_basis K v γ hrs τ hτ
    ((((TorusIndices.unitCentralizer K v γ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
        (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : ℂ) *
      ((τ ((TorusIndices.unitCentralizer K v γ).subgroupOf
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) :
        Set (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ))⁻¹ •
      (shadowLinear D (unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ)).comp S.toLinearMap) bs
    (fun p I₃ hI₃ => ?_) f hI).trans ?_
  · have h := orbitalIntegral_heckeIndicator_eq_shadow K v ϖ hϖ γ hγ hrs u D hdet S hST hSc τ hτ p.1.1 p.1.2 p.2
      (I := I₃) (by rw [hbs p] at hI₃; exact hI₃)
    rw [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, shadowLinear_apply, smul_eq_mul, hbs p]
    exact h
  · rw [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, shadowLinear_apply, smul_eq_mul]

end LinearExtension

end InertBaseChange

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Pointwise
open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    [Finite ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ})]
    (hfin : ∀ g : GL (Fin 2) (v.adicCompletion K),
      (QuotientGroup.mk '' ((LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) : Set (GL (Fin
          2) (v.adicCompletion K))) * {g}) :
        Set (GL (Fin 2) (v.adicCompletion K) ⧸ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion
            K))).Finite)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    (u : (v.adicCompletionIntegers K)ˣ) (D : ℤ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u * algebraMap (v.adicCompletionIntegers K)
          (v.adicCompletion K) ϖ ^ D)
    (S : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ →ₐ[ℂ]
        AddMonoidAlgebra ℂ (ℤ × ℤ))
    (hST : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ hϖ0) (hfin _)) =
      (Nat.card ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ}) : ℂ) • AddMonoidAlgebra.single ((1 : ℤ), (0 : ℤ)) 1 +
        AddMonoidAlgebra.single ((0 : ℤ), (1 : ℤ)) 1)
    (hSc : S (HeckePair.heckeIndicator ℂ (LocalGL2.diagPi ϖ hϖ0 * LocalGL2.localRepInf ϖ hϖ0) (hfin _)) =
      AddMonoidAlgebra.single ((1 : ℤ), (1 : ℤ)) 1)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
        (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ)
    (hC : (LT.LatticeTree.fixedVertexSet (R := v.adicCompletionIntegers K) γ).Finite)
    (hTZ : ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range) ⊔
          Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex (Subgroup.centralizer ({γ} : Set (GL (Fin 2)
              (v.adicCompletion K)))) ≠ 0)
    (hm : (τ (((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range)).subgroupOf
            (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : Set (Subgroup.centralizer ({γ} : Set
                (GL (Fin 2) (v.adicCompletion K)))))).toReal ≠ 0)
    (f : HeckePair.HeckeAlgebra (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ℂ) (I :
        ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ
      (f : GL (Fin 2) (v.adicCompletion K) → ℂ) I) :
    I = ((((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range) ⊔
              Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex (Subgroup.centralizer ({γ} : Set (GL (Fin 2)
                  (v.adicCompletion K)))) : ℂ) *
          ((τ (((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ⊓
            Subgroup.comap (Matrix.GeneralLinearGroup.det : GL (Fin 2) (v.adicCompletion K) →* (v.adicCompletion K)ˣ)
              (Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).toMonoidHom).range)).subgroupOf
              (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) : Set (Subgroup.centralizer ({γ} :
                  Set (GL (Fin 2) (v.adicCompletion K)))))).toReal : ℂ))⁻¹ *
      ((if Even D then (LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ : ℂ) * (S f).coeff (D / 2, D /
          2) else 0) +
        2 * (S f).coeff.sum fun (x : ℤ × ℤ) (r : ℂ) => if x.1 < x.2 ∧ x.1 + x.2 = D then r else 0) := by
  have _ := hC
  have _ := hTZ
  have _ := hm
  have hsq := (QuadraticIrreducibility.irreducible_charpoly_iff K v γ).1 hγ
  have hrs : AutomorphicForm.IsRegularSemisimple γ :=
    (AutomorphicForm.isRegularSemisimple_iff γ).2
      (isUnit_iff_ne_zero.mpr fun h0 => hsq (by rw [h0]; exact IsSquare.zero))
  exact InertBaseChange.orbitalIntegral_eq_shadow K v ϖ hϖ γ hγ hrs u D hdet S hST hSc τ hτ f hI

end S_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly
end P2MW
export P2MW.S_AutomorphicForm_orbitalIntegral_eq_shadow_of_irreducible_charpoly (solution)
