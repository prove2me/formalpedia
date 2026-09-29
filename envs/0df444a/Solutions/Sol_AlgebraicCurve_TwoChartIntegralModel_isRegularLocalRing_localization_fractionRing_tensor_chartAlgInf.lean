-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/163e5139-3343-531f-a97d-307294bac53f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf

set_option autoImplicit false

universe u

open scoped TensorProduct
open Polynomial

namespace R1

section FieldLevel

variable (K₀ F : Type u) [Field K₀] [Field F] [Algebra K₀ F] (j : F)

private abbrev A0 : Subalgebra K₀ F := Algebra.adjoin K₀ ({j} : Set F)

private abbrev Kj : IntermediateField K₀ F := IntermediateField.adjoin K₀ ({j} : Set F)

private theorem A0_le_Kj : A0 K₀ F j ≤ (Kj K₀ F j).toSubalgebra := IntermediateField.algebra_adjoin_le_adjoin K₀ _

noncomputable scoped instance algA0Kj : Algebra ↥(A0 K₀ F j) ↥(Kj K₀ F j) :=
  (Subalgebra.inclusion (A0_le_Kj K₀ F j)).toRingHom.toAlgebra

private theorem algebraMap_A0_Kj (x : ↥(A0 K₀ F j)) : ((algebraMap ↥(A0 K₀ F j) ↥(Kj K₀ F j) x : ↥(Kj K₀ F j)) : F) = (x : F) := rfl

scoped instance towerA0KjF : IsScalarTower ↥(A0 K₀ F j) ↥(Kj K₀ F j) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance towerK0A0Kj : IsScalarTower K₀ ↥(A0 K₀ F j) ↥(Kj K₀ F j) :=
  IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)

scoped instance isFractionRing_A0_Kj : IsFractionRing ↥(A0 K₀ F j) ↥(Kj K₀ F j) := by
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · refine isUnit_iff_ne_zero.mpr (fun h => nonZeroDivisors.ne_zero y.2 (Subtype.ext ?_))
    exact congrArg (fun t : ↥(Kj K₀ F j) => (t : F)) h
  · obtain ⟨r, hr, s, hs, hz⟩ := IntermediateField.mem_adjoin_iff_div.mp z.2
    by_cases hs0 : s = 0
    · refine ⟨(0, 1), ?_⟩
      have hz0 : z = 0 := Subtype.ext (by rw [hz, hs0, div_zero]; rfl)
      simp [hz0]
    · refine ⟨(⟨r, hr⟩, ⟨⟨s, hs⟩, mem_nonZeroDivisors_of_ne_zero (fun h => hs0 (congrArg Subtype.val h))⟩), Subtype.ext ?_⟩
      show (z : F) * s = r
      rw [hz, div_mul_cancel₀ _ hs0]
  · rw [OneMemClass.coe_one, one_mul, one_mul]
    exact Subtype.ext (congrArg (fun t : ↥(Kj K₀ F j) => (t : F)) h)

end FieldLevel

end R1

namespace R1

section Dedekind

variable (K₀ F : Type u) [Field K₀] [Field F] [Algebra K₀ F] (j : F)

private theorem isPrincipalIdealRing_A0 (htj : Transcendental K₀ j) : IsPrincipalIdealRing ↥(A0 K₀ F j) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K₀ j htj).toRingEquiv.toRingHom
    (Polynomial.algEquivOfTranscendental K₀ j htj).surjective

private abbrev D : Subalgebra ↥(A0 K₀ F j) F := integralClosure ↥(A0 K₀ F j) F

private theorem isDedekindDomain_D (htj : Transcendental K₀ j)
    [FiniteDimensional ↥(Kj K₀ F j) F] [Algebra.IsSeparable ↥(Kj K₀ F j) F] :
    IsDedekindDomain ↥(D K₀ F j) := by
  haveI := isPrincipalIdealRing_A0 K₀ F j htj
  exact integralClosure.isDedekindDomain ↥(A0 K₀ F j) ↥(Kj K₀ F j) F

private def jD : ↥(D K₀ F j) := ⟨j, isIntegral_algebraMap (A := F) (x := (⟨j, Algebra.subset_adjoin rfl⟩ : ↥(A0 K₀ F j)))⟩

@[scoped simp] private theorem coe_jD : (jD K₀ F j : F) = j := rfl

private theorem not_isUnit_jD (htj : Transcendental K₀ j) : ¬ IsUnit (jD K₀ F j) := by
  haveI := isPrincipalIdealRing_A0 K₀ F j htj
  rintro ⟨u, hu⟩

  have hinvD : IsIntegral ↥(A0 K₀ F j) (j⁻¹ : F) := by
    have h1 : ((u⁻¹ : (↥(D K₀ F j))ˣ) : ↥(D K₀ F j)) * jD K₀ F j = 1 := by rw [← hu, Units.inv_mul]
    have h2 : (((u⁻¹ : (↥(D K₀ F j))ˣ) : ↥(D K₀ F j)) : F) = j⁻¹ := by
      have := congrArg (fun t : ↥(D K₀ F j) => (t : F)) h1
      simp only [Subalgebra.coe_mul, coe_jD, OneMemClass.coe_one] at this
      exact eq_inv_of_mul_eq_one_left this
    rw [← h2]; exact ((u⁻¹ : (↥(D K₀ F j))ˣ) : ↥(D K₀ F j)).2

  have hinvK : (j⁻¹ : F) ∈ Kj K₀ F j := inv_mem (IntermediateField.subset_adjoin K₀ _ rfl)

  have hint : IsIntegral ↥(A0 K₀ F j) (⟨j⁻¹, hinvK⟩ : ↥(Kj K₀ F j)) :=
    IsIntegral.tower_bot (A := ↥(Kj K₀ F j)) (B := F) (algebraMap ↥(Kj K₀ F j) F).injective hinvD
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hyF : (y : F) = j⁻¹ := by
    have := congrArg (fun t : ↥(Kj K₀ F j) => (t : F)) hy
    simpa [algebraMap_A0_Kj] using this

  obtain ⟨q, hq⟩ : ∃ q : K₀[X], aeval j q = (y : F) := by
    have hy2 : (y : F) ∈ (aeval (R := K₀) j).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact y.2
    exact hy2
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact htj ⟨X, X_ne_zero, by simp⟩
  apply htj
  refine ⟨X * q - 1, fun h => ?_, ?_⟩
  · have := congrArg (fun r : K₀[X] => r.coeff 0) h
    simp at this
  · rw [map_sub, map_mul, aeval_X, hq, hyF, mul_inv_cancel₀ hj0, map_one, sub_self]

end Dedekind

end R1
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.R1"

namespace R1

section Local

variable (K₀ F : Type u) [Field K₀] [Field F] [Algebra K₀ F] (j : F)

private theorem local_of_ringEquiv {T S : Type u} [CommRing T] [CommRing S] [IsDomain S] [IsDedekindDomain S] (e : T ≃+* S)
    (m : Ideal T) [m.IsMaximal] (hm : Ideal.map e m ≠ ⊥) :
    IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞) := by
  set n : Ideal S := Ideal.map e m with hndef
  haveI : n.IsMaximal := Ideal.map_isMaximal_of_equiv e
  haveI : IsDiscreteValuationRing (Localization.AtPrime n) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hm _
  have H : Submonoid.map e.toMonoidHom m.primeCompl = n.primeCompl := by
    have hn : ∀ y : T, e y ∈ n ↔ y ∈ m := fun y => by
      rw [hndef, ← Ideal.comap_symm, Ideal.mem_comap, RingEquiv.symm_apply_apply]
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact fun hx => hy ((hn y).mp hx)
    · intro hx
      refine ⟨e.symm x, fun h => hx ?_, e.apply_symm_apply x⟩
      rw [← e.apply_symm_apply x]
      exact (hn _).mpr h
  let L : Localization.AtPrime m ≃+* Localization.AtPrime n :=
    IsLocalization.ringEquivOfRingEquiv (M := m.primeCompl) (T := n.primeCompl) (Localization.AtPrime m) (Localization.AtPrime n) e H
  exact ⟨IsRegularLocalRing.of_ringEquiv L.symm, by
    rw [ringKrullDim_eq_of_ringEquiv L, IsDiscreteValuationRing.ringKrullDim_eq_one]; rfl⟩

end Local
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.R1"

end R1
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.R1"

namespace R1

section BaseLevel

variable (R : Type u) [CommRing R] (K₀ : Type u) [Field K₀] [Algebra R K₀]
  (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (j : F)

private abbrev AR : Subalgebra R F := Algebra.adjoin R ({j} : Set F)

private noncomputable def inclARA0 : ↥(AR R F j) →+* ↥(A0 K₀ F j) :=
  (Subalgebra.inclusion (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_adjoin_restrictScalars R F K₀ ({j} : Set F))).toRingHom

@[scoped simp] private theorem coe_inclARA0 (x : ↥(AR R F j)) : ((inclARA0 R K₀ F j x : ↥(A0 K₀ F j)) : F) = (x : F) :=
  Subalgebra.coe_inclusion _ x

noncomputable scoped instance algARA0 : Algebra ↥(AR R F j) ↥(A0 K₀ F j) := (inclARA0 R K₀ F j).toAlgebra

private theorem algebraMap_AR_A0_eq : algebraMap ↥(AR R F j) ↥(A0 K₀ F j) = inclARA0 R K₀ F j := RingHom.algebraMap_toAlgebra _

@[scoped simp] private theorem algebraMap_AR_A0 (x : ↥(AR R F j)) : ((algebraMap ↥(AR R F j) ↥(A0 K₀ F j) x : ↥(A0 K₀ F j)) : F) = (x : F) := by
  rw [algebraMap_AR_A0_eq, coe_inclARA0]

scoped instance towerARA0F : IsScalarTower ↥(AR R F j) ↥(A0 K₀ F j) F :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    simp only [Subalgebra.algebraMap_eq, RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, Subalgebra.coe_val,
      algebraMap_AR_A0])

private theorem algebraMap_R_A0 (r : R) : ((algebraMap R ↥(A0 K₀ F j) r : ↥(A0 K₀ F j)) : F) = algebraMap R F r := by
  rw [IsScalarTower.algebraMap_apply R K₀ ↥(A0 K₀ F j), Subalgebra.coe_algebraMap, ← IsScalarTower.algebraMap_apply]

private theorem algebraMap_R_AR (r : R) : ((algebraMap R ↥(AR R F j) r : ↥(AR R F j)) : F) = algebraMap R F r :=
  Subalgebra.coe_algebraMap _ r

scoped instance towerRARA0 : IsScalarTower R ↥(AR R F j) ↥(A0 K₀ F j) :=
  IsScalarTower.of_algebraMap_eq (fun r => Subtype.ext (by rw [algebraMap_AR_A0, algebraMap_R_A0, algebraMap_R_AR]))

private abbrev MR : Submonoid ↥(AR R F j) := Algebra.algebraMapSubmonoid ↥(AR R F j) (nonZeroDivisors R)

variable [IsDomain R] [IsFractionRing R K₀]

scoped instance isLocalization_AR_A0 : IsLocalization (MR R F j) ↥(A0 K₀ F j) := by
  refine ⟨?_, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
  · rintro ⟨_, s, hs, rfl⟩
    rw [← IsScalarTower.algebraMap_apply R ↥(AR R F j) ↥(A0 K₀ F j), IsScalarTower.algebraMap_apply R K₀ ↥(A0 K₀ F j)]
    exact (IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).map _
  ·
    obtain ⟨q, hq⟩ : ∃ q : K₀[X], aeval j q = (z : F) := by
      have hz : (z : F) ∈ (aeval (R := K₀) j).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact z.2
      exact hz
    obtain ⟨b, hbM, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
    refine ⟨(⟨aeval j (IsLocalization.integerNormalization (nonZeroDivisors R) q), Polynomial.aeval_mem_adjoin_singleton R j⟩,
      ⟨algebraMap R _ b, b, hbM, rfl⟩), Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, algebraMap_AR_A0, algebraMap_AR_A0, algebraMap_R_AR]
    show (z : F) * algebraMap R F b = aeval j (IsLocalization.integerNormalization (nonZeroDivisors R) q)
    rw [← Polynomial.aeval_map_algebraMap K₀, hmap, ← algebraMap_smul K₀ b q, map_smul, Algebra.smul_def, hq, mul_comm,
      ← IsScalarTower.algebraMap_apply]
  · rw [Submonoid.coe_one, one_mul, one_mul]
    exact Subtype.ext (by rw [← algebraMap_AR_A0 R K₀ F j x, ← algebraMap_AR_A0 R K₀ F j y, h])

end BaseLevel
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.R1"

end R1
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.R1"

namespace R1

section Tensor

variable (R : Type u) [CommRing R] (K₀ : Type u) [Field K₀] [Algebra R K₀]
  (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F] (j : F)

open AlgebraicCurve.TwoChartIntegralModel

private abbrev Afin : Subalgebra R F := chartAlgFin R F j

private abbrev T : Type u := K₀ ⊗[R] ↥(Afin R F j)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

include K₀ in
private theorem injective_algebraMap_R_F [IsFractionRing R K₀] : Function.Injective (algebraMap R F) := by
  rw [IsScalarTower.algebraMap_eq R K₀ F]
  exact (algebraMap K₀ F).injective.comp (IsFractionRing.injective R K₀)

private noncomputable def gT : T R K₀ F j →ₐ[R] F :=
  Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R K₀ F) (Afin R F j).val

private theorem gT_tmul (c : K₀) (a : ↥(Afin R F j)) : gT R K₀ F j (c ⊗ₜ a) = algebraMap K₀ F c * (a : F) :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ c a

private theorem gT_algebraMap (a : ↥(Afin R F j)) : gT R K₀ F j (algebraMap ↥(Afin R F j) (T R K₀ F j) a) = (a : F) := by
  rw [show algebraMap ↥(Afin R F j) (T R K₀ F j) a = (1 : K₀) ⊗ₜ a from rfl, gT_tmul, map_one, one_mul]

private abbrev MA : Submonoid ↥(Afin R F j) := Algebra.algebraMapSubmonoid ↥(Afin R F j) (nonZeroDivisors R)

variable [IsDomain R] [IsFractionRing R K₀]

include K₀ in
private theorem coe_MA_ne_zero (s : ↥(MA R F j)) : ((s : ↥(Afin R F j)) : F) ≠ 0 := by
  obtain ⟨_, r, hr, hs⟩ := s
  simp only [← hs, Subalgebra.coe_algebraMap]
  exact fun h => nonZeroDivisors.ne_zero hr ((injective_iff_map_eq_zero _).mp (injective_algebraMap_R_F R K₀ F) r h)

private theorem gT_mk' (a : ↥(Afin R F j)) (s : ↥(MA R F j)) :
    gT R K₀ F j (IsLocalization.mk' (T R K₀ F j) a s) = (a : F) / ((s : ↥(Afin R F j)) : F) := by
  rw [eq_div_iff (coe_MA_ne_zero R K₀ F j s), ← gT_algebraMap R K₀ F j (s : ↥(Afin R F j)), ← map_mul,
    IsLocalization.mk'_spec, gT_algebraMap]

private theorem gT_injective : Function.Injective (gT R K₀ F j) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective (MA R F j) t
  dsimp only at h
  subst h
  rw [gT_mk', div_eq_zero_iff] at ht
  have ha : a = 0 := Subtype.ext (ht.resolve_right (coe_MA_ne_zero R K₀ F j s))
  rw [ha, IsLocalization.mk'_zero]

private theorem gT_mem_D (t : T R K₀ F j) : gT R K₀ F j t ∈ D K₀ F j := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective (MA R F j) t
  dsimp only at h
  subst h
  rw [gT_mk', div_eq_mul_inv]
  refine IsIntegral.mul ?_ ?_
  · exact chartAlg_le_chartAlg R F K₀ ({j} : Set F) a.2
  · obtain ⟨_, r, hr, hs⟩ := s
    simp only [← hs, Subalgebra.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply R K₀ F, ← map_inv₀, IsScalarTower.algebraMap_apply K₀ ↥(A0 K₀ F j) F]
    exact isIntegral_algebraMap

private theorem exists_gT_eq {x : F} (hx : x ∈ D K₀ F j) : ∃ t : T R K₀ F j, gT R K₀ F j t = x := by
  obtain ⟨⟨_, r, hr, rfl⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (MR R F j) x hx
  rw [Submonoid.smul_def, Subalgebra.smul_def, smul_eq_mul, algebraMap_R_AR] at hint

  have hr0 : algebraMap R F r ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hr ((injective_iff_map_eq_zero _).mp (injective_algebraMap_R_F R K₀ F) r h)
  refine ⟨IsLocalization.mk' (T R K₀ F j) (⟨algebraMap R F r * x, hint⟩ : ↥(Afin R F j))
    (⟨algebraMap R ↥(Afin R F j) r, Algebra.mem_algebraMapSubmonoid_of_mem (⟨r, hr⟩ : ↥(nonZeroDivisors R))⟩ : ↥(MA R F j)), ?_⟩
  rw [gT_mk', Subalgebra.coe_algebraMap, mul_div_cancel_left₀ _ hr0]

private noncomputable def eTD : T R K₀ F j ≃+* ↥(D K₀ F j) :=
  RingEquiv.ofBijective ((gT R K₀ F j).toRingHom.codRestrict (D K₀ F j) (gT_mem_D R K₀ F j))
    ⟨fun x y h => gT_injective R K₀ F j (congrArg Subtype.val h), fun y => by
      obtain ⟨t, ht⟩ := exists_gT_eq R K₀ F j y.2
      exact ⟨t, Subtype.ext ht⟩⟩

private theorem coe_eTD (t : T R K₀ F j) : ((eTD R K₀ F j t : ↥(D K₀ F j)) : F) = gT R K₀ F j t := rfl

end Tensor
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.R1"

end R1
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf.R1"

open R1 in

private theorem R1.fin_aux
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (m : Ideal (K₀ ⊗[R] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))) [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) ∧
      ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞) := by
  haveI := hFD; haveI := hsep
  have htj' : Transcendental K₀ j := fun h => htj ((IsFractionRing.isAlgebraic_iff R K₀ F).mpr h)
  haveI : IsDedekindDomain ↥(R1.D K₀ F j) := R1.isDedekindDomain_D K₀ F j htj'
  refine R1.local_of_ringEquiv (R1.eTD R K₀ F j) m (fun hbot => ?_)
  have hm0 : m = ⊥ := (Ideal.map_eq_bot_iff_of_injective (R1.eTD R K₀ F j).injective).mp hbot

  apply R1.not_isUnit_jD K₀ F j htj'
  have hj0 : R1.jD K₀ F j ≠ 0 := fun h => (Fact.out : j ≠ 0) (congrArg Subtype.val h)
  have ht0 : (R1.eTD R K₀ F j).symm (R1.jD K₀ F j) ≠ 0 := fun h => hj0 (by simpa using h)
  have hunit : IsUnit ((R1.eTD R K₀ F j).symm (R1.jD K₀ F j)) := by
    by_contra hnu
    have hne : Ideal.span {(R1.eTD R K₀ F j).symm (R1.jD K₀ F j)} ≠ ⊤ := fun h => hnu (Ideal.span_singleton_eq_top.mp h)
    haveI hbm : (⊥ : Ideal (K₀ ⊗[R] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))).IsMaximal := hm0 ▸ inferInstance
    exact ht0 (Ideal.span_singleton_eq_bot.mp (hbm.eq_of_le hne bot_le).symm)
  simpa using hunit.map (R1.eTD R K₀ F j)

open R1 in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (m : Ideal (K₀ ⊗[R] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j))) [m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) ∧
      ringKrullDim (Localization.AtPrime m) = (1 : ℕ∞) := by
  haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero Fact.out⟩
  have htj' : Transcendental R j⁻¹ := fun h => htj (IsAlgebraic.inv_iff.mp h)
  have hK : IntermediateField.adjoin K₀ ({j⁻¹} : Set F) = IntermediateField.adjoin K₀ ({j} : Set F) := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr (inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self K₀ j⁻¹)
      rwa [inv_inv] at h
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hK]; exact hFD
  have hsep' : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j⁻¹} : Set F)) F := by rw [hK]; exact hsep
  exact R1.fin_aux R K₀ F j⁻¹ htj' hFD' hsep' m

end S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgInf (solution)
