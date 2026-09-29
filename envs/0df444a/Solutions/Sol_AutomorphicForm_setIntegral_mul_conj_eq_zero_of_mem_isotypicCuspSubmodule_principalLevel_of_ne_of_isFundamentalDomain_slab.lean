-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d04aa1ca-0291-50fa-8c80-44c20f5e2975

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

section NeBot

open NumberField IsDedekindDomain

namespace S14EigenPerp

private theorem _root_.S14EigenPerp.exists_notMem_finset (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "S14EigenPerp" "exists_notMem_finset"

theorem ne_bot_of_forall_dvd_mem (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨w, hw⟩ := exists_notMem_finset K S
  exact hw (hN w ⟨⊥, by rw [Ideal.mul_bot]⟩)

end S14EigenPerp

end NeBot

section Standardness

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel

namespace StdL

variable (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

private def piScalar (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    GL (Fin 2) (v.adicCompletion L) :=
  ⟨Matrix.diagonal fun _ => algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ,
    Matrix.diagonal fun _ => (algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [mul_inv_cancel₀ hϖ0, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal]; simp only [inv_mul_cancel₀ hϖ0, Matrix.diagonal_one]⟩

private def piUnit (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (v.adicCompletion L)ˣ :=
  Units.mk0 _ hϖ0

private theorem weyl_diagPi_weyl_diagPi (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (weylR : GL (Fin 2) (v.adicCompletion L)) * diagPi ϖ hϖ0 * weylR * diagPi ϖ hϖ0
      = piScalar L v ϖ hϖ0 := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagPi]
  show !![(0 : v.adicCompletion L), 1; 1, 0]
        * !![algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ, 0; 0, 1]
        * !![(0 : v.adicCompletion L), 1; 1, 0]
        * !![algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ, 0; 0, 1]
      = Matrix.diagonal fun _ => algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem diagPi_inv_eq (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    (diagPi ϖ hϖ0)⁻¹
      = (piScalar L v ϖ hϖ0)⁻¹ * (weylR : GL (Fin 2) (v.adicCompletion L)) * diagPi ϖ hϖ0
          * weylR := by
  rw [← weyl_diagPi_weyl_diagPi L v ϖ hϖ0]
  group

private theorem finEmbed_localEmbed_piScalar (ϖ : v.adicCompletionIntegers L)
    (hϖ0 : algebraMap (v.adicCompletionIntegers L) (v.adicCompletion L) ϖ ≠ 0) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v (piScalar L v ϖ hϖ0))
      = centralScalar (𝓞 L) L
          (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0))) := by
  apply Units.ext
  rw [coe_finEmbed, coe_localEmbed]
  show finMat (𝓞 L) L (localMat (𝓞 L) L v (piScalar L v ϖ hϖ0 : Matrix (Fin 2) (Fin 2) _))
      = Matrix.scalar (Fin 2)
          (((Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0)) :
              (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L))
  rw [Matrix.scalar_apply, Units.coe_map]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 L) L ?_ ?_
  · rw [mapMatrix_arch_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
    simp only [adeleArch_apply, finIncl_apply_fst, Matrix.diagonal_one]
  · rw [mapMatrix_fin_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
    simp only [adeleFin_apply, finIncl_apply_snd]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
      show Matrix.diagonal (fun _ => algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) ϖ)
          = Matrix.diagonal fun _ => finAdeleEval (𝓞 L) L w
              ((localUnit (𝓞 L) L w (piUnit L w ϖ hϖ0) : (FiniteAdeleRing (𝓞 L) L)ˣ) :
                FiniteAdeleRing (𝓞 L) L)
      rw [finAdeleEval_apply, localUnit_apply_self]
      rfl
    · rw [mapMatrix_localMat_of_ne (𝓞 L) L v _ hw, RingHom.mapMatrix_apply,
        Matrix.diagonal_map (map_zero _)]
      simp only [finAdeleEval_apply, localUnit_apply_of_ne (𝓞 L) L v _ hw, Matrix.diagonal_one]

private theorem heckeGen_inv_eq_of_weyl_mem (U : Subgroup (AdelicGL2 (𝓞 L) L))
    (hU : finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR) ∈ U) :
    ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L), u₁ ∈ U ∧ u₂ ∈ U ∧
      (heckeGen (𝓞 L) L v)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L v * u₂ := by
  obtain ⟨ϖ, hϖ0, -, hgen, -⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen L v
  refine ⟨(Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v (piUnit L v ϖ hϖ0)))⁻¹,
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR), finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR),
    hU, hU, ?_⟩
  rw [← hgen, ← map_inv (finEmbed (𝓞 L) L), ← map_inv (localEmbed (𝓞 L) L v),
    diagPi_inv_eq L v ϖ hϖ0]
  simp only [map_mul, map_inv, finEmbed_localEmbed_piScalar]

private theorem finEmbed_localEmbed_weylR_mem (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (hv : ¬ v.asIdeal ∣ N) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR)
      ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    have hb : idealBound (𝓞 L) N v = 1 := idealBound_eq_one_of_not_dvd (R := 𝓞 L) hN hv
    have hW : IsLocalLevelOne (𝓞 L) L v N
        ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) := by
      refine ⟨fun i j => ?_, ?_, ?_⟩
      · show (!![(0 : v.adicCompletion L), 1; 1, 0] : Matrix (Fin 2) (Fin 2) _) i j
            ∈ v.adicCompletionIntegers L
        fin_cases i <;> fin_cases j <;> simp
      · show Valued.v ((!![(0 : v.adicCompletion L), 1; 1, 0] : Matrix (Fin 2) (Fin 2) _) 1 0)
            ≤ idealBound (𝓞 L) N v
        rw [hb]; simp
      · show Valued.v ((!![(0 : v.adicCompletion L), 1; 1, 0] : Matrix (Fin 2) (Fin 2) _) 1 1 - 1)
            ≤ idealBound (𝓞 L) N v
        rw [hb]; simp
    have hWinv : (((weylR : GL (Fin 2) (v.adicCompletion L))⁻¹ : GL (Fin 2) (v.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion L))
        = ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) :=
      rfl
    refine ⟨hW, ?_⟩
    rw [hWinv]
    exact hW
  · rw [mem_finiteAdelicGL2Subgroup_iff, glArch_finEmbed]

private theorem map_weylMatrix {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) :
    (!![(0 : A), 1; 1, 0] : Matrix (Fin 2) (Fin 2) A).map f = !![(0 : B), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem weyl_mul_finEmbed_localEmbed_weylR :
    weyl (𝓞 L) L * finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR)
      = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR) * weyl (𝓞 L) L := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_finEmbed, coe_localEmbed]
  have hw : ((weyl (𝓞 L) L : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
      = !![0, 1; 1, 0] := rfl
  have hwR : ((weylR : GL (Fin 2) (v.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion L))
      = !![0, 1; 1, 0] := rfl
  rw [hw, hwR]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 L) L ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, mul_one, one_mul]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat, RingHom.mapMatrix_apply, map_weylMatrix]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L fun w => ?_
    rw [map_mul, map_mul, RingHom.mapMatrix_apply (M := !![(0 : FiniteAdeleRing (𝓞 L) L), 1; 1, 0]),
      map_weylMatrix]
    by_cases hw' : w = v
    · subst hw'
      rw [mapMatrix_localMat_self]
    · rw [mapMatrix_localMat_of_ne (𝓞 L) L v _ hw', mul_one, one_mul]

private theorem finEmbed_localEmbed_weylR_mem_principalLevel (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (hv : ¬ v.asIdeal ∣ N) :
    finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR)
      ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  obtain ⟨h₁, hfin⟩ := Subgroup.mem_inf.mp (finEmbed_localEmbed_weylR_mem L v N hN hv)
  refine Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 L) L N).mpr ⟨h₁, ?_⟩, hfin⟩
  refine Subgroup.mem_map.mpr ⟨_, h₁, ?_⟩
  show weyl (𝓞 L) L * finEmbed (𝓞 L) L (localEmbed (𝓞 L) L v weylR) * (weyl (𝓞 L) L)⁻¹ = _
  rw [weyl_mul_finEmbed_localEmbed_weylR, mul_inv_cancel_right]

private theorem hstd_principalLevel_heckeGen (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hNS : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L),
        u₁ ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        u₂ ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        (heckeGen (𝓞 L) L w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L w * u₂ :=
  fun w hw =>
    heckeGen_inv_eq_of_weyl_mem L w _
      (finEmbed_localEmbed_weylR_mem_principalLevel L w N hN fun hdvd => hw (hNS w hdvd))

end StdL

end Standardness

section SlabConstruction

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Venue

variable {K : Type} [Field K] [NumberField K]

open HeckeIntegralSeam

private theorem cosetSum_eq_of_isHeckeCosetSystem {U : Subgroup (AdelicGL2 (𝓞 K) K)} {gv : AdelicGL2 (𝓞 K) K}
    {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] {reps₀ : ι₀ → AdelicGL2 (𝓞 K) K} {reps₁ : ι₁ → AdelicGL2 (𝓞 K) K}
    (h₀ : IsHeckeCosetSystem U gv reps₀) (h₁ : IsHeckeCosetSystem U gv reps₁) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) (g : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (g * reps₀ i) = ∑ j, φ (g * reps₁ j) := by

  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (reps₀ i) : AdelicGL2 (𝓞 K) K ⧸ U) = QuotientGroup.mk (reps₁ j) :=
    fun i => h₁.covers (reps₀ i) (h₀.mem_doubleCoset i)
  choose f hf using hcov
  have hinj : Function.Injective f := by
    intro i i' hii'
    apply h₀.mk_injective
    simp only
    rw [hf i, hf i', hii']
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := h₀.covers (reps₁ j) (h₁.mem_doubleCoset j)
    refine ⟨i, h₁.mk_injective ?_⟩
    simp only
    rw [← hf i, hi]
  refine Fintype.sum_bijective f ⟨hinj, hsurj⟩ _ _ fun i => ?_

  have hu : (reps₀ i)⁻¹ * reps₁ (f i) ∈ U := QuotientGroup.eq.1 (hf i)
  have e : reps₁ (f i) = reps₀ i * ((reps₀ i)⁻¹ * reps₁ (f i)) := by group
  rw [e, ← mul_assoc, hφU _ _ hu]

end Venue

namespace SlabOrthogonality

variable (K : Type) [Field K] [NumberField K]

private abbrev slabPins (Φ : Set (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

private def slabPairing (Φ : Set (AdelicGL2 (𝓞 K) K)) (a b : AdelicGL2 (𝓞 K) K → ℂ) : ℂ :=
  ∫ g in Φ, a g * conj (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K

variable {K}

section Members

variable {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
variable (W : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
  (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))

private theorem invariant_and_eigen_of_mem {Φ : HeckeEigensystem K ℂ} (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    {reps₀ : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K}
    (hsys₀ : HeckeIntegralSeam.IsHeckeCosetSystem (U N) (gen v) reps₀) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ) :
    (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U N, φ (g * u) = φ g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K, ∑ i, φ (g * reps₀ i) = Φ.a v * φ g := by
  have hφ' : φ ∈
      Submodule.span ℂ {ψ | IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ ψ} := hφ
  clear hφ
  induction hφ' using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ x := hx
    have hxU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U N, x (g * u) = x g := fun g u hu => hx'.level_invariant g u hu
    refine ⟨hxU, fun g => ?_⟩
    obtain ⟨reps, hsys, heig⟩ := hx'.hecke_eigen v hv
    rw [Venue.cosetSum_eq_of_isHeckeCosetSystem hsys₀ hsys x hxU g]
    exact heig g
  | zero => exact ⟨fun _ _ _ => rfl, fun g => by simp⟩
  | add x y _ _ hx hy =>
    refine ⟨fun g u hu => ?_, fun g => ?_⟩
    · simp only [Pi.add_apply, hx.1 g u hu, hy.1 g u hu]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hx.2 g, hy.2 g, mul_add]
  | smul c x _ hx =>
    refine ⟨fun g u hu => ?_, fun g => ?_⟩
    · simp only [Pi.smul_apply, hx.1 g u hu]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx.2 g]
      ring

end Members

open AutomorphicForm.CuspidalConstituent

variable {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 K) K)}

private theorem isSlabFundamentalDomain_of_binders (hα : 0 < α) (hαβ : α < β)
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    IsSlabFundamentalDomain K α β Φ := by
  exact ⟨hα, hαβ, hΦs, hΦ⟩

private theorem pairing_zero_eq_slabPairing (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    pairing K Φ 0 a b = slabPairing K Φ a b := by
  simp only [pairing, slabPairing, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]

private theorem slabPairing_smul_left (c : ℂ) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    slabPairing K Φ (c • a) b = c * slabPairing K Φ a b := by
  unfold slabPairing
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

private theorem slabPairing_smul_right (c : ℂ) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    slabPairing K Φ a (c • b) = conj c * slabPairing K Φ a b := by
  unfold slabPairing
  simp_rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (conj c)]
  exact integral_const_mul _ _

private theorem memLp_two_of_mem {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {a : AdelicGL2 (𝓞 K) K → ℂ}
    (ha : a ∈ contMemberSubmodule K Φ ξ) : MemLp a 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
  ((mem_memberSubmodule_iff' K Φ ξ a).1 ha.1).2

private theorem integrable_mul_conj_of_mem {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {a b : AdelicGL2 (𝓞 K) K → ℂ} (ha : a ∈ contMemberSubmodule K Φ ξ) (hb : b ∈ contMemberSubmodule K Φ ξ) :
    Integrable (fun g => a g * conj (b g)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
  (memLp_two_of_mem ha).integrable_mul (memLp_two_of_mem hb).star

private theorem slabPairing_sum_left (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) {n : ℕ}
    (a : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (ha : ∀ i, a i ∈ contMemberSubmodule K Φ ξ) (b : AdelicGL2 (𝓞 K) K → ℂ)
    (hb : b ∈ contMemberSubmodule K Φ ξ) :
    slabPairing K Φ (fun g => ∑ i, a i g) b = ∑ i, slabPairing K Φ (a i) b := by
  unfold slabPairing
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_conj_of_mem (ha i) hb

private theorem slabPairing_sum_right (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (a : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ contMemberSubmodule K Φ ξ) {n : ℕ} (b : Fin n → AdelicGL2 (𝓞 K) K → ℂ)
    (hb : ∀ i, b i ∈ contMemberSubmodule K Φ ξ) :
    slabPairing K Φ a (fun g => ∑ i, b i g) = ∑ i, slabPairing K Φ a (b i) := by
  unfold slabPairing
  simp_rw [map_sum, Finset.mul_sum]
  exact integral_finsetSum Finset.univ fun i _ => integrable_mul_conj_of_mem ha (hb i)

private theorem weightedMeasure_zero_eq : weightedMeasure K Φ 0 = (adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ := by
  rw [weightedMeasure_def]
  have hone : (fun x => ENNReal.ofReal (weight K 0 x)) = (1 : AdelicGL2 (𝓞 K) K → ENNReal) := by
    funext x
    simp [weight_def]
  rw [hone, withDensity_one]

private theorem eq_zero_of_slabPairing_self_eq_zero (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (a : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ contMemberSubmodule K Φ ξ) (h : slabPairing K Φ a a = 0) : a = 0 := by
  have hsq : slabPairing K Φ a a = ((∫ g in Φ, ‖a g‖ ^ 2 ∂adelicGLHaar (Fin 2) (𝓞 K) K : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    unfold slabPairing
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [Complex.mul_conj', Complex.ofReal_pow]
  have hint : Integrable (fun g => ‖a g‖ ^ 2) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    (memLp_two_of_mem ha).norm.integrable_sq
  have hzero : (fun g => ‖a g‖ ^ 2) =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0 :=
    (integral_eq_zero_iff_of_nonneg (f := fun g => ‖a g‖ ^ 2) (fun g => sq_nonneg ‖a g‖) hint).1
      (Complex.ofReal_eq_zero.1 (hsq.symm.trans h))
  have hae : a =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ] 0 := hzero.mono fun g hg => by simpa using hg
  refine eq_zero_of_toCarrier_eq_zero K hΦ₀ 0 ξ a ha ?_
  show (memLp_weightedMeasure_of_mem K hΦ₀ 0 ha.1).toLp a = 0
  rw [Lp.eq_zero_iff_ae_eq_zero]
  refine (MemLp.coeFn_toLp _).trans ?_
  rw [weightedMeasure_zero_eq]
  exact hae

private theorem exists_forall_slabPairing_rightTranslate_eq (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (r : AdelicGL2 (𝓞 K) K) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a b : AdelicGL2 (𝓞 K) K → ℂ, a ∈ contMemberSubmodule K Φ ξ → b ∈ contMemberSubmodule K Φ ξ →
        rightTranslate K r a ∈ contMemberSubmodule K Φ ξ ∧
        rightTranslate K r⁻¹ b ∈ contMemberSubmodule K Φ ξ ∧
        slabPairing K Φ (rightTranslate K r a) b = (κ : ℂ) * slabPairing K Φ a (rightTranslate K r⁻¹ b) := by
  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det r) :=
    NumberField.TateGlobal.ideleNorm_pos _

  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K
    (Real.sqrt (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det r))⁻¹)
    (Real.sqrt_pos.2 (inv_pos.2 hd))
  have hdet : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
    rw [show centralScalar (𝓞 K) K z = Matrix.GeneralLinearGroup.scalar (Fin 2) z from rfl,
      Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, sq]
  obtain ⟨y, hy_def⟩ : ∃ y : AdelicGL2 (𝓞 K) K, y = centralScalar (𝓞 K) K z * r := ⟨_, rfl⟩
  have hy : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) = 1 := by
    rw [hy_def, map_mul, hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, hz,
      Real.mul_self_sqrt (inv_nonneg.2 hd.le), inv_mul_cancel₀ hd.ne']
  obtain ⟨c, hc_def⟩ : ∃ c : ℂ, c = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc_def]
    exact (ξ ⟨z, Subgroup.mem_top z⟩).ne_zero
  refine ⟨‖c⁻¹‖ ^ 2, pow_pos (norm_pos_iff.2 (inv_ne_zero hc0)) 2, fun a b ha hb => ?_⟩
  obtain ⟨hya', hyb', hpair⟩ :=
    rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one K hΦ₀ 0 ξ a b ha hb y hy
  have hcen_a := ((mem_memberSubmodule_iff' K Φ ξ a).1 ha.1).1.central_transform
  have hcen_b := ((mem_memberSubmodule_iff' K Φ ξ b).1 hb.1).1.central_transform

  have hya : ∀ g : AdelicGL2 (𝓞 K) K, a (g * y) = c * a (g * r) := by
    intro g
    rw [hy_def, ← mul_assoc, AutomorphicForm.SiegelCovering.mul_centralScalar_comm, mul_assoc, hc_def]
    exact hcen_a ⟨z, Subgroup.mem_top z⟩ (g * r)
  have hyb : ∀ g : AdelicGL2 (𝓞 K) K, b (g * y⁻¹) = c⁻¹ * b (g * r⁻¹) := by
    intro g
    rw [hy_def, mul_inv_rev, ← map_inv (centralScalar (𝓞 K) K) z, ← mul_assoc,
      AutomorphicForm.SiegelCovering.mul_centralScalar_comm]
    have h := hcen_b (⟨z, Subgroup.mem_top z⟩ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))⁻¹ (g * r⁻¹)
    rw [map_inv ξ, Units.val_inv_eq_inv_val, ← hc_def] at h
    exact h
  have hra : rightTranslate K r a = c⁻¹ • rightTranslate K y a := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    rw [hya g, inv_mul_cancel_left₀ hc0]
  have hrb : rightTranslate K y⁻¹ b = c⁻¹ • rightTranslate K r⁻¹ b := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    exact hyb g
  have hrb' : rightTranslate K r⁻¹ b = c • rightTranslate K y⁻¹ b := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
    rw [hyb g, mul_inv_cancel_left₀ hc0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hra]
    exact (contMemberSubmodule K Φ ξ).smul_mem _ hya'
  · rw [hrb']
    exact (contMemberSubmodule K Φ ξ).smul_mem _ hyb'
  · calc slabPairing K Φ (rightTranslate K r a) b
        _ = c⁻¹ * pairing K Φ 0 (rightTranslate K y a) b := by
          rw [hra, slabPairing_smul_left, pairing_zero_eq_slabPairing]
        _ = c⁻¹ * slabPairing K Φ a (rightTranslate K y⁻¹ b) := by rw [hpair, pairing_zero_eq_slabPairing]
        _ = ((‖c⁻¹‖ ^ 2 : ℝ) : ℂ) * slabPairing K Φ a (rightTranslate K r⁻¹ b) := by
          rw [hrb, slabPairing_smul_right, Complex.ofReal_pow, ← Complex.mul_conj', mul_assoc]

private theorem exists_forall_mul_slabPairing_eq (hΦ₀ : IsSlabFundamentalDomain K α β Φ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (U : Subgroup (AdelicGL2 (𝓞 K) K)) (gv : AdelicGL2 (𝓞 K) K)
    (hstd : ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 K) K), u₁ ∈ U ∧ u₂ ∈ U ∧
      gv⁻¹ = centralScalar (𝓞 K) K z * u₁ * gv * u₂)
    {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps) :
    ∃ c : ℂ, ∀ (a b : AdelicGL2 (𝓞 K) K → ℂ) (A B : ℂ),
      a ∈ contMemberSubmodule K Φ ξ → b ∈ contMemberSubmodule K Φ ξ →
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, a (g * u) = a g) → (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, b (g * u) = b g) →
      (∀ g : AdelicGL2 (𝓞 K) K, ∑ i, a (g * reps i) = A * a g) →
      (∀ g : AdelicGL2 (𝓞 K) K, ∑ i, b (g * reps i) = B * b g) →
      A * slabPairing K Φ a b = c * conj B * slabPairing K Φ a b := by
  obtain ⟨z, u₁, u₂, hu₁, hu₂, hgv⟩ := hstd
  choose κ _ hκ using fun x : AdelicGL2 (𝓞 K) K => exists_forall_slabPairing_rightTranslate_eq hΦ₀ ξ x
  obtain ⟨i₀, -⟩ := hsys.covers gv (HeckePair.self_mem_doubleCoset (U := U) gv)
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 i₀.pos.ne'
  obtain ⟨w, hw_def⟩ : ∃ w : ℂ, w = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hcomm : ∀ X Y : AdelicGL2 (𝓞 K) K,
      X * (centralScalar (𝓞 K) K z * Y) = centralScalar (𝓞 K) K z * (X * Y) := fun X Y => by
    rw [← mul_assoc, AutomorphicForm.SiegelCovering.mul_centralScalar_comm, mul_assoc]
  refine ⟨(∑ i, (κ (reps i) : ℂ)) * conj w * (n : ℂ)⁻¹, fun a b A B ha hb haU hbU haE hbE => ?_⟩
  by_cases h0 : slabPairing K Φ a b = 0
  · simp only [h0, mul_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h0 (by simp [slabPairing])
  have haa : slabPairing K Φ a a ≠ 0 := fun h => ha0 (eq_zero_of_slabPairing_self_eq_zero hΦ₀ ξ a ha h)
  have hfix : ∀ u ∈ U, rightTranslate K u a = a := fun u hu => funext fun g => by
    rw [rightTranslate_apply]
    exact haU g u hu

  have hcost : ∀ u ∈ U, (κ u : ℂ) = 1 := by
    intro u hu
    have h1 := (hκ u a a ha ha).2.2
    rw [hfix u hu, hfix u⁻¹ (inv_mem hu)] at h1
    exact mul_right_cancel₀ haa (h1.symm.trans (one_mul _).symm)

  have hfree : ∀ u ∈ U, ∀ ψ : AdelicGL2 (𝓞 K) K → ℂ, ψ ∈ contMemberSubmodule K Φ ξ →
      slabPairing K Φ a (rightTranslate K u ψ) = slabPairing K Φ a ψ := by
    intro u hu ψ hψ
    have h1 := (hκ u⁻¹ a ψ ha hψ).2.2
    rw [inv_inv, hcost u⁻¹ (inv_mem hu), one_mul, hfix u⁻¹ (inv_mem hu)] at h1
    exact h1.symm
  have hcen_b := ((mem_memberSubmodule_iff' K Φ ξ b).1 hb.1).1.central_transform
  have hgvb : rightTranslate K gv b ∈ contMemberSubmodule K Φ ξ := (hκ gv b b hb hb).1

  have hL : A * slabPairing K Φ a b =
      (∑ i, (κ (reps i) : ℂ)) * (conj w * slabPairing K Φ a (rightTranslate K gv b)) := by
    have hsum := slabPairing_sum_left ξ (fun i => rightTranslate K (reps i) a)
      (fun i => (hκ (reps i) a b ha hb).1) b hb
    have hfun : (fun g => ∑ i, rightTranslate K (reps i) a g) = A • a := by
      funext g
      simp only [rightTranslate_apply, Pi.smul_apply, smul_eq_mul]
      exact haE g
    rw [hfun, slabPairing_smul_left] at hsum
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨u, hu, u', hu', hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hsys.mem_doubleCoset i)
    have hinv : rightTranslate K (reps i)⁻¹ b = w • rightTranslate K (u'⁻¹ * u₁) (rightTranslate K gv b) := by
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
      have hg : g * (reps i)⁻¹ = centralScalar (𝓞 K) K z * (g * (u'⁻¹ * u₁) * gv) * (u₂ * u⁻¹) := by
        rw [← hrep, mul_inv_rev, mul_inv_rev, hgv]
        simp only [mul_assoc]
        rw [hcomm, hcomm]
      rw [hg, hbU _ _ (mul_mem hu₂ (inv_mem hu)), hw_def]
      exact hcen_b ⟨z, Subgroup.mem_top z⟩ _
    rw [(hκ (reps i) a b ha hb).2.2, hinv, slabPairing_smul_right, hfree _ (mul_mem (inv_mem hu') hu₁) _ hgvb]

  have hR : conj B * slabPairing K Φ a b = (n : ℂ) * slabPairing K Φ a (rightTranslate K gv b) := by
    have hsum := slabPairing_sum_right ξ a ha (fun i => rightTranslate K (reps i) b)
      (fun i => (hκ (reps i) b b hb hb).1)
    have hfun : (fun g => ∑ i, rightTranslate K (reps i) b g) = B • b := by
      funext g
      simp only [rightTranslate_apply, Pi.smul_apply, smul_eq_mul]
      exact hbE g
    rw [hfun, slabPairing_smul_right] at hsum
    rw [hsum]
    have hterm : ∀ i, slabPairing K Φ a (rightTranslate K (reps i) b) =
        slabPairing K Φ a (rightTranslate K gv b) := by
      intro i
      obtain ⟨u, hu, u', hu', hrep⟩ := HeckePair.mem_doubleCoset_iff.1 (hsys.mem_doubleCoset i)
      have hrt : rightTranslate K (reps i) b = rightTranslate K u (rightTranslate K gv b) := by
        funext g
        simp only [rightTranslate_apply]
        rw [← hrep, ← mul_assoc, ← mul_assoc, hbU _ _ hu']
      rw [hrt, hfree u hu _ hgvb]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc A * slabPairing K Φ a b
    _ = (∑ i, (κ (reps i) : ℂ)) * conj w * slabPairing K Φ a (rightTranslate K gv b) := by rw [hL]; ring
    _ = (∑ i, (κ (reps i) : ℂ)) * conj w * (n : ℂ)⁻¹ *
          ((n : ℂ) * slabPairing K Φ a (rightTranslate K gv b)) := by
        rw [mul_assoc _ (n : ℂ)⁻¹, inv_mul_cancel_left₀ hn]
    _ = (∑ i, (κ (reps i) : ℂ)) * conj w * (n : ℂ)⁻¹ * conj B * slabPairing K Φ a b := by rw [← hR]; ring

private theorem mem_contMemberSubmodule_of_isIsotypicCuspFormAt
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {π : HeckeEigensystem K ℂ} {a : AdelicGL2 (𝓞 K) K → ℂ} (ha : IsIsotypicCuspFormAt K (slabPins K Φ) ξ N S π a) :
    a ∈ contMemberSubmodule K Φ ξ := by
  exact ⟨(mem_memberSubmodule_iff K Φ ξ a).2 ha.smoothCusp.1.1, ha.continuous⟩

private theorem isotypicCuspSubmodule_le_contMemberSubmodule
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (π : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K (slabPins K Φ) ξ N S π ≤ contMemberSubmodule K Φ ξ := by
  exact Submodule.span_le.2 fun a ha => mem_contMemberSubmodule_of_isIsotypicCuspFormAt ξ N S ha

private theorem toRawCentral_b_eq_of_mem_cuspClasses (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) {π : HeckeEigensystem K ℂ}
    (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    π.toRawCentral.b v =
      ((ξ ⟨Matrix.GeneralLinearGroup.det ((slabPins K Φ).gen v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
  obtain ⟨χ, hχ, hne⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hne
  have h₁ := hχ.central_eigen v hv g
  have h₂ := ((isAutomorphicFnAt_fdPins_iff K Φ ξ χ).1 hχ.smoothCusp.1.1).1.central_transform
    ⟨Matrix.GeneralLinearGroup.det ((slabPins K Φ).gen v), Subgroup.mem_top _⟩ g
  exact mul_right_cancel₀ hg (h₁.symm.trans h₂)

private theorem b_eq_b_of_mem_cuspClasses (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) {π π' : HeckeEigensystem K ℂ}
    (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S) (hπ' : π' ∈ cuspClasses K (slabPins K Φ) ξ N S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) : π.b v = π'.b v := by
  have h := (toRawCentral_b_eq_of_mem_cuspClasses ξ N S hπ v hv).trans
    (toRawCentral_b_eq_of_mem_cuspClasses ξ N S hπ' v hv).symm
  rw [HeckeEigensystem.toRawCentral_b, HeckeEigensystem.toRawCentral_b] at h
  exact mul_left_cancel₀ (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero v)) h

private theorem exists_a_ne_of_ne_of_mem_cuspClasses (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) {π π' : HeckeEigensystem K ℂ}
    (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S) (hπ' : π' ∈ cuspClasses K (slabPins K Φ) ξ N S)
    (hne : π ≠ π') : ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ π.a v ≠ π'.a v := by
  by_contra h
  exact hne (eq_of_mem_cuspClasses hπ hπ' fun v hv =>
    ⟨Classical.byContradiction fun hav => h ⟨v, hv, hav⟩, b_eq_b_of_mem_cuspClasses ξ N S hπ hπ' v hv⟩)

private theorem integral_mul_conj_eq_zero_of_ne_of_mem_cuspClasses (hα : 0 < α) (hαβ : α < β)
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    {π π' : HeckeEigensystem K ℂ} (hπ : π ∈ cuspClasses K (slabPins K Φ) ξ N S)
    (hπ' : π' ∈ cuspClasses K (slabPins K Φ) ξ N S) (hne : π ≠ π') {a b : AdelicGL2 (𝓞 K) K → ℂ}
    (ha : a ∈ isotypicCuspSubmodule K (slabPins K Φ) ξ N S π)
    (hb : b ∈ isotypicCuspSubmodule K (slabPins K Φ) ξ N S π') :
    ∫ g in Φ, a g * starRingEnd ℂ (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0 := by
  have hΦ₀ : IsSlabFundamentalDomain K α β Φ := isSlabFundamentalDomain_of_binders hα hαβ hΦs hΦ
  have ha' : a ∈ contMemberSubmodule K Φ ξ := isotypicCuspSubmodule_le_contMemberSubmodule ξ N S π ha
  have hb' : b ∈ contMemberSubmodule K Φ ξ := isotypicCuspSubmodule_le_contMemberSubmodule ξ N S π' hb
  show slabPairing K Φ a b = 0
  by_cases hb0 : b = 0
  · rw [hb0]
    simp [slabPairing]

  obtain ⟨v, hv, hav⟩ := exists_a_ne_of_ne_of_mem_cuspClasses ξ N S hπ hπ' hne
  obtain ⟨χ, hχ, -⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hπ
  obtain ⟨reps, hsys, -⟩ := hχ.hecke_eigen v hv
  obtain ⟨haU, haE⟩ := invariant_and_eigen_of_mem Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) N S v hv hsys ha
  obtain ⟨hbU, hbE⟩ := invariant_and_eigen_of_mem Φ (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) N S v hv hsys hb

  obtain ⟨c, hc⟩ := exists_forall_mul_slabPairing_eq hΦ₀ ξ (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (heckeGen (𝓞 K) K v) (StdL.hstd_principalLevel_heckeGen K N hN S hNS v hv) reps hsys
  have hab := hc a b (π.a v) (π'.a v) ha' hb' haU hbU haE hbE
  have hbb := hc b b (π'.a v) (π'.a v) hb' hb' hbU hbU hbE hbE
  have hbb0 : slabPairing K Φ b b ≠ 0 := fun h => hb0 (eq_zero_of_slabPairing_self_eq_zero hΦ₀ ξ b hb' h)
  rw [← mul_right_cancel₀ hbb0 hbb] at hab
  exact (mul_eq_mul_right_iff.1 hab).resolve_left hav

end SlabOrthogonality

end SlabConstruction

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ComplexConjugate

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (π π' : HeckeEigensystem K ℂ)
    (hπ : π ∈ cuspClasses K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S)
    (hπ' : π' ∈ cuspClasses K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S)
    (hne : π ≠ π')
    (a b : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π)
    (hb : b ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π') :
    ∫ g in Φ, a g * conj (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0 :=
  SlabOrthogonality.integral_mul_conj_eq_zero_of_ne_of_mem_cuspClasses hα hαβ hΦs hΦ ξ N
    (S14EigenPerp.ne_bot_of_forall_dvd_mem K S N hNS) S hNS hπ hπ' hne ha hb

end
end S_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab (solution)
