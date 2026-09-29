-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/527e5934-ab39-5749-8425-f742d867e803

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
import Theorems.Thm_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace R1S9Split

open AutomorphicForm

theorem finsum_mem_eq_sum_finsum_mem_inter {α ι M : Type*} [AddCommMonoid M]
    (f : α → M) (S : Set α) (Δ : Set ι) (I : ι → Set α) (Δφ : Finset ι)
    (hsub : (↑Δφ : Set ι) ⊆ Δ)
    (hdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' → Disjoint (I t) (I t'))
    (hcov : S ⊆ ⋃ t ∈ Δ, I t)
    (hvan : ∀ t ∈ Δ, t ∉ Δφ → ∀ a ∈ S ∩ I t, f a = 0)
    (hfin : (S ∩ Function.support f).Finite) :
    ∑ᶠ a ∈ S, f a = ∑ t ∈ Δφ, ∑ᶠ a ∈ S ∩ I t, f a := by
  classical
  set s : Set α := S ∩ Function.support f with hs
  have hS : ∑ᶠ a ∈ S, f a = ∑ᶠ a ∈ s, f a := (finsum_mem_inter_support f S).symm
  have hdecomp : s = ⋃ t ∈ (↑Δφ : Set ι), (s ∩ I t) := by
    ext a
    constructor
    · intro ha
      obtain ⟨t, ht, hat⟩ : ∃ t ∈ Δ, a ∈ I t := by
        have := hcov ha.1
        simpa only [Set.mem_iUnion, exists_prop] using this
      have htφ : t ∈ Δφ := by
        by_contra h
        exact ha.2 (hvan t ht h a ⟨ha.1, hat⟩)
      exact Set.mem_biUnion (Finset.mem_coe.mpr htφ) ⟨ha, hat⟩
    · intro ha
      simp only [Set.mem_iUnion, exists_prop] at ha
      obtain ⟨t, -, hat⟩ := ha
      exact hat.1
  have hpd : (↑Δφ : Set ι).PairwiseDisjoint fun t => s ∩ I t := by
    intro t ht t' ht' hne
    exact (hdisj t (hsub ht) t' (hsub ht') hne).mono Set.inter_subset_right Set.inter_subset_right
  rw [hS, hdecomp, finsum_mem_biUnion hpd Δφ.finite_toSet (fun t _ => hfin.subset Set.inter_subset_left),
    finsum_mem_coe_finset]
  refine Finset.sum_congr rfl fun t _ => ?_
  apply finsum_mem_inter_support_eq
  ext a
  simp only [hs, Set.mem_inter_iff, Function.mem_support]
  tauto

section AdelicAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := rfl

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) :=
  sigmaAdelicAct_globalPoints K L D σ g

theorem conj_identity (h δ : GL (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L) :
    (globalPoints (𝓞 L) L h * x)⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y =
      x⁻¹ * globalPoints (𝓞 L) L (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) *
        sigmaAdelicAct K L D σ ((globalPoints (𝓞 L) L h)⁻¹ * y) := by
  rw [map_mul (sigmaAdelicAct K L D σ), map_inv (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints',
    map_mul (globalPoints (𝓞 L) L), map_mul (globalPoints (𝓞 L) L), map_inv (globalPoints (𝓞 L) L), mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs_left (g y : AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (centralScalar (𝓞 L) L w * y) = centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, ← centralScalar_comm, mul_assoc]

theorem centralScalar_principal (q : Lˣ) :
    centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (q : L)) i j =
    algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (q : L) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem unitsAct_inv_apply (w : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ (D.unitsAct σ⁻¹ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem unipotentGL2_inv {R : Type*} [CommRing R] (u : R) : (unipotentGL2 u)⁻¹ = unipotentGL2 (-u) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero]

theorem sigmaAdelicAct_unipotentGL2 (u : AdeleRing (𝓞 L) L) :
    sigmaAdelicAct K L D σ (unipotentGL2 u) = unipotentGL2 ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sigmaAdelicAct_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem kernel_transport {t g δ : GL (Fin 2) L}
    (h : t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∃ (x' : AdelicGL2 (𝓞 L) L) (z' : (AdeleRing (𝓞 L) L)ˣ),
      x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x) =
        x'⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z' * x') := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have hδ : g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g =
      t * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    rw [hu, mul_inv_cancel_left]
  set ι := globalPoints (𝓞 L) L with hι
  set uA : (AdeleRing (𝓞 L) L)ˣ := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u
    with huA
  refine ⟨(ι g)⁻¹ * x, D.unitsAct σ⁻¹ uA * z, ?_⟩
  have key : x⁻¹ * ι δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x) =
      ((ι g)⁻¹ * x)⁻¹ * ι (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) *
        sigmaAdelicAct K L D σ ((ι g)⁻¹ * (centralScalar (𝓞 L) L z * x)) := by
    have := conj_identity K L D σ g δ ((ι g)⁻¹ * x) (centralScalar (𝓞 L) L z * x)
    rw [mul_inv_cancel_left] at this
    exact this
  rw [key, hδ, map_mul ι, ← centralScalar_principal, ← huA, mul_cs_left]
  simp only [map_mul, map_inv, sigmaAdelicAct_centralScalar, MulAut.apply_inv_self, mul_assoc]

theorem borel_transport [NumberField K] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) L} (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hN : Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) (q : AdeleRing (𝓞 L) L) :
    ∃ u : AdeleRing (𝓞 L) L,
      x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 q * (centralScalar (𝓞 L) L z * x)) =
        (unipotentGL2 u * x)⁻¹ * globalPoints (𝓞 L) L γ *
          sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (unipotentGL2 u * x)) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L

  have hdet : (γ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero γ
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  obtain ⟨h00, h11⟩ := mul_ne_zero_iff.mp hdet

  set c₀ : L := (γ : Matrix (Fin 2) (Fin 2) L) 1 1 / (γ : Matrix (Fin 2) (Fin 2) L) 0 0 with hc₀
  have hc₀N : Algebra.norm K c₀ ≠ 1 := by
    have hprod : c₀ * ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 := by
      rw [hc₀]
      field_simp
    have hn := congrArg (Algebra.norm K) hprod
    rw [map_mul, map_one] at hn
    intro h
    apply hN
    rwa [h, one_mul] at hn

  obtain ⟨u, hu⟩ :=
    (M4aHerbrand.IdeleGaloisDescent.bijective_act_sub_algebraMap_mul_of_norm_ne_one D hgen c₀ hc₀N).2
      ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) q)
  refine ⟨u, ?_⟩
  dsimp only at hu
  set a : AdeleRing (𝓞 L) L := algebraMap L (AdeleRing (𝓞 L) L) ((γ : Matrix (Fin 2) (Fin 2) L) 0 0) with ha
  set b : AdeleRing (𝓞 L) L := algebraMap L (AdeleRing (𝓞 L) L) ((γ : Matrix (Fin 2) (Fin 2) L) 1 1) with hb
  set e : AdeleRing (𝓞 L) L := algebraMap L (AdeleRing (𝓞 L) L) ((γ : Matrix (Fin 2) (Fin 2) L) 0 1) with he
  have hab : a * algebraMap L (AdeleRing (𝓞 L) L) c₀ = b := by
    rw [ha, hb, hc₀, ← map_mul, mul_div_cancel₀ _ h00]
  have hu' : a * (D.act σ : RingAut (AdeleRing (𝓞 L) L)) u - b * u =
      a * (D.act σ : RingAut (AdeleRing (𝓞 L) L)) q := by
    linear_combination a * hu + u * hab

  have hι : ∀ i j, ((globalPoints (𝓞 L) L γ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      algebraMap L (AdeleRing (𝓞 L) L) ((γ : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => rfl
  have h10' : ((globalPoints (𝓞 L) L γ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 := by
    rw [hι, h10, map_zero]

  have hmat : (unipotentGL2 u)⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 u) =
      globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 q) := by
    rw [unipotentGL2_inv, sigmaAdelicAct_unipotentGL2, sigmaAdelicAct_unipotentGL2]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have e00 := hι 0 0
    have e01 := hι 0 1
    have e11 := hι 1 1
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      (simp [unipotentGL2_coe, h10', e00, e01, e11, ← ha, ← hb, ← he]; try linear_combination hu')
  calc x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 q * (centralScalar (𝓞 L) L z * x))
      = x⁻¹ * (globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 q)) *
          sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x) := by
        rw [map_mul (sigmaAdelicAct K L D σ) (unipotentGL2 q)]
        simp only [mul_assoc]
    _ = x⁻¹ * ((unipotentGL2 u)⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 u)) *
          sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x) := by rw [hmat]
    _ = (unipotentGL2 u * x)⁻¹ * globalPoints (𝓞 L) L γ *
          sigmaAdelicAct K L D σ (unipotentGL2 u * (centralScalar (𝓞 L) L z * x)) := by
        rw [map_mul (sigmaAdelicAct K L D σ) (unipotentGL2 u), mul_inv_rev]
        simp only [mul_assoc]
    _ = _ := by rw [mul_cs_left]

end AdelicAlgebra

section LocalFiniteness

variable {L : Type} [Field L] [NumberField L]

theorem finite_inter_support (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    (S : Set (GL (Fin 2) L)) (g y : AdelicGL2 (𝓞 L) L) :
    (S ∩ Function.support fun δ => φ (g * globalPoints (𝓞 L) L δ * y)).Finite := by
  have hfin := AutomorphicForm.adelicKernelLocalFiniteness L (tsupport φ) hφs g⁻¹ y
  rw [inv_inv] at hfin
  refine (hfin.subset ?_).subset Set.inter_subset_right
  intro δ hδ
  exact subset_tsupport _ hδ

theorem continuous_finsum_translate {Y : Type*} [TopologicalSpace Y]
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (S : Set (GL (Fin 2) L)) (g : AdelicGL2 (𝓞 L) L) (h : Y → AdelicGL2 (𝓞 L) L) (hh : Continuous h) :
    Continuous fun y => ∑ᶠ δ ∈ S, φ (g * globalPoints (𝓞 L) L δ * h y) := by
  classical
  refine continuous_iff_continuousAt.mpr fun y₀ => ?_
  obtain ⟨W, hWc, hWn⟩ := exists_compact_mem_nhds (h y₀)
  have hCW : IsCompact (tsupport φ * W⁻¹) := hφs.mul hWc.inv
  have hfin := AutomorphicForm.adelicKernelLocalFiniteness L (tsupport φ * W⁻¹) hCW g⁻¹ 1
  set T : Finset (GL (Fin 2) L) := hfin.toFinset with hT
  have key : ∀ y, h y ∈ W → ∀ δ, φ (g * globalPoints (𝓞 L) L δ * h y) ≠ 0 → δ ∈ T := by
    intro y hy δ hδ
    have hmem : g * globalPoints (𝓞 L) L δ * h y ∈ tsupport φ :=
      subset_tsupport _ (Function.mem_support.mpr hδ)
    simp only [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, inv_inv, mul_one]
    refine Set.mem_mul.mpr ⟨g * globalPoints (𝓞 L) L δ * h y, hmem, (h y)⁻¹, Set.inv_mem_inv.mpr hy, ?_⟩
    group
  have hloc : ∀ y, h y ∈ W → (∑ᶠ δ ∈ S, φ (g * globalPoints (𝓞 L) L δ * h y)) =
      ∑ δ ∈ T, S.indicator (fun δ => φ (g * globalPoints (𝓞 L) L δ * h y)) δ := by
    intro y hy
    rw [finsum_mem_def]
    apply finsum_eq_sum_of_support_subset
    intro δ hδ
    rw [Function.mem_support] at hδ
    have h0 : φ (g * globalPoints (𝓞 L) L δ * h y) ≠ 0 := by
      intro h0
      apply hδ
      by_cases hδS : δ ∈ S
      · rw [Set.indicator_of_mem hδS, h0]
      · rw [Set.indicator_of_notMem hδS]
    exact Finset.mem_coe.mpr (key y hy δ h0)
  have hev : (fun y => ∑ᶠ δ ∈ S, φ (g * globalPoints (𝓞 L) L δ * h y)) =ᶠ[nhds y₀]
      fun y => ∑ δ ∈ T, S.indicator (fun δ => φ (g * globalPoints (𝓞 L) L δ * h y)) δ := by
    filter_upwards [hh.continuousAt.preimage_mem_nhds hWn] with y hy
    exact hloc y hy
  refine ContinuousAt.congr_of_eventuallyEq ?_ hev
  apply Continuous.continuousAt
  refine continuous_finsetSum _ fun δ _ => ?_
  by_cases hδS : δ ∈ S
  · simp only [Set.indicator_of_mem hδS]
    exact hφc.comp (continuous_const.mul hh)
  · simp only [Set.indicator_of_notMem hδS]
    exact continuous_const

theorem exists_card_le (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) :
    ∃ N : ℕ, ∀ (y : AdelicGL2 (𝓞 L) L) (s : Finset (GL (Fin 2) L)),
      (∀ δ ∈ s, x⁻¹ * globalPoints (𝓞 L) L δ * y ∈ tsupport φ) → s.card ≤ N := by
  classical
  have hC : IsCompact (tsupport φ * (tsupport φ)⁻¹) := hφs.mul hφs.inv
  have hfin := AutomorphicForm.adelicKernelLocalFiniteness L _ hC x x
  refine ⟨hfin.toFinset.card, fun y s hs => ?_⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨δ₀, hδ₀⟩
  · simp
  refine Finset.card_le_card_of_injOn (fun δ => δ * δ₀⁻¹) (fun δ hδ => ?_) ?_
  · simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    refine Set.mem_mul.mpr ⟨x⁻¹ * globalPoints (𝓞 L) L δ * y, hs δ hδ,
      (x⁻¹ * globalPoints (𝓞 L) L δ₀ * y)⁻¹, Set.inv_mem_inv.mpr (hs δ₀ hδ₀), ?_⟩
    simp only [map_mul, map_inv]
    group
  · intro a _ b _ hab
    exact mul_right_cancel hab

theorem exists_norm_finsum_le (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (S : Set (GL (Fin 2) L)) (y : AdelicGL2 (𝓞 L) L),
      ‖∑ᶠ δ ∈ S, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)‖ ≤ M := by
  classical
  obtain ⟨N, hN⟩ := exists_card_le φ hφs x
  obtain ⟨B, hB⟩ := hφc.bounded_above_of_compact_support hφs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  refine ⟨N * B, by positivity, fun S y => ?_⟩
  have hfin : (S ∩ Function.support fun δ => φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)).Finite :=
    finite_inter_support φ hφs S x⁻¹ y
  rw [finsum_mem_eq_sum _ hfin]
  have hcard : (hfin.toFinset.card : ℝ) ≤ N := by
    exact_mod_cast hN y _ fun δ hδ => subset_tsupport _ (hfin.mem_toFinset.mp hδ).2
  calc ‖∑ δ ∈ hfin.toFinset, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)‖
      ≤ ∑ δ ∈ hfin.toFinset, ‖φ (x⁻¹ * globalPoints (𝓞 L) L δ * y)‖ := norm_sum_le _ _
    _ ≤ ∑ _δ ∈ hfin.toFinset, B := Finset.sum_le_sum fun δ _ => hB _
    _ = hfin.toFinset.card * B := by simp
    _ ≤ N * B := by gcongr

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 L) L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ centralScalar (𝓞 L) L) =
        fun z : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal fun _ : Fin 2 => (z : AdeleRing (𝓞 L) L) := by
      funext z
      rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
  · have : (fun z : (AdeleRing (𝓞 L) L)ˣ => ((centralScalar (𝓞 L) L z)⁻¹ : AdelicGL2 (𝓞 L) L).val) =
        fun z : (AdeleRing (𝓞 L) L)ˣ => Matrix.diagonal fun _ : Fin 2 => ((z⁻¹ : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L) := by
      funext z
      rw [← map_inv]
      rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_coe_inv)

end LocalFiniteness

section ClassSets

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

theorem classOrbit_subset_hyp (t : GL (Fin 2) L)
    (ht : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
        t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)} ⊆
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} :=
  (LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal hgen).1 t ⟨ht.1, ht.2.1⟩
    ht.2.2

theorem upper_mem_hyp_iff (γ : GL (Fin 2) L) (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    γ ∈ {δ : GL (Fin 2) L | ∃ γ' : GL (Fin 2) K, γ' ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ'} ↔
      Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 :=
  LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one hgen γ h10

end ClassSets

theorem assembly {Z G Q A T : Type*} {mZ : MeasurableSpace Z} (νZ : Measure Z) (Ω : Set Z)
    {mQ : MeasurableSpace Q} (μQ : Measure Q) (u : Q → G) [Group G]
    (ξ : Z → ℂ) (w : Z → G) (E : Set G) (f : A → G → ℂ)
    (S : Set A) (I : T → Set A) (B : Set A) (J : T → Set A) (Δφ : Finset T)
    (h1 : ∀ z, ∑ᶠ a ∈ S, f a (w z) = ∑ t ∈ Δφ, ∑ᶠ a ∈ I t, f a (w z))
    (h2 : ∀ z, @constantTerm Q mQ G _ μQ u (fun y => ∑ᶠ a ∈ B, f a y) (w z) =
      ∑ t ∈ Δφ, @constantTerm Q mQ G _ μQ u (fun y => ∑ᶠ a ∈ J t, f a y) (w z))
    (h3 : ∀ t ∈ Δφ, IntegrableOn (fun z => ξ z * ((∑ᶠ a ∈ I t, f a (w z)) -
      E.indicator (@constantTerm Q mQ G _ μQ u (fun y => ∑ᶠ a ∈ J t, f a y)) (w z))) Ω νZ) :
    ∫ z in Ω, ξ z * ((∑ᶠ a ∈ S, f a (w z)) -
        E.indicator (@constantTerm Q mQ G _ μQ u (fun y => ∑ᶠ a ∈ B, f a y)) (w z)) ∂νZ =
      ∑ t ∈ Δφ, ∫ z in Ω, ξ z * ((∑ᶠ a ∈ I t, f a (w z)) -
        E.indicator (@constantTerm Q mQ G _ μQ u (fun y => ∑ᶠ a ∈ J t, f a y)) (w z)) ∂νZ := by
  classical
  have hpt : (fun z => ξ z * ((∑ᶠ a ∈ S, f a (w z)) -
        E.indicator (@constantTerm Q mQ G _ μQ u (fun y => ∑ᶠ a ∈ B, f a y)) (w z))) =
      fun z => ∑ t ∈ Δφ, ξ z * ((∑ᶠ a ∈ I t, f a (w z)) -
        E.indicator (@constantTerm Q mQ G _ μQ u (fun y => ∑ᶠ a ∈ J t, f a y)) (w z)) := by
    funext z
    rw [h1 z]
    by_cases hE : w z ∈ E
    · simp only [Set.indicator_of_mem hE, h2 z, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    · simp only [Set.indicator_of_notMem hE, sub_zero, Finset.mul_sum]
  rw [hpt, integral_finsetSum _ h3]

end R1S9Split

open R1S9Split AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    (hΔcov : {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    (Δφ : Finset (GL (Fin 2) L)) (hΔφsub : (↑Δφ : Set (GL (Fin 2) L)) ⊆ Δ)
    (hΔφ : ∀ t ∈ Δ, t ∉ Δφ → ∀ (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) = 0)
    (R : ℝ) (x : AdelicGL2 (𝓞 L) L) :
    (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
    ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
    γ ∈ AutomorphicForm.hyperbolicCell K ∧
    LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
    Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
    (@AutomorphicForm.constantTerm _
    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
    (fun t => AutomorphicForm.unipotentGL2 t)
    (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
    (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)) x =
      ∑ t ∈ Δφ, (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
      Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
      (@AutomorphicForm.constantTerm _
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
      (fun t => AutomorphicForm.unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}},
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
      (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)) x := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L

  letI mA : MeasurableSpace (AdeleRing (𝓞 L) L) := adeleBorel (𝓞 L) L
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L
  beta_reduce

  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι
  set σA := AutomorphicForm.sigmaAdelicAct K L D σ with hσA
  set zc := AutomorphicForm.centralScalar (𝓞 L) L with hzc
  set Hyp : Set (GL (Fin 2) L) := {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
    γ ∈ AutomorphicForm.hyperbolicCell K ∧
    LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} with hHyp
  set Icl : GL (Fin 2) L → Set (GL (Fin 2) L) := fun t => {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
      t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
    with hIcl
  set Bset : Set (GL (Fin 2) L) := {γ : GL (Fin 2) L |
    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1} with hBset
  set ν : Measure (AdeleRing (𝓞 L) L) :=
    @ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L) with hν
  haveI hνfin : IsFiniteMeasure ν := by rw [hν]; infer_instance

  have hIsub : ∀ t ∈ Δ, Icl t ⊆ Hyp := fun t ht => classOrbit_subset_hyp hgen t (hΔd t ht)
  have hBcov : Bset ⊆ ⋃ t ∈ Δ, Icl t := by
    intro γ hγ
    exact hΔcov ((upper_mem_hyp_iff hgen γ hγ.1).mpr hγ.2)
  have hBinter : ∀ t ∈ Δ, Bset ∩ Icl t =
      {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ Icl t} := by
    intro t ht
    ext γ
    constructor
    · rintro ⟨hγB, hγI⟩
      exact ⟨hγB.1, hγI⟩
    · rintro ⟨h10, hγI⟩
      exact ⟨⟨h10, (upper_mem_hyp_iff hgen γ h10).mp (hIsub t ht hγI)⟩, hγI⟩

  have hvanK : ∀ t ∈ Δ, t ∉ Δφ → ∀ δ ∈ Icl t, ∀ (x' : AdelicGL2 (𝓞 L) L) (z' : (AdeleRing (𝓞 L) L)ˣ),
      φ (x'⁻¹ * ι δ * σA (zc z' * x')) = 0 := by
    intro t ht htφ δ hδ x' z'
    obtain ⟨g, hg⟩ := hδ
    obtain ⟨x'', z'', hxz⟩ := kernel_transport K L D σ hg x' z'
    rw [hxz]
    exact hΔφ t ht htφ x'' z''
  have hvanB : ∀ t ∈ Δ, t ∉ Δφ → ∀ γ ∈ Bset ∩ Icl t,
      ∀ (x' : AdelicGL2 (𝓞 L) L) (z' : (AdeleRing (𝓞 L) L)ˣ) (q : AdeleRing (𝓞 L) L),
      φ (x'⁻¹ * ι γ * σA (unipotentGL2 q * (zc z' * x'))) = 0 := by
    intro t ht htφ γ hγ x' z' q
    obtain ⟨u, hu⟩ := borel_transport K L D σ hgen hγ.1.1 hγ.1.2 x' z' q
    rw [hu]
    exact hvanK t ht htφ γ hγ.2 _ _

  have h1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ∑ᶠ δ ∈ Hyp, φ (x⁻¹ * ι δ * σA (zc z * x)) = ∑ t ∈ Δφ, ∑ᶠ δ ∈ Icl t, φ (x⁻¹ * ι δ * σA (zc z * x)) := by
    intro z
    rw [finsum_mem_eq_sum_finsum_mem_inter (fun δ => φ (x⁻¹ * ι δ * σA (zc z * x))) Hyp Δ Icl Δφ hΔφsub
      hΔdisj hΔcov (fun t ht htφ δ hδ => hvanK t ht htφ δ hδ.2 x z)
      (finite_inter_support φ hφs Hyp x⁻¹ (σA (zc z * x)))]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Set.inter_eq_right.mpr (hIsub t (hΔφsub (Finset.mem_coe.mpr ht)))]

  have h2 : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      @constantTerm _ (adeleBorel (𝓞 L) L) _ _ ν (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ Bset, φ (x⁻¹ * ι δ * σA y)) (zc z * x) =
        ∑ t ∈ Δφ, @constantTerm _ (adeleBorel (𝓞 L) L) _ _ ν (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ Icl t},
            φ (x⁻¹ * ι δ * σA y)) (zc z * x) := by
    intro z
    unfold constantTerm constantTermIntegrand
    have hpt : (fun q : AdeleRing (𝓞 L) L => ∑ᶠ δ ∈ Bset, φ (x⁻¹ * ι δ * σA (unipotentGL2 q * (zc z * x)))) =
        fun q => ∑ t ∈ Δφ, ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ Icl t},
          φ (x⁻¹ * ι δ * σA (unipotentGL2 q * (zc z * x))) := by
      funext q
      rw [finsum_mem_eq_sum_finsum_mem_inter (fun δ => φ (x⁻¹ * ι δ * σA (unipotentGL2 q * (zc z * x))))
        Bset Δ Icl Δφ hΔφsub hΔdisj hBcov (fun t ht htφ δ hδ => hvanB t ht htφ δ hδ x z q)
        (finite_inter_support φ hφs Bset x⁻¹ (σA (unipotentGL2 q * (zc z * x))))]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hBinter t (hΔφsub (Finset.mem_coe.mpr ht))]

    obtain ⟨M, hM0, hM⟩ := exists_norm_finsum_le φ hφc hφs x
    have hcont : ∀ S : Set (GL (Fin 2) L), Continuous fun q : AdeleRing (𝓞 L) L =>
        ∑ᶠ δ ∈ S, φ (x⁻¹ * ι δ * σA (unipotentGL2 q * (zc z * x))) := fun S =>
      continuous_finsum_translate φ hφc hφs S x⁻¹ (fun q => σA (unipotentGL2 q * (zc z * x)))
        ((continuous_sigmaAdelicAct K L D σ).comp
          (AutomorphicForm.continuous_unipotentGL2.mul continuous_const))
    have hint : ∀ S : Set (GL (Fin 2) L), Integrable (fun q : AdeleRing (𝓞 L) L =>
        ∑ᶠ δ ∈ S, φ (x⁻¹ * ι δ * σA (unipotentGL2 q * (zc z * x)))) ν := fun S =>
      (integrable_const M).mono' (hcont S).aestronglyMeasurable (Filter.Eventually.of_forall fun q => hM S _)
    show (∫ q, ∑ᶠ δ ∈ Bset, φ (x⁻¹ * ι δ * σA (unipotentGL2 q * (zc z * x))) ∂ν) =
      ∑ t ∈ Δφ, ∫ q, ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ Icl t},
          φ (x⁻¹ * ι δ * σA (unipotentGL2 q * (zc z * x))) ∂ν
    rw [hpt, integral_finsetSum _ fun t _ => hint _]

  have h3 := fun (t : GL (Fin 2) L) (_ : t ∈ Δφ) =>
    AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport K L ΦL
      νZL ΩL hΩL D σ ξL hξc hξt φ hφc hφs (Icl t)
      {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ Icl t} R x
  exact assembly νZL ΩL ν (fun t => unipotentGL2 t) (fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (fun z => zc z * x) (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
    (fun δ y => φ (x⁻¹ * ι δ * σA y)) Hyp Icl Bset
    (fun t => {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ Icl t}) Δφ h1 h2 h3

end
end S_AutomorphicForm_setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_sum_of_hasCompactSupport (solution)
