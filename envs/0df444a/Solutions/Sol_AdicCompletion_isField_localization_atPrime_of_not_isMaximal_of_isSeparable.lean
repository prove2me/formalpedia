-- Prove2me | solution 1 for AdicCompletion.isField_localization_atPrime_of_not_isMaximal_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/d4349299-ef3b-5536-81eb-778ecd7c468c

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionRingFunctoriality
import Definitions.Def_SemilocalAdicCompletion
import Definitions.Def_AdicCompletionTensorRing
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver
import Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable

set_option autoImplicit false
open IsLocalRing
open scoped AdicCompletion.GaloisAction TensorProduct Polynomial

namespace BDescGF

theorem core {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (K L : Type) [Field K] [Field L] [Algebra O K] [IsFractionRing O K] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O C L] [Algebra.IsSeparable K L]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (K₀ : Type) [Field K₀] [Algebra (AdicCompletion (maximalIdeal O) O) K₀] [IsFractionRing (AdicCompletion (maximalIdeal O) O) K₀]
    (F : Type) [CommRing F] [Algebra (AdicCompletion 𝔫 C) F] [Algebra (AdicCompletion (maximalIdeal O) O) F] [Algebra K₀ F]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) K₀ F]
    [IsLocalization (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C) (nonZeroDivisors (AdicCompletion (maximalIdeal O) O))) F] :
    IsReduced F ∧ Module.Finite K₀ F ∧
      Module.Finite (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) := by
  classical

  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  have hOC : Function.Injective (algebraMap O C) :=
    (faithfulSMul_iff_algebraMap_injective O C).mp inferInstance
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hOC
  haveI : Module.IsTorsionFree O C := Module.IsTorsionFree.of_smul_eq_zero (fun o c h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hOC (by rw [h, map_zero])
    · right; exact h)

  haveI : Algebra.IsIntegral O C := Algebra.IsIntegral.of_finite O C
  have hOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O C L]
    exact (IsFractionRing.injective C L).comp hOC
  have hfinKL : Module.Finite K L := by
    let ψKL : K ⊗[O] C →ₐ[K] L :=
      Algebra.TensorProduct.lift (Algebra.ofId K L) (IsScalarTower.toAlgHom O C L) (fun _ _ => Commute.all _ _)
    have hψKL : ∀ (k : K) (c : C), ψKL (k ⊗ₜ c) = algebraMap K L k * algebraMap C L c :=
      fun k c => Algebra.TensorProduct.lift_tmul _ _ _ k c
    have hsurjKL : Function.Surjective ψKL := by
      intro z
      obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := C) z
      have hd0 : (d : C) ≠ 0 := nonZeroDivisors.ne_zero hd
      obtain ⟨b, a, ha, hab⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul O (1 : C) hd0
      have hdL : algebraMap C L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have haL : algebraMap O L a ≠ 0 := (map_ne_zero_iff (algebraMap O L) hOL).mpr ha
      have key : algebraMap C L d * algebraMap C L b = algebraMap O L a := by
        rw [← map_mul, ← hab, Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply]
      refine ⟨(algebraMap O K a)⁻¹ ⊗ₜ (c * b), ?_⟩
      rw [hψKL, map_mul, map_inv₀, ← IsScalarTower.algebraMap_apply O K L, eq_div_iff hdL]
      calc (algebraMap O L a)⁻¹ * (algebraMap C L c * algebraMap C L b) * algebraMap C L d
          = (algebraMap O L a)⁻¹ * (algebraMap C L d * algebraMap C L b) * algebraMap C L c := by ring
        _ = algebraMap C L c := by rw [key, inv_mul_cancel₀ haL, one_mul]
    exact Module.Finite.of_surjective ψKL.toLinearMap hsurjKL
  haveI := hfinKL
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L

  have hinjK₀ : Function.Injective (algebraMap (AdicCompletion (maximalIdeal O) O) K₀) :=
    IsFractionRing.injective (AdicCompletion (maximalIdeal O) O) K₀
  haveI : IsDomain (AdicCompletion (maximalIdeal O) O) := Function.Injective.isDomain _ hinjK₀
  have hinjO : Function.Injective (algebraMap O (AdicCompletion (maximalIdeal O) O)) := by
    have : (algebraMap O (AdicCompletion (maximalIdeal O) O) : O → AdicCompletion (maximalIdeal O) O)
        = AdicCompletion.of (maximalIdeal O) O := by
      funext o
      rw [AdicCompletion.algebraMap_apply (maximalIdeal O), Algebra.algebraMap_self, RingHom.id_apply]
    rw [this]
    exact AdicCompletion.of_injective (maximalIdeal O) O
  letI algOK₀ : Algebra O K₀ :=
    ((algebraMap (AdicCompletion (maximalIdeal O) O) K₀).comp
      (algebraMap O (AdicCompletion (maximalIdeal O) O))).toAlgebra
  haveI : IsScalarTower O (AdicCompletion (maximalIdeal O) O) K₀ :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul O K₀ :=
    (faithfulSMul_iff_algebraMap_injective O K₀).mpr (hinjK₀.comp hinjO)
  have hunitK₀ : ∀ y : nonZeroDivisors O, IsUnit (algebraMap O K₀ y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap O K₀) (hinjK₀.comp hinjO)).mpr (nonZeroDivisors.ne_zero y.2))
  letI algKK₀ : Algebra K K₀ := (IsLocalization.lift (M := nonZeroDivisors O) (S := K) hunitK₀).toAlgebra
  haveI : IsScalarTower O K K₀ :=
    IsScalarTower.of_algebraMap_eq (fun o => (IsLocalization.lift_eq (M := nonZeroDivisors O) (S := K) hunitK₀ o).symm)
  letI algOF : Algebra O F :=
    ((algebraMap (AdicCompletion (maximalIdeal O) O) F).comp
      (algebraMap O (AdicCompletion (maximalIdeal O) O))).toAlgebra
  haveI : IsScalarTower O (AdicCompletion (maximalIdeal O) O) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower O K₀ F := IsScalarTower.of_algebraMap_eq (fun o => by
    show algebraMap (AdicCompletion (maximalIdeal O) O) F (algebraMap O _ o) =
      algebraMap K₀ F (algebraMap (AdicCompletion (maximalIdeal O) O) K₀ (algebraMap O _ o))
    rw [← IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) K₀ F])
  letI algKF : Algebra K F :=
    ((algebraMap K₀ F).comp (algebraMap K K₀)).toAlgebra
  haveI : IsScalarTower K K₀ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower O K F := IsScalarTower.of_algebraMap_eq (fun o => by
    show algebraMap O F o = algebraMap K₀ F (algebraMap K K₀ (algebraMap O K o))
    rw [← IsScalarTower.algebraMap_apply O K K₀, ← IsScalarTower.algebraMap_apply O K₀ F])

  let gCF : C →+* F := (algebraMap (AdicCompletion 𝔫 C) F).comp (algebraMap C (AdicCompletion 𝔫 C))
  have hCĈ : ∀ c : C, algebraMap C (AdicCompletion 𝔫 C) c = AdicCompletion.of 𝔫 C c := by
    intro c
    rw [AdicCompletion.algebraMap_apply 𝔫, Algebra.algebraMap_self, RingHom.id_apply]
  have hsq : ∀ o : O, gCF (algebraMap O C o) = algebraMap O F o := by
    intro o
    show algebraMap (AdicCompletion 𝔫 C) F (algebraMap C (AdicCompletion 𝔫 C) (algebraMap O C o)) =
      algebraMap (AdicCompletion (maximalIdeal O) O) F (algebraMap O (AdicCompletion (maximalIdeal O) O) o)
    rw [IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F,
      ← IsScalarTower.algebraMap_apply O (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C),
      AdicCompletion.algebraMap_apply 𝔫, AdicCompletion.algebraMap_apply 𝔫, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hunit : ∀ y : nonZeroDivisors C, IsUnit (gCF y) := by
    intro y
    have hy0 : (y : C) ≠ 0 := nonZeroDivisors.ne_zero y.2
    haveI : Algebra.IsIntegral O C := Algebra.IsIntegral.of_finite O C
    obtain ⟨b, a, ha, hab⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul O (1 : C) hy0

    have h1 : gCF (algebraMap O C a) = gCF y * gCF b := by
      rw [← map_mul, ← hab, Algebra.smul_def, mul_one]
    have hu : IsUnit (gCF (algebraMap O C a)) := by
      rw [hsq, IsScalarTower.algebraMap_apply O K₀ F]
      refine (IsUnit.mk0 _ ?_).map _
      exact (map_ne_zero_iff (algebraMap O K₀) (hinjK₀.comp hinjO)).mpr ha
    rw [h1] at hu
    exact isUnit_of_mul_isUnit_left hu
  let φ₀ : L →+* F := IsLocalization.lift (M := nonZeroDivisors C) hunit
  have hφ₀C : ∀ c : C, φ₀ (algebraMap C L c) = gCF c :=
    fun c => IsLocalization.lift_eq hunit c
  have hφ₀K : ∀ k : K, φ₀ (algebraMap K L k) =
      algebraMap K F k := by
    have : φ₀.comp (algebraMap K L) = algebraMap K F := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors O)
      ext o
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply O K L,
        IsScalarTower.algebraMap_apply O C L, hφ₀C, hsq,
        ← IsScalarTower.algebraMap_apply O K F]
    intro k
    exact congrArg (fun f : K →+* F => f k) this
  let φ : L →ₐ[K] F := { toRingHom := φ₀, commutes' := hφ₀K }
  have hφC : ∀ c : C, φ (algebraMap C L c) = gCF c := hφ₀C
  let ψ : K₀ ⊗[K] L →ₐ[K₀] F :=
    Algebra.TensorProduct.lift (Algebra.ofId K₀ F) φ (fun _ _ => Commute.all _ _)
  have hψ : ∀ (k : K₀) (l : L), ψ (k ⊗ₜ l) = algebraMap K₀ F k * φ l :=
    fun k l => Algebra.TensorProduct.lift_tmul _ _ _ k l

  set I : Ideal C := (maximalIdeal O).map (algebraMap O C) with hI
  have hI𝔫 : I ≤ 𝔫 := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro o ho
    have h := Ideal.LiesOver.over (P := 𝔫) (p := maximalIdeal O)
    rw [h] at ho
    exact ho
  haveI : IsArtinianRing (C ⧸ I) := by
    letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field (maximalIdeal O)
    haveI : Module.Finite (O ⧸ maximalIdeal O) (C ⧸ I) := inferInstance
    exact IsArtinianRing.of_finite (O ⧸ maximalIdeal O) (C ⧸ I)
  let Φ := AdicCompletion.semilocalPiEquiv I
  let T := AdicCompletion.tensorRingEquiv C (maximalIdeal O)
  let 𝔫' : {P : Ideal C // P.IsMaximal ∧ I ≤ P} := ⟨𝔫, inferInstance, hI𝔫⟩
  have hΦ : ∀ y, Φ y 𝔫' = AdicCompletion.semilocalComponent I hI𝔫 y := fun y => rfl
  have hcompat : ∀ x : AdicCompletion (maximalIdeal O) O,
      AdicCompletion.semilocalComponent I hI𝔫 (AdicCompletion.completionBaseChangeHom C (maximalIdeal O) x)
      = algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal O) n x)
    rw [AdicCompletion.evalₐ_algebraMap_of_liesOver (maximalIdeal O) 𝔫 n o x ho.symm]
    rw [AdicCompletion.semilocalComponent, AdicCompletion.evalₐ_mapₐ, AdicCompletion.completionBaseChangeHom,
      AdicCompletion.evalₐ_mapₐ, ← ho, AdicCompletion.levelMapₐ_mk, AdicCompletion.levelMapₐ_mk]
    rfl
  have hrange : ∀ c : AdicCompletion 𝔫 C, algebraMap (AdicCompletion 𝔫 C) F c ∈ ψ.range := by
    intro c
    obtain ⟨y, hy⟩ := Φ.surjective (Function.update 0 𝔫' c)
    obtain ⟨d, hd⟩ := T.surjective y
    have hc : Φ (T d) 𝔫' = c := by rw [hd, hy, Function.update_self]
    suffices h : ∀ d', algebraMap (AdicCompletion 𝔫 C) F (Φ (T d') 𝔫') ∈ ψ.range by
      rw [← hc]; exact h d
    intro d'
    induction d' using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero, Pi.zero_apply, map_zero]
      exact zero_mem _
    | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply, map_add]
      exact add_mem hx hy
    | tmul x c₀ =>
      rw [AdicCompletion.tensorRingEquiv_tmul, map_mul, Pi.mul_apply, map_mul]
      refine mul_mem ?_ ?_
      · rw [hΦ, hcompat, ← IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F,
          IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) K₀ F]
        exact Subalgebra.algebraMap_mem _ _
      · rw [AdicCompletion.semilocalPiEquiv_of]
        have : algebraMap (AdicCompletion 𝔫 C) F (AdicCompletion.of 𝔫 C c₀) =
            ψ ((1 : K₀) ⊗ₜ algebraMap C L c₀) := by
          rw [hψ, map_one, one_mul, hφC, ← hCĈ]
          rfl
        rw [this]
        exact ⟨_, rfl⟩
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨c, s⟩, hz⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C) (nonZeroDivisors (AdicCompletion (maximalIdeal O) O))) z
    obtain ⟨s₀, hs₀, hs₀eq⟩ := Submonoid.mem_map.mp s.2
    have hs₀K : algebraMap (AdicCompletion (maximalIdeal O) O) K₀ s₀ ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs₀
    have hsF : algebraMap (AdicCompletion 𝔫 C) F s =
        algebraMap K₀ F (algebraMap (AdicCompletion (maximalIdeal O) O) K₀ s₀) := by
      rw [← IsScalarTower.algebraMap_apply, ← hs₀eq, ← IsScalarTower.algebraMap_apply]
    have hz' : z = algebraMap (AdicCompletion 𝔫 C) F c *
        algebraMap K₀ F (algebraMap (AdicCompletion (maximalIdeal O) O) K₀ s₀)⁻¹ := by
      rw [← hz, hsF, mul_assoc, ← map_mul, mul_inv_cancel₀ hs₀K, map_one, mul_one]
    have hmem : z ∈ ψ.range := by
      rw [hz']
      exact mul_mem (hrange c) (Subalgebra.algebraMap_mem _ _)
    exact (AlgHom.mem_range ψ).mp hmem

  haveI : Algebra.FormallyUnramified K₀ (K₀ ⊗[K] L) := inferInstance
  haveI : Module.Finite K₀ (K₀ ⊗[K] L) := inferInstance
  haveI : Algebra.FormallyUnramified K₀ F := Algebra.FormallyUnramified.of_surjective ψ hsurj
  haveI : Module.Finite K₀ F := Module.Finite.of_surjective ψ.toLinearMap hsurj
  haveI : Algebra.EssFiniteType K₀ F := inferInstance
  refine ⟨Algebra.FormallyUnramified.isReduced_of_field K₀ F, inferInstance, ?_⟩

  have hsmul : ∀ (r : AdicCompletion (maximalIdeal O) O) (d : AdicCompletion (maximalIdeal O) O ⊗[O] C),
      Φ (T (r • d)) 𝔫' = algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) r * Φ (T d) 𝔫' := by
    intro r d
    have hsm : r • d = (r ⊗ₜ[O] (1 : C)) * d := by
      induction d using TensorProduct.induction_on with
      | zero => rw [smul_zero, mul_zero]
      | tmul a c => rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]
      | add x y hx hy => rw [smul_add, mul_add, hx, hy]
    have hof1 : AdicCompletion.of I C (1 : C) = 1 := by
      have := (AdicCompletion.algebraMap_apply I (R := C) (S := C) (1 : C)).symm
      rw [Algebra.algebraMap_self, RingHom.id_apply] at this
      rw [this, map_one]
    rw [hsm, map_mul, map_mul, Pi.mul_apply, AdicCompletion.tensorRingEquiv_tmul, hof1, mul_one, hΦ, hΦ, hcompat]
  let pL : AdicCompletion (maximalIdeal O) O ⊗[O] C →ₗ[AdicCompletion (maximalIdeal O) O] AdicCompletion 𝔫 C :=
    { toFun := fun d => Φ (T d) 𝔫'
      map_add' := fun x y => by
        show Φ (T (x + y)) 𝔫' = Φ (T x) 𝔫' + Φ (T y) 𝔫'
        rw [map_add, map_add, Pi.add_apply]
      map_smul' := fun r d => by
        show Φ (T (r • d)) 𝔫' = r • Φ (T d) 𝔫'
        rw [hsmul, Algebra.smul_def] }
  have hpL : Function.Surjective pL := by
    intro c
    obtain ⟨y, hy⟩ := Φ.surjective (Function.update 0 𝔫' c)
    obtain ⟨d, hd⟩ := T.surjective y
    exact ⟨d, by show Φ (T d) 𝔫' = c; rw [hd, hy, Function.update_self]⟩
  exact Module.Finite.of_surjective pL hpL

end BDescGF

theorem solution {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (K L : Type) [Field K] [Field L] [Algebra O K] [IsFractionRing O K] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O C L] [Algebra.IsSeparable K L]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (𝔓 : Ideal (AdicCompletion 𝔫 C)) [𝔓.IsPrime] (h𝔓 : ¬ 𝔓.IsMaximal) :
    IsField (Localization.AtPrime 𝔓) := by
  classical
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  haveI : IsNoetherianRing (AdicCompletion 𝔫 C) := AdicCompletion.isNoetherianRing_of_isNoetherianRing 𝔫

  haveI hÔnoeth : IsNoetherianRing (AdicCompletion (maximalIdeal O) O) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing (maximalIdeal O)
  have hdimO : ringKrullDim O = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one O (IsDiscreteValuationRing.not_isField O)
  have hdimÔ : ringKrullDim (AdicCompletion (maximalIdeal O) O) = 1 := by
    rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq O, hdimO]
  haveI hÔreg : IsRegularLocalRing (AdicCompletion (maximalIdeal O) O) := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [AdicCompletion.maximalIdeal_eq_map (R := O), hdimÔ]
    obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal O)).principal
    have hmap : (maximalIdeal O).map (algebraMap O (AdicCompletion (maximalIdeal O) O)) =
        Ideal.span {algebraMap O (AdicCompletion (maximalIdeal O) O) ϖ} := by
      rw [show maximalIdeal O = Ideal.span {ϖ} from hϖ, Ideal.map_span, Set.image_singleton]
    rw [hmap]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := AdicCompletion (maximalIdeal O) O)
      (Set.finite_singleton (algebraMap O (AdicCompletion (maximalIdeal O) O) ϖ))
    rw [Set.ncard_singleton] at h
    exact_mod_cast h
  haveI : IsDomain (AdicCompletion (maximalIdeal O) O) := IsRegularLocalRing.isDomain _

  let M : Submonoid (AdicCompletion 𝔫 C) :=
    Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C) (nonZeroDivisors (AdicCompletion (maximalIdeal O) O))
  haveI hMF : IsLocalization M (Localization M) := Localization.isLocalization
  have hMle : M ≤ nonZeroDivisors (AdicCompletion 𝔫 C) := by
    rintro _ ⟨r, hr, rfl⟩
    exact AdicCompletion.mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver (O := O) (C := C) 𝔫 r hr
  have hinj : Function.Injective (algebraMap (AdicCompletion 𝔫 C) (Localization M)) :=
    IsLocalization.injective (Localization M) hMle
  let K₀ := FractionRing (AdicCompletion (maximalIdeal O) O)
  have hunits : ∀ r : ↥(nonZeroDivisors (AdicCompletion (maximalIdeal O) O)),
      IsUnit (algebraMap (AdicCompletion (maximalIdeal O) O) (Localization M) r) := by
    rintro ⟨r, hr⟩
    rw [IsScalarTower.algebraMap_apply (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) (Localization M)]
    exact IsLocalization.map_units (Localization M) ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem ⟨r, hr⟩⟩
  letI algKF : Algebra K₀ (Localization M) :=
    (IsLocalization.lift (M := nonZeroDivisors (AdicCompletion (maximalIdeal O) O)) (S := K₀) hunits).toAlgebra
  haveI : IsScalarTower (AdicCompletion (maximalIdeal O) O) K₀ (Localization M) :=
    IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq hunits r).symm)
  obtain ⟨hred, hfinF, hfinOC⟩ := BDescGF.core (O := O) (C := C) K L 𝔫 K₀ (Localization M)
  haveI := hfinOC
  haveI : Algebra.IsIntegral (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) :=
    Algebra.IsIntegral.of_finite _ _

  have hq₀p : (𝔓.comap (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C))).IsPrime :=
    Ideal.IsPrime.comap _
  have hq₀m : 𝔓.comap (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C)) ≠
      maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
    intro h
    apply h𝔓
    have hmx : (𝔓.comap (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C))).IsMaximal := by
      rw [h]; exact IsLocalRing.maximalIdeal.isMaximal _
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔓 hmx
  have hq₀bot : 𝔓.comap (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C)) = ⊥ := by
    set q₀ := 𝔓.comap (algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C)) with hq₀
    haveI := hq₀p
    have hlt : q₀ < maximalIdeal _ := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hq₀p.ne_top) hq₀m
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : ((maximalIdeal (AdicCompletion (maximalIdeal O) O)).height : WithBot ℕ∞) ≤ 1 :=
      Ideal.height_le_ringKrullDim_of_isPrime.trans hdimÔ.le
    have h2' : (maximalIdeal (AdicCompletion (maximalIdeal O) O)).height ≤ 1 :=
      WithBot.coe_le_coe.1 (by rw [WithBot.coe_one]; exact h2)
    have h3 : q₀.height + 1 ≤ 1 := h1.trans h2'
    have h0 : q₀.height = 0 := by
      cases hq : q₀.height using ENat.recTopCoe with
      | top => rw [hq] at h3; simp at h3
      | coe n => rw [hq] at h3; norm_cast at h3 ⊢; omega
    have hmin : q₀ ∈ minimalPrimes (AdicCompletion (maximalIdeal O) O) := Ideal.height_eq_zero_iff.1 h0
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
    exact hmin

  have hmin𝔓 : 𝔓 ∈ minimalPrimes (AdicCompletion 𝔫 C) := by
    refine ⟨⟨inferInstance, bot_le⟩, fun 𝔓' h𝔓' hle => ?_⟩
    haveI : 𝔓'.IsPrime := h𝔓'.1
    by_contra hcon
    obtain ⟨x, hx𝔓, hx𝔓'⟩ := Set.not_subset.mp hcon
    have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := AdicCompletion (maximalIdeal O) O) hle ⟨hx𝔓, hx𝔓'⟩
      (Algebra.IsIntegral.isIntegral x)
    rw [hq₀bot] at hlt
    exact not_lt_bot hlt

  haveI : IsReduced (AdicCompletion 𝔫 C) :=
    isReduced_of_injective (algebraMap (AdicCompletion 𝔫 C) (Localization M)) hinj
  haveI : IsReduced (Localization.AtPrime 𝔓) := inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime 𝔓) :=
    IsLocalization.isNoetherianRing 𝔓.primeCompl _ inferInstance
  have hdim𝔓 : ringKrullDim (Localization.AtPrime 𝔓) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔓 (Localization.AtPrime 𝔓), Ideal.height_eq_zero_iff.2 hmin𝔓]
    rfl
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime 𝔓) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim𝔓]; exact le_rfl)
  haveI : IsArtinianRing (Localization.AtPrime 𝔓) := isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing _

end S_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable
end P2MW
export P2MW.S_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable (solution)
