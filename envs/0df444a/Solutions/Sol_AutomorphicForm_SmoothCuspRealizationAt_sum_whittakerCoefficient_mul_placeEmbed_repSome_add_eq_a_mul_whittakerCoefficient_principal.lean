-- Prove2me | solution 1 for AutomorphicForm.SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient_principal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/801fb5be-d89e-5efd-83d8-fe64a1e87293

import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient_principal

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.SmoothCusp LocalGL2 AdelicDock
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hint : ∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F
      (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ R.toFun α g)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    {I : Type*} [Fintype I] (b : I → v.adicCompletionIntegers F)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem
      (principalLevel (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
      (fun i : Option I => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
        (i.elim (localRepInf ϖ hϖ0) (fun c => localRepSome ϖ hϖ0 (b c))))))
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    (∑ i, whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b i))))) +
      whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)) =
      Ψ.a v * whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by
  classical

  have hSome : ∀ c : I, UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repSome
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b c)))
      = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepSome ϖ hϖ0 (b c))) := by
    intro c
    have hloc : UnramifiedWhittaker.repSome
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b c)) = localRepSome ϖ hϖ0 (b c) := by
      apply Units.ext
      simp [UnramifiedWhittaker.repSome, localRepSome, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul,
        coe_unipotentInt, coe_diagPi, Matrix.mul_fin_two]
    unfold UnramifiedWhittaker.placeEmbed
    rw [MonoidHom.comp_apply, hloc]
  have hInf : UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repInf
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)
      = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0)) := by
    have hloc : UnramifiedWhittaker.repInf
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0 = localRepInf ϖ hϖ0 := by
      apply Units.ext
      simp [UnramifiedWhittaker.repInf, localRepInf, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul,
        coe_weylInt, coe_diagPi, Matrix.mul_fin_two]
    unfold UnramifiedWhittaker.placeEmbed
    rw [MonoidHom.comp_apply, hloc]

  set fam : Option I → AdelicGL2 (𝓞 F) F := fun i => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
    (i.elim (localRepInf ϖ hϖ0) (fun c => localRepSome ϖ hϖ0 (b c)))) with hfam
  have hcard : Fintype.card (Option I) = Ideal.absNorm v.asIdeal + 1 := by
    rw [Fintype.card_option, hI]
  set e : Option I ≃ Fin (Ideal.absNorm v.asIdeal + 1) := Fintype.equivFinOfCardEq hcard with he
  set reps' : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F := fun i => fam (e.symm i) with hreps'
  have hsys' : HeckeIntegralSeam.IsHeckeCosetSystem (principalLevel (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) reps' := by
    refine ⟨fun i => hsys.mem_doubleCoset _, fun x hx => ?_, fun i j hij => ?_⟩
    · obtain ⟨j, hj⟩ := hsys.covers x hx
      refine ⟨e j, ?_⟩
      rw [hj, hreps']
      simp only [Equiv.symm_apply_apply]
    · have h2 : (QuotientGroup.mk (fam (e.symm i)) : AdelicGL2 (𝓞 F) F ⧸ (principalLevel (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F))
          = QuotientGroup.mk (fam (e.symm j)) := hij
      have := hsys.mk_injective h2
      exact e.symm.injective this

  obtain ⟨reps, hreps, hsum⟩ := R.hecke_eigen v hv
  have hinv : ∀ y : AdelicGL2 (𝓞 F) F, ∀ u ∈ principalLevel (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F,
      R.toFun (y * u) = R.toFun y := R.level_invariant
  have heq : ∀ y : AdelicGL2 (𝓞 F) F, (∑ i, R.toFun (y * reps' i)) = Ψ.a v * R.toFun y := by
    intro y
    rw [HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hreps hsys' hinv y]
    exact hsum y

  letI := adeleBorel (𝓞 F) F
  have hW : ∀ y : AdelicGL2 (𝓞 F) F, whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α y
      = ∫ x, R.toFun (unipotentGL2 x * y) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
          ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := fun y => rfl
  have hint' : ∀ y : AdelicGL2 (𝓞 F) F, Integrable
      (fun x => R.toFun (unipotentGL2 x * y) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := fun y => hint α y
  have hsumW : (∑ i, whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α (g * reps' i))
      = Ψ.a v * whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by
    simp_rw [hW]
    rw [← integral_finsetSum _ (fun i _ => hint' (g * reps' i)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have h1 : (∑ i, R.toFun (unipotentGL2 x * (g * reps' i)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
        = (∑ i, R.toFun (unipotentGL2 x * g * reps' i)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc]
    show (∑ i, R.toFun (unipotentGL2 x * (g * reps' i)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
      = Ψ.a v * (R.toFun (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
    rw [h1, heq (unipotentGL2 x * g), mul_assoc]

  have hreindex : (∑ i, whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α (g * reps' i))
      = ∑ j : Option I, whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α (g * fam j) :=
    Fintype.sum_equiv e.symm _ _ (fun i => rfl)
  rw [hreindex, Fintype.sum_option] at hsumW
  have hS : ∀ c : I, g * fam (some c) = g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repSome
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b c))) := fun c => by
    simp only [hfam, Option.elim_some, hSome]
  have hN : g * fam none = g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repInf
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0) := by
    simp only [hfam, Option.elim_none, hInf]
  simp_rw [hS, hN] at hsumW
  rw [add_comm]
  exact hsumW

end S_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient_principal
end P2MW
export P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient_principal (solution)
