-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0623_parallel1
-- name    : PNT_ZeroFree_433_0623_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:18:35.711714+00:00
-- url     : https://prove2.me/theorems/67825fd0-5a90-4a0f-8d25-0f7e2bf6eb38
-- title:
--   Zero-free region foundations: Descent.FirstEnergy, Descent.FirstCoupledReindex [0623_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Descent.FirstEnergy
--   - OAI.NumberTheory.DirichletL.Descent.FirstCoupledReindex
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/FirstEnergy.lean#L14-L153
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/FirstCoupledReindex.lean#L12-L121

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0045
import Definitions.Def_PNT_ZeroFree_433_0047
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0065
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/FirstEnergy.lean#L14-L153
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/FirstCoupledReindex.lean#L12-L121
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Descent.FirstEnergy
section
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
local notation "lambda" => ConcretePrimeRowBridge.goodLambda
theorem full_rayIdealRow_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    Continuous (fun t => rayIdealRow p hg F (C t) negative χ D h) := by
  simp only [rayIdealRow, ConcretePrimeRowBridge.conjugateIdealRowSum,
    ConcretePrimeRowBridge.mobiusIdealColumn]
  fun_prop

theorem full_rayIdealRow_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖rayIdealRow p hg F (C t) negative χ D h‖ ≤ M := by
  let P := fun i => Ideal.span {p i}
  let s := supportIdealFamily P (F \ D)
  let T := fun (t : Frequency × (Fin 9 → ℝ)) (I : Ideal O) =>
    ConcretePrimeRowBridge.mobiusIdealColumn
      (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
        else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C t (D ∪ recoveredSupport P (F \ D) I)) I *
      star (ConcretePrimeRowBridge.idealSexticRow s (supportIdealFamily_pos P (F \ D))
        (supportIdealFamily_good P hg (F \ D)) I h)
  refine ⟨∑ I ∈ s, ‖T 0 I‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro t
  change ‖∑ I ∈ s, T t I‖ ≤ _
  apply (norm_sum_le s (T t)).trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  simp only [T, ConcretePrimeRowBridge.mobiusIdealColumn, norm_mul, hC]

theorem full_rayIdealEnergy_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (h : O) :
    Continuous (fun t => rayIdealEnergy p hg F (C t) negative h) := by
  unfold rayIdealEnergy
  apply continuous_finsetSum _
  intro r hr
  apply continuous_finsetSum _
  intro D hD
  exact continuous_const.mul ((full_rayIdealRow_continuous p hg F C hC negative _ D h).norm.pow 2)

theorem full_rayIdealEnergy_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, rayIdealEnergy p hg F (C t) negative h ≤ M := by
  choose M hM hbound using fun (r : RayCharacter × RayCharacter) (D : Finset ι) =>
    full_rayIdealRow_uniform_bound p hg F C hC negative (if negative then r.1 else r.2) D h
  refine ⟨∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ * (M r D)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound r D t) 2)
    (norm_nonneg _)

theorem full_integrable_rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (negative : Bool) (h : O) (b : (Frequency × (Fin 9 → ℝ)) → ℂ) (hb : Integrable b) :
    Integrable (fun t : Frequency × (Fin 9 → ℝ) => ‖b t‖ * rayIdealEnergy p hg F (C t) negative h) volume := by
  obtain ⟨M, hM, hbnd⟩ := full_rayIdealEnergy_uniform_bound p hg F C hn negative h
  apply hb.norm.mul_bdd (c := M)
  · exact (full_rayIdealEnergy_continuous p hg F C hc negative h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (rayIdealEnergy_nonneg p hg F (C t) negative h)]
      exact hbnd t)

theorem full_cube_integral_norm_le_energy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F : Finset ι)
    (C₁ C₂ : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => C₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => C₂ t S))
    (hn₁ : ∀ t S, ‖C₁ t S‖ = ‖C₁ 0 S‖)
    (hn₂ : ∀ t S, ‖C₂ t S‖ = ‖C₂ 0 S‖)
    (h : O) (b : (Frequency × (Fin 9 → ℝ)) → ℂ)
    (hb : Integrable b) (hbc : Continuous b) (a : ℂ) :
    ‖∫ t : Frequency × (Fin 9 → ℝ), b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₁ t) true h) *
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₂ t) false h) := by
  let E₁ := fun t => rayIdealEnergy p hg F (C₁ t) true h
  let E₂ := fun t => rayIdealEnergy p hg F (C₂ t) false h
  let w := fun t : Frequency × (Fin 9 → ℝ) => ‖b t‖ * ‖a‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => rayIdealEnergy_nonneg p hg F (C₁ t) true h
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => rayIdealEnergy_nonneg p hg F (C₂ t) false h
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have i₁ : Integrable (fun t => w t * E₁ t) volume := by
    convert! (full_integrable_rayIdealEnergy p hg F C₁ hc₁ hn₁ true h b hb).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₁]
    ring
  have i₂ : Integrable (fun t => w t * E₂ t) volume := by
    convert! (full_integrable_rayIdealEnergy p hg F C₂ hc₂ hn₂ false h b hb).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₂]
    ring
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (((hbc.norm.mul_const ‖a‖).mul
      (full_rayIdealEnergy_continuous p hg F C₁ hc₁ true h)))
  have hg' : Continuous g :=
    Real.continuous_sqrt.comp (((hbc.norm.mul_const ‖a‖).mul
      (full_rayIdealEnergy_continuous p hg F C₂ hc₂ false h)))
  have hfsq (t : Frequency × (Fin 9 → ℝ)) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : Frequency × (Fin 9 → ℝ)) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : Frequency × (Fin 9 → ℝ)) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : Frequency × (Fin 9 → ℝ), b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      ∫ t : Frequency × (Fin 9 → ℝ), f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (idealPairReindex_norm_le p hg F (C₁ t) (C₂ t) h) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : Frequency × (Fin 9 → ℝ), f t * g t) ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), w t * E₁ t) * Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : Frequency × (Fin 9 → ℝ), f t * g t) ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), f t ^ 2) * Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal

end
end SevenEighths.InverseMoment

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Descent.FirstCoupledReindex
section
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic CoprimeMobiusExtension
open RayFourExpansion MixedCrossSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_coprime_coupled_reindex {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
        (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
      ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
        H (D ∪ U) (D ∪ V) *
          star (supportMobius P U * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg U h)) *
            (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← prime_product_moebius P hprime hinj D]
  change supportMobius P D * _ = _
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  have hdV : Disjoint D V := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
  have hmu (S T : Finset ι) (hd : Disjoint S T) :
      supportMobius P (S ∪ T) = supportMobius P S * supportMobius P T := by
    simp only [supportMobius,prime_product_moebius P hprime hinj,
      Finset.card_union_of_disjoint hd,pow_add]
  have hrow (S T : Finset ι) (hd : Disjoint S T) :
      finiteSquarefreeRow P hg (S ∪ T) h =
        finiteSquarefreeRow P hg S h * finiteSquarefreeRow P hg T h := Finset.prod_union hd
  rw [hmu D U hdU,hmu D V hdV,hrow D U hdU,hrow D V hdV]
  simp only [star_mul,star_star,star_supportMobius]
  have hm := supportMobius_sq P hprime hinj D
  have hz := finiteSquarefreeRow_self_pair P hg D h
  calc
    _ = (supportMobius P D * supportMobius P D) *
        (star (finiteSquarefreeRow P hg D h)*finiteSquarefreeRow P hg D h) *
        (H (D ∪ U) (D ∪ V) *
          (supportMobius P U * star (C₁ (D ∪ U)) * finiteSquarefreeRow P hg U h) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h))) := by ring
    _ = _ := by rw [hm,hz]; ring

theorem first_quadratic_coupled_reindex {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * quadraticCrossPhase p hg S T *
        star (supportMobius (fun i => Ideal.span {p i}) S * C₁ S * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h)) *
        (supportMobius (fun i => Ideal.span {p i}) T * C₂ T * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
          H (D ∪ U) (D ∪ V) *
          star (supportMobius (fun i => Ideal.span {p i}) U *
            (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
          (supportMobius (fun i => Ideal.span {p i}) V *
            (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h)) := by
  let P := fun i => Ideal.span {p i}
  have hcop : Pairwise (Function.onFun IsCoprime P) := by
    intro i j hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)
  have hprime (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  let T := fun (r : RayCharacter × RayCharacter) (S V : Finset ι) => if Disjoint S V then
    H S V * star (supportMobius P S * (star (supportRay p r.1 S)*C₁ S) * star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P V * (supportRay p r.2 V*C₂ V) * star (finiteSquarefreeRow P hg V h)) else 0
  have he (S V : Finset ι) :
      (if Disjoint S V then H S V * quadraticCrossPhase p hg S V *
        star (supportMobius P S*C₁ S*star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P V*C₂ V*star (finiteSquarefreeRow P hg V h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
    by_cases hd : Disjoint S V
    · rw [if_pos hd,quadraticCrossPhase_character_expansion p hp hcop hg hc S V hd]
      simp only [Fintype.sum_prod_type,T,if_pos hd,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay,star_mul,star_star]
      ring
    · simp [T,hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ V ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun V hV => he S V)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ V ∈ B.powerset, T r S V := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ V ∈ B.powerset, crossCoeff r.1 r.2*T r S V := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact first_coprime_coupled_reindex P hprime hinj hg B _ _ H h

end
end SevenEighths.InverseMoment

end OAI

end


