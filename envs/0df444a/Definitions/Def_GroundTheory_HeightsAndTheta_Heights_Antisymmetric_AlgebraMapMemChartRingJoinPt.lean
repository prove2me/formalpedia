-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AlgebraMapMemChartRingJoinPt
-- name    : GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AlgebraMapMemChartRingJoinPt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:19.9188+00:00
-- url     : https://prove2.me/theorems/64a0d100-4a23-45bd-a9f5-156271487a39
-- title:
--   Algebra Map Mem Chart Ring Join Pt
-- statement:
--   Definitions and structural lemmas for Algebra Map Mem Chart Ring Join Pt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/AlgebraMapMemChartRingJoinPt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo TensorProduct
section Pullback
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}
theorem algebraMap_mem_chartRing_joinPt (x : ι → Ω) (z : κ → Ω') (i : ι) (l : κ) (hz : z l ≠ 0)
    {a : Ω} (ha : a ∈ chartRing ℤ x i) :
    algebraMap Ω Ω' a ∈ chartRing ℤ (joinPt x z) (i, l) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have : algebraMap Ω Ω' (x j / x i) = joinPt x z (j, l) / joinPt x z (i, l) := by
      simp only [joinPt, segreJoin, map_div₀]
      rw [mul_div_mul_right _ _ hz]
    rw [this]
    exact div_mem_chartRing _ _ _
  | algebraMap n =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ n
  | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
  | mul y w _ _ hy hw => rw [map_mul]; exact mul_mem hy hw
theorem div_mem_chartRing_joinPt (x : ι → Ω) (z : κ → Ω') (j : ι) (l m : κ) (hx : x j ≠ 0) :
    z l / z m ∈ chartRing ℤ (joinPt x z) (j, m) := by
  have hx' : algebraMap Ω Ω' (x j) ≠ 0 := (map_ne_zero _).2 hx
  have : z l / z m = joinPt x z (j, l) / joinPt x z (j, m) := by
    simp only [joinPt, segreJoin]
    rw [mul_div_mul_left _ _ hx']
  rw [this]
  exact div_mem_chartRing _ _ _
variable {E : Type} [AddCommGroup E] [Module Ω E]
theorem one_tmul_smul (s : Ω) (v : E) :
    (1 : Ω') ⊗ₜ[Ω] (s • v) = algebraMap Ω Ω' s • ((1 : Ω') ⊗ₜ[Ω] v) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul,
    mul_one]
variable {r : ℕ}
theorem pullbackLat_stable {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ)
    {a : Ω'} (ha : a ∈ chartRing ℤ (joinPt x z) q) {e : Ω' ⊗[Ω] E} (he : e ∈ pullbackLat B z q) :
    a • e ∈ pullbackLat B z q := by
  induction he using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, v, hv, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ hw hw' => rw [smul_add]; exact add_mem hw hw'
  | neg w _ hw => rw [smul_neg]; exact neg_mem hw
theorem smul_one_tmul_mem_pullbackLat {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω')
    (q : ι × κ) {a : Ω'} (ha : a ∈ chartRing ℤ (joinPt x z) q) {v : E} (hv : v ∈ B.lat q.1) :
    a • ((1 : Ω') ⊗ₜ[Ω] v) ∈ pullbackLat B z q :=
  AddSubgroup.subset_closure ⟨a, ha, v, hv, rfl⟩
def pullbackBundle {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω') :
    ChartBundle ℤ (joinPt x z) r (Ω' ⊗[Ω] E) where
  lat := pullbackLat B z
  stable q a ha e he := pullbackLat_stable B z q ha he
  frame q hq := by
    obtain ⟨i, l⟩ := q
    obtain ⟨hxi', hzl⟩ := mul_ne_zero_iff.1 hq
    have hxi : x i ≠ 0 := fun h => hxi' (by simp [h])
    obtain ⟨k, f, c, hf, hc, hsum, hfr⟩ := B.frame i hxi
    refine ⟨k, fun l' => algebraMap Ω Ω' (f l'), fun l' => algebraMap Ω Ω' (c l'),
      fun l' => algebraMap_mem_chartRing_joinPt x z i l hzl (hf l'),
      fun l' => algebraMap_mem_chartRing_joinPt x z i l hzl (hc l'), ?_, fun l' => ?_⟩
    · simp only [← map_mul, ← map_sum, hsum, map_one]
    obtain ⟨b, hli, hspan, hiff⟩ := hfr l'
    set R := chartRing ℤ (joinPt x z) (i, l)
    set F := algebraMap Ω Ω' (f l')
    have hF : F ∈ R := algebraMap_mem_chartRing_joinPt x z i l hzl (hf l')
    let bas : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hspan.ge
    let bb := Algebra.TensorProduct.basis Ω' bas
    have hbb : ∀ q, bb q = (1 : Ω') ⊗ₜ[Ω] b q := fun q => by
      rw [Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
    have hrep : ∀ (a : Fin r → Ω') (q : Fin r), bb.repr (∑ q, a q • bb q) q = a q := fun a q => by
      rw [← bb.equivFun_symm_apply, ← bb.equivFun_apply, LinearEquiv.apply_symm_apply]

    have hRadd : ∀ a a' : Ω', (∃ n : ℕ, F ^ n * a ∈ R) → (∃ n : ℕ, F ^ n * a' ∈ R) →
        ∃ n : ℕ, F ^ n * (a + a') ∈ R := by
      rintro a a' ⟨n, hn⟩ ⟨n', hn'⟩
      refine ⟨n + n', ?_⟩
      have : F ^ (n + n') * (a + a') = F ^ n' * (F ^ n * a) + F ^ n * (F ^ n' * a') := by ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hF _) hn) (mul_mem (pow_mem hF _) hn')
    refine ⟨fun q => (1 : Ω') ⊗ₜ[Ω] b q, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
    · have := bb.linearIndependent
      simpa only [funext hbb] using this
    · have := bb.span_eq
      simpa only [funext hbb] using this
    · rintro ⟨n, hn⟩

      have key : ∀ w ∈ pullbackLat B z (i, l), ∀ q, ∃ m : ℕ, F ^ m * bb.repr w q ∈ R := by
        intro w hw
        induction hw using AddSubgroup.closure_induction with
        | mem w hw =>
          obtain ⟨a, ha, v, hv, rfl⟩ := hw
          obtain ⟨α, hα, hvα⟩ := (hiff v).1 ⟨0, by simpa using hv⟩
          have hv' : (1 : Ω') ⊗ₜ[Ω] v = ∑ q, algebraMap Ω Ω' (α q) • bb q := by
            rw [hvα, TensorProduct.tmul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [one_tmul_smul, hbb]
          intro q
          obtain ⟨m, hm⟩ := hα q
          refine ⟨m, ?_⟩
          rw [hv', map_smul, Finsupp.smul_apply, hrep, smul_eq_mul]
          have : F ^ m * (a * algebraMap Ω Ω' (α q)) = a * algebraMap Ω Ω' (f l' ^ m * α q) := by
            simp only [F, map_mul, map_pow]; ring
          rw [this]
          exact mul_mem ha (algebraMap_mem_chartRing_joinPt x z i l hzl hm)
        | zero => intro q; exact ⟨0, by simp⟩
        | add w w' _ _ hw hw' =>
          intro q
          rw [map_add, Finsupp.add_apply]
          exact hRadd _ _ (hw q) (hw' q)
        | neg w _ hw =>
          intro q
          obtain ⟨m, hm⟩ := hw q
          exact ⟨m, by rw [map_neg, Finsupp.neg_apply, mul_neg]; exact neg_mem hm⟩
      refine ⟨fun q => bb.repr e q, fun q => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := key _ hn q
        refine ⟨m + n, ?_⟩
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add] at hm
        exact hm
      · conv_lhs => rw [← bb.sum_repr e]
        exact Finset.sum_congr rfl fun q _ => by rw [hbb]
    · rintro ⟨a, ha, rfl⟩

      have hbq : ∀ q, ∃ n : ℕ, F ^ n • ((1 : Ω') ⊗ₜ[Ω] b q) ∈ pullbackLat B z (i, l) := by
        intro q
        obtain ⟨n, hn⟩ := (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
          rcases eq_or_ne q' q with rfl | h
          · simp
          · simp [Pi.single_eq_of_ne h]⟩, by simp [Pi.single_apply]⟩
        refine ⟨n, ?_⟩
        have : F ^ n • ((1 : Ω') ⊗ₜ[Ω] b q) = (1 : Ω') • ((1 : Ω') ⊗ₜ[Ω] (f l' ^ n • b q)) := by
          rw [one_smul, one_tmul_smul, map_pow]
        rw [this]
        exact smul_one_tmul_mem_pullbackLat B z (i, l) (one_mem _) hn
      refine Finset.sum_induction _ (fun w => ∃ n : ℕ, F ^ n • w ∈ pullbackLat B z (i, l)) ?_
        ⟨0, by simp⟩ fun q _ => ?_
      · rintro w w' ⟨n, hn⟩ ⟨n', hn'⟩
        refine ⟨n + n', ?_⟩
        rw [show F ^ (n + n') • (w + w') = F ^ n' • (F ^ n • w) + F ^ n • (F ^ n' • w') by
          rw [smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n' n, smul_add]]
        exact add_mem (pullbackLat_stable B z _ (pow_mem hF _) hn)
          (pullbackLat_stable B z _ (pow_mem hF _) hn')
      · obtain ⟨n, hn⟩ := hbq q
        obtain ⟨m, hm⟩ := ha q
        refine ⟨m + n, ?_⟩
        rw [pow_add, mul_smul, smul_comm (F ^ n) (a q), ← mul_smul]
        exact pullbackLat_stable B z _ hm hn
  overlap q q' hq hq' e he := by
    obtain ⟨i, l⟩ := q
    obtain ⟨j, l₂⟩ := q'
    obtain ⟨hxi', -⟩ := mul_ne_zero_iff.1 hq
    obtain ⟨hxj', -⟩ := mul_ne_zero_iff.1 hq'
    have hxi : x i ≠ 0 := fun h => hxi' (by simp [h])
    have hxj : x j ≠ 0 := fun h => hxj' (by simp [h])
    have ht : joinPt x z (i, l) / joinPt x z (j, l₂) ∈ chartRing ℤ (joinPt x z) (j, l₂) :=
      div_mem_chartRing _ _ _
    induction he using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hw
      obtain ⟨m₁, hm₁⟩ := exists_pow_mul_mem_chartRing (o := ℤ) (joinPt x z) (i, l) (j, l₂) hq ha
      obtain ⟨m₂, hm₂⟩ := B.overlap i j hxi hxj v hv
      refine ⟨m₁ + m₂, ?_⟩
      have htt : joinPt x z (i, l) / joinPt x z (j, l₂) =
          algebraMap Ω Ω' (x i / x j) * (z l / z l₂) := by
        simp only [joinPt, segreJoin, map_div₀]
        rw [mul_div_mul_comm]
      have : (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ (m₁ + m₂) • (a • ((1 : Ω') ⊗ₜ[Ω] v)) =
          ((joinPt x z (i, l) / joinPt x z (j, l₂)) ^ m₁ * a * (z l / z l₂) ^ m₂) •
            ((1 : Ω') ⊗ₜ[Ω] ((x i / x j) ^ m₂ • v)) := by
        rw [one_tmul_smul, smul_smul, smul_smul, map_pow]
        congr 1
        rw [htt]
        ring
      rw [this]
      exact smul_one_tmul_mem_pullbackLat B z (j, l₂)
        (mul_mem hm₁ (pow_mem (div_mem_chartRing_joinPt x z j l l₂ hxj) _)) hm₂
    | zero => exact ⟨0, by simp⟩
    | add w w' _ _ hw hw' =>
      obtain ⟨n, hn⟩ := hw
      obtain ⟨n', hn'⟩ := hw'
      refine ⟨n + n', ?_⟩
      rw [show (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ (n + n') • (w + w') =
          (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n' •
              ((joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n • w) +
            (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n •
              ((joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n' • w') by
        rw [smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n' n, smul_add]]
      exact add_mem (pullbackLat_stable B z _ (pow_mem ht _) hn)
        (pullbackLat_stable B z _ (pow_mem ht _) hn')
    | neg w _ hw =>
      obtain ⟨n, hn⟩ := hw
      exact ⟨n, by rw [smul_neg]; exact neg_mem hn⟩
end Pullback
end GroundTheory.Heights₂.Heights


