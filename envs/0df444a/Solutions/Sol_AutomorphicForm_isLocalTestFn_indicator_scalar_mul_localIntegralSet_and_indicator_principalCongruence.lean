-- Prove2me | solution 1 for AutomorphicForm.isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/363e0886-ccc4-50bd-aebc-0ceca118b198

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace Ws31
namespace ITF

theorem isLocalTestFn_indicator_comp_mul_left (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (z : GL (Fin 2) (v.adicCompletion K)) {S : Set (GL (Fin 2) (v.adicCompletion K))}
    (ho : IsOpen S) (hc : IsCompact S) :
    AutomorphicForm.IsLocalTestFn K v (fun g => S.indicator (fun _ => (1 : ℂ)) (z * g)) := by
  have e : (fun g => S.indicator (fun _ => (1 : ℂ)) (z * g))
      = (S.indicator fun _ => (1 : ℂ)) ∘ (Homeomorph.mulLeft z) := rfl
  rw [e]
  exact ⟨(AutomorphicForm.isLocallyConstant_indicator_one ho hc.isClosed).comp_continuous
      (Homeomorph.mulLeft z).continuous,
    (HasCompactSupport.intro hc (fun _ hg => by simp [hg])).comp_homeomorph (Homeomorph.mulLeft z)⟩

theorem isOpen_isCompact_principalCongruence (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
        ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1} ∧
    IsCompact {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
        ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1} := by
  have hcont : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) (v.adicCompletion K) =>
      ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j := fun i j =>
    (Units.continuous_val.sub continuous_const).matrix_elem i j
  have hclopen : ∀ i j : Fin 2, IsClopen {k : GL (Fin 2) (v.adicCompletion K) |
      Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1} := fun i j => by
    have h0 := (Valued.isClopen_ball (R := v.adicCompletion K) 1).preimage (hcont i j)
    convert h0 using 1
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact (Valuation.restrict_lt_one_iff (v := Valued.v)).symm
  have hset : {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
        ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}
      = AutomorphicForm.localIntegralSet K v ∩ ⋂ i : Fin 2, ⋂ j : Fin 2,
          {k : GL (Fin 2) (v.adicCompletion K) |
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  have ho2 : IsOpen (⋂ i : Fin 2, ⋂ j : Fin 2, {k : GL (Fin 2) (v.adicCompletion K) |
      Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}) :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hclopen i j).isOpen
  have hc2 : IsClosed (⋂ i : Fin 2, ⋂ j : Fin 2, {k : GL (Fin 2) (v.adicCompletion K) |
      Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}) :=
    isClosed_iInter fun i => isClosed_iInter fun j => (hclopen i j).isClosed
  rw [hset]
  exact ⟨(AutomorphicForm.isOpen_localIntegralSet K v).inter ho2,
    (AutomorphicForm.isCompact_localIntegralSet K v).inter_right hc2⟩

end Ws31.ITF

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) :
    AutomorphicForm.IsLocalTestFn K v (fun g =>
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)) ∧
    AutomorphicForm.IsLocalTestFn K v (fun g =>
      {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
          ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}.indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)) := by
  refine ⟨Ws31.ITF.isLocalTestFn_indicator_comp_mul_left K v _
      (AutomorphicForm.isOpen_localIntegralSet K v) (AutomorphicForm.isCompact_localIntegralSet K v), ?_⟩
  obtain ⟨ho, hc⟩ := Ws31.ITF.isOpen_isCompact_principalCongruence K v
  exact Ws31.ITF.isLocalTestFn_indicator_comp_mul_left K v _ ho hc

end S_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence
end P2MW
export P2MW.S_AutomorphicForm_isLocalTestFn_indicator_scalar_mul_localIntegralSet_and_indicator_principalCongruence (solution)
