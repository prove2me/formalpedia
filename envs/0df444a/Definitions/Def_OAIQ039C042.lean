-- Prove2me | Definitions.Def_OAIQ039C042
-- name    : OAIQ039C042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:23:22.292062+00:00
-- url     : https://prove2.me/theorems/3942867a-47e5-47c8-8ba4-e6df3defa0e4
-- title:
--   Definitions bundle OAIQ039C042 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 2 definitions and 8 theorems. The definitions and types are `OAI.Kadison.ConcreteCorner.restrictCommutant`, `OAI.Kadison.NormalGNS.algebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_ConcreteCornerVonNeumann`, `Commutator_NormalGNS`, `Commutator_StandardTrace`.
--
--   **Imports.** It imports the bundle `OAIQ039C032` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C054` and `OAIQ039C057`; the proofs of `OAI.Kadison.IrreducibleTowerAveraging.hull_bounded`, `OAI.Kadison.MatrixCornerImplementation.corner_derivation_bound`, `OAI.Kadison.MatrixCornerImplementation.exists_local_module` and `OAI.Kadison.NormalGNS.commutant_range_eq_of_commutative`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C032

section
-- module Solutions.OAIQ039_CM.Commutator_ConcreteCornerVonNeumann
attribute [-instance] _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConcreteCorner

open MatrixCornerHilbert ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

variable {M} {p : Algebra M} (hp : IsStarProjection p)

lemma lift_right (T : Space hp →L[ℂ] Space hp) : lift hp T*(p:H →L[ℂ] H)=lift hp T := by
  ext x
  change (T (project hp (project hp x:H)):H)=(T (project hp x):H)
  rw [project_fixed]

variable (R : H →L[ℂ] H) (hR : R∈M.commutant)

include hR in
lemma commutant_preserves (x : H) (hx : x∈Space hp) : R x∈Space hp := by
  rw [mem_fixedSpace] at hx ⊢
  have he := VonNeumannAlgebra.mem_commutant_iff.mp hR (p:H →L[ℂ] H) p.property
  calc
    inclusion M p (R x) = R (inclusion M p x) := congrArg (fun T : H →L[ℂ] H => T x) he
    _ = R x := by rw [hx]

def restrictCommutant : Space hp →L[ℂ] Space hp := R.restrict (commutant_preserves hp R hR)

@[simp] lemma restrictCommutant_apply (x : Space hp) : (restrictCommutant hp R hR x:H)=R x := rfl

lemma project_commutant (x : H) : project hp (R x)=restrictCommutant hp R hR (project hp x) := by
  apply Subtype.ext
  exact congrArg (fun T : H →L[ℂ] H => T x)
    (VonNeumannAlgebra.mem_commutant_iff.mp hR (p:H →L[ℂ] H) p.property)

end Kadison.ConcreteCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem vector_unitball_isClosed (hnormal : BoundedWOTContinuous M τ) :
    IsClosed {x : τ.GNS | ∃ a : M, ‖a‖≤1 ∧ algebraVector τ a=x} := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  choose a ha hav using hv
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω
    (fun i => (a i : H →L[ℂ] H)) 1 (by norm_num) ha
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun i => (a i).property)
  let b : M := ⟨W,hWM⟩
  refine ⟨b,hW,?_⟩
  apply (algebraVector_dense τ).eq_of_inner_right ℂ
  intro c
  have htr : Tendsto (fun i => τ (star c*a i)) (ω : Filter ℕ) (𝓝 (τ (star c*b))) := by
    apply tendsto_trace M τ hnormal (fun i => star c*a i) (star c*b) ‖c‖
    · intro i
      exact (norm_mul_le _ _).trans (by simpa only [norm_star,mul_one] using mul_le_mul_of_nonneg_left (ha i) (norm_nonneg (star c)))
    · exact (norm_mul_le _ _).trans (by simpa only [norm_star,mul_one] using mul_le_mul_of_nonneg_left (show ‖b‖≤1 from hW) (norm_nonneg (star c)))
    · intro ξ η
      change Tendsto (fun i => inner ℂ ((star (c : H →L[ℂ] H)) ((a i : H →L[ℂ] H) ξ)) η)
        (ω : Filter ℕ) (𝓝 (inner ℂ ((star (c : H →L[ℂ] H)) (W ξ)) η))
      simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using hlim ξ ((c : H →L[ℂ] H) η)
  have hvec : Tendsto (fun i => inner ℂ (algebraVector τ c) (algebraVector τ (a i)))
      (ω : Filter ℕ) (𝓝 (inner ℂ (algebraVector τ c) x)) := by
    have ht : Tendsto (fun z : τ.GNS => inner ℂ (algebraVector τ c) z)
        (𝓝 x) (𝓝 (inner ℂ (algebraVector τ c) x)) :=
      (continuous_const.inner continuous_id).tendsto x
    exact ht.comp ((hx.mono_left hω).congr' (Eventually.of_forall fun i => (hav i).symm))
  rw [inner_algebraVector]
  simp only [inner_algebraVector] at hvec
  exact tendsto_nhds_unique htr hvec

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ

theorem bicommutant_selfAdjoint_contraction (hnormal : BoundedWOTContinuous M τ)
    {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) :
    ∃ a : M, ‖a‖≤1 ∧ τ.gnsStarAlgHom a=T := by
  have hx : T (vacuum τ)∈closure {x : τ.GNS | ∃ a : M, ‖a‖≤1 ∧ algebraVector τ a=x} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a,_,hna,he⟩ := Kaplansky.range_selfAdjoint_contraction_finite_approx
      Unit τ.gnsStarAlgHom hT hsT hnT (fun _ => vacuum τ) ε hε
    refine ⟨algebraVector τ a,⟨a,hna,rfl⟩,?_⟩
    simpa only [dist_eq_norm,norm_sub_rev,left_vacuum,algebraVector_apply] using he ()
  rw [(vector_unitball_isClosed M τ hnormal).closure_eq] at hx
  obtain ⟨a,ha,he⟩ := hx
  refine ⟨a,ha,eq_of_vacuum M τ hτ (Set.subset_centralizer_centralizer (Set.mem_range_self a)) hT ?_⟩
  simpa only [left_vacuum,algebraVector_apply] using he

theorem range_bicommutant (hnormal : BoundedWOTContinuous M τ) :
    Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom))=Set.range τ.gnsStarAlgHom := by
  apply BicommutantRange.operatorHom_range
  intro T hT hsT hnT
  obtain ⟨a,_,ha⟩ := bicommutant_selfAdjoint_contraction M τ hτ hnormal hT hsT hnT
  exact ⟨a,ha⟩

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StandardTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

def algebra : VonNeumannAlgebra τ.GNS :=
  BicommutantRange.ofStarHom τ.gnsStarAlgHom (range_bicommutant M τ hτ hnormal)

@[simp] lemma mem_algebra (T : τ.GNS →L[ℂ] τ.GNS) :
    T∈algebra M τ hτ hnormal ↔ ∃ a : M, τ.gnsStarAlgHom a=T := Iff.rfl

end Kadison.NormalGNS

end

end
end

end OAI
end


