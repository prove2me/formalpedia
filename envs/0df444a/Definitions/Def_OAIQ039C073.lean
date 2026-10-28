-- Prove2me | Definitions.Def_OAIQ039C073
-- name    : OAIQ039C073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:27:35.469713+00:00
-- url     : https://prove2.me/theorems/4d856721-dbd3-415c-b191-32c666bbd7cc
-- title:
--   Definitions bundle OAIQ039C073 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_MatrixApproximation`, `Commutator_MatrixScalarApproximation`, `Commutator_MatrixTowerClosure`.
--
--   **Imports.** It imports the bundle `OAIQ039C071` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C074`; the statements `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition`, `OAI.Kadison.MatrixTower.finite_standard_entrywise_bound`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.MatrixTower.rectangular_contraction_after_average`, `OAI.Kadison.MatrixTower.square_contraction_after_average` and `OAI.Kadison.MatrixTower.square_symmetry_after_average`; the proofs of `OAI.Kadison.MatrixTower.exists_matrix_freeCornerPosition`, `OAI.Kadison.MatrixTower.finite_standard_bound`, `OAI.Kadison.MatrixTower.finite_standard_entrywise_bound`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound`, `OAI.Kadison.MatrixTower.generated_factor`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.MatrixTower.rectangular_contraction_after_average`, `OAI.Kadison.MatrixTower.square_contraction_after_average` and `OAI.Kadison.MatrixTower.square_symmetry_after_average`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C071

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixApproximation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixApproximation

open TracialGNS ProjectionSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hτ hnormal hfaith hone in
theorem exists_matrix_approximation (hfac : FactorCorner.IsFactor M)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) (y : M) (hy : IsSelfAdjoint y)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (_ : Nonempty I)
      (φ : Matrix I I ℂ →⋆ₐ[ℂ] M) (x : Matrix I I ℂ),
      Function.Injective φ ∧ 2≤Fintype.card I ∧ ‖algebraVector τ (y-φ x)‖<ε := by
  classical
  obtain ⟨J,hJ,p,c,hp,ho,hpsum,he⟩ :=
    SpectralPartition.exists_spectral_step_subtype M y hy (half_pos hε)
  let : Fintype J := hJ
  let C : ℝ := ∑ j,‖c j‖
  let d : ℝ := ε/(2*(C+1))
  have hC : 0≤C := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hd : 0<d := div_pos hε (by positivity)
  obtain ⟨b,hb⟩ := exists_nat_gt (max (1:ℝ) (1/d^2))
  have hb1 : (1:ℝ)<b := (le_max_left _ _).trans_lt hb
  have hbNat : 1<b := by exact_mod_cast hb1
  have hb0 : 0<b := lt_trans Nat.zero_lt_one hbNat
  have hbR : (0:ℝ)<b := Nat.cast_pos.mpr hb0
  have hbd : 1/(b:ℝ)<d^2 := by
    have hlt : 1/d^2<(b:ℝ) := (le_max_right _ _).trans_lt hb
    have hs : 0<d^2 := sq_pos_of_pos hd
    exact (div_lt_iff₀ hbR).mpr (by
      have hh := (div_lt_iff₀ hs).mp hlt
      nlinarith)
  obtain ⟨I,hI,q,s,hq,hqo,hqs,hs⟩ :=
    NormalGNS.equal_trace_refinement M τ hτ hnormal hfaith hone hdiffuse p hp ho hpsum b hb0
  let : Fintype I := hI
  have hcard : (Fintype.card I:ℝ)/(b:ℝ)=1 := by
    have hh := congrArg (fun a : M => (τ a).re) hqs
    rw [map_sum,hone,Complex.one_re] at hh
    change Complex.reAddGroupHom (∑ i,τ (q i))=1 at hh
    rw [map_sum] at hh
    change (∑ i,(τ (q i)).re)=1 at hh
    simpa only [hq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div] using hh
  have hcardNat : Fintype.card I=b := by
    have hh := (div_eq_one_iff_eq (ne_of_gt hbR)).mp hcard
    exact_mod_cast hh
  have hcard0 : 0<Fintype.card I := by rw [hcardNat]; exact hb0
  let : Nonempty I := Fintype.card_pos_iff.mp hcard0
  have heq : ∀ i j,τ (q i)=τ (q j) := by
    intro i j
    apply Complex.ext
    · rw [(hq i).2,(hq j).2]
    · exact (τ.map_nonneg (hq i).1.nonneg).2.symm.trans (τ.map_nonneg (hq j).1.nonneg).2
  obtain ⟨φ,hφ⟩ := FiniteFactorMatrices.partition_representation M hfac τ hτ hfaith q
    (fun i => (hq i).1) heq hqo hqs
  have hadj : StarAlgebra.adjoin ℂ (Set.range q)≤φ.range := by
    apply StarAlgebra.adjoin_le
    rintro a ⟨i,rfl⟩
    exact ⟨Matrix.single i i 1,hφ i⟩
  have hmem : (∑ j,(c j:ℂ) • s j)∈φ.range := by
    apply φ.range.sum_mem
    intro j hj
    exact φ.range.smul_mem (hadj (hs j).2.2.2) _
  obtain ⟨x,hx⟩ := hmem
  change φ x=(∑ j,(c j:ℂ) • s j) at hx
  have hneq : (0:M)≠1 := by
    intro hz
    have ht := congrArg τ hz
    rw [map_zero,hone] at ht
    exact zero_ne_one ht
  let : Nontrivial M := ⟨⟨0,1,hneq⟩⟩
  refine ⟨I,hI,inferInstance,inferInstance,φ,x,φ.toAlgHom.toRingHom.injective,?_,?_⟩
  · rw [hcardNat]; omega
  · rw [hx]
    have herr := step_error τ p s c hp (fun j => (hs j).1) (fun j => (hs j).2.1)
      hd.le (fun j => ((hs j).2.2.1.trans hbd).le)
    have hCd : C*d<ε/2 := by
      have hh : d*(2*(C+1))=ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    calc
      _≤‖algebraVector τ (y-∑ j,(c j:ℂ) • p j)‖+
          ‖algebraVector τ ((∑ j,(c j:ℂ) • p j)-(∑ j,(c j:ℂ) • s j))‖ := by
        rw [map_sub,map_sub,map_sub]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _≤‖y-∑ j,(c j:ℂ) • p j‖+C*d := add_le_add (vector_norm_le τ hone _) herr
      _<ε := by linarith

end Kadison.MatrixApproximation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixScalarApproximation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixApproximation

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a)) (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)

include hτ hnormal hfaith hone in
theorem exists_scalar_expectation (hfac : FactorCorner.IsFactor M)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) (y : M) (hy : IsSelfAdjoint y)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (_ : Nonempty I)
      (φ : Matrix I I ℂ →⋆ₐ[ℂ] M),
      Function.Injective φ ∧ 2≤Fintype.card I ∧
      ‖algebraVector τ (MatrixExpectation.expectation φ y-τ y • (1:M))‖<ε := by
  obtain ⟨I,hI,hdec,hne,φ,x,hφ,hcard,he⟩ :=
    exists_matrix_approximation M τ hτ hnormal hfaith hone hfac hdiffuse y hy (half_pos hε)
  let : Fintype I := hI
  let : DecidableEq I := hdec
  let : Nonempty I := hne
  refine ⟨I,hI,hdec,hne,φ,hφ,hcard,?_⟩
  have heq : MatrixExpectation.expectation φ y-τ y • (1:M)=
      MatrixExpectation.expectation φ (y-φ x)-τ (y-φ x) • (1:M) := by
    rw [map_sub,MatrixExpectation.on_matrix_trace φ τ hτ hone,map_sub,sub_smul]
    abel
  have hn : ‖algebraVector τ (τ (y-φ x) • (1:M))‖≤‖algebraVector τ (y-φ x)‖ := by
    rw [map_smul,norm_smul]
    have h1 : ‖algebraVector τ (1:M)‖=1 := by
      exact vacuum_norm τ hone
    rw [h1,mul_one]
    exact trace_norm_le_vector τ hone _
  rw [heq,map_sub]
  calc
    _≤‖algebraVector τ (MatrixExpectation.expectation φ (y-φ x))‖+
        ‖algebraVector τ (τ (y-φ x) • (1:M))‖ := norm_sub_le _ _
    _≤2*‖algebraVector τ (y-φ x)‖ := by
      linarith [MatrixExpectation.norm_vector_le φ τ hτ (y-φ x)]
    _<ε := by linarith

end Kadison.MatrixApproximation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

lemma generated_le : generated M F≤M := by
  intro a ha
  change a∈(M : Set (H →L[ℂ] H))
  rw [←M.centralizer_centralizer]
  intro c hc
  apply (mem_generated M F a).mp ha c
  intro b hb
  exact hc b (stageAlgebra_le M F hb)

end Kadison.MatrixTower

end

end
end

end OAI
end


