-- Prove2me | Definitions.Def_OAIQ039C045
-- name    : OAIQ039C045
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:32.405806+00:00
-- url     : https://prove2.me/theorems/46f825f0-b56c-46ad-9bdd-0035e558fcbb
-- title:
--   Definitions bundle OAIQ039C045 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 4 definitions and 7 theorems. The definitions and types are `OAI.Kadison.FinitePatching.Words.mapLetter`, `OAI.Kadison.FinitePatching.Words.newLetter`, `OAI.Kadison.FinitePatching.Words.slotIncrement`, `OAI.Kadison.FinitePatching.Words.wordCost`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DecomposableDenseLimit`, `Commutator_FiniteHankel`, `Commutator_HankelAlgebra`, `Commutator_KaplanskyDensity`, `Commutator_KaplanskyFull`, `Commutator_MatrixAlgebraDensity`, `Commutator_PartialUnitaryWords`, `Commutator_PartialWordContinuity`, `Commutator_PartialWordReindex`.
--
--   **Imports.** It imports the bundles `OAIQ039C032`, `OAIQ039C033`, `OAIQ039C034` and `OAIQ039C035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C054` and `OAIQ039C055`; the statement `OAI.Kadison.FinitePatching.Words.momentBound_completed`; the proofs of `OAI.Kadison.FinitePatching.Words.momentBound_completed`, `OAI.Kadison.FinitePatching.Words.moment_limit_of_dense_coefficients` and `OAI.Kadison.FinitePatching.Words.word_perturbation_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C034
import Definitions.Def_OAIQ039C035

section
-- module Solutions.OAIQ039_CM.Commutator_DecomposableDenseLimit
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem mem_ae_of_bounded_dense_const_limit (Q : Ω → VonNeumannAlgebra H)
    (T : Ω → H →L[ℂ] H) (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {c : ℝ} (hc : ∀ᵐ a ∂μ,‖T a‖ ≤ c)
    (S : ℕ → Ω → H →L[ℂ] H)
    (hS : ∀ n ξ,AEStronglyMeasurable (fun a => S n a ξ) μ)
    {b : ℝ} (hb : 0≤b) (hSb : ∀ n,∀ᵐ a ∂μ,‖S n a‖≤b)
    (hmem : ∀ n,∀ᵐ a ∂μ,S n a∈Q a)
    (hlim : ∀ j : ℕ,Tendsto (fun n => operator μ (S n) (hS n) (hSb n)
      (Lp.const 2 μ (TopologicalSpace.denseSeq H j))) atTop
      (𝓝 (operator μ T hT hc (Lp.const 2 μ (TopologicalSpace.denseSeq H j))))) : ∀ᵐ a ∂μ,T a∈Q a := by
  let v : ℕ → H := TopologicalSpace.denseSeq H
  let V : ℕ → Lp H 2 μ := fun j => Lp.constL 2 μ ℂ (v j)
  have hconst (j : ℕ) : V j =ᵐ[μ] fun _ => v j := Lp.coeFn_const 2 μ (v j)
  have hfinite (m : ℕ) : ∀ᵐ a ∂μ,∃ k : ℕ → ℕ,∀ j : Fin m,
      Tendsto (fun n => S (k n) a (v j)) atTop (𝓝 (T a (v j))) := by
    obtain ⟨k,hk,hka⟩ := exists_finite_test_subsequence μ
      (fun n (j : Fin m) => operator μ (S n) (hS n) (hSb n) (V j))
      (fun (j : Fin m) => operator μ T hT hc (V j)) (fun j => hlim j)
    filter_upwards [hka,ae_all_iff.mpr hconst,
      ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun j : ℕ =>
        operator_ae μ (S n) (hS n) (hSb n) (V j))),
      ae_all_iff.mpr (fun j : ℕ => operator_ae μ T hT hc (V j))]
      with a hka hv hs ht
    refine ⟨k,fun j => ?_⟩
    have he (n : ℕ) : operator μ (S (k n)) (hS (k n)) (hSb (k n)) (V j) a=
        S (k n) a (v j) := by rw [hs,hv]
    have he' : operator μ T hT hc (V j) a=T a (v j) := by rw [ht,hv]
    simpa only [he,he'] using hka j
  filter_upwards [ae_all_iff.mpr hfinite,ae_all_iff.mpr hSb,ae_all_iff.mpr hmem]
    with a hf hba hma
  apply mem_vonNeumann_of_dense_finite_tests (Q a) v
    (TopologicalSpace.denseRange_denseSeq H) (T a) b hb
  intro m
  obtain ⟨k,hk⟩ := hf m
  have hevent : ∀ᶠ n in atTop,∀ j : Fin m,
      ‖S (k n) a (v j)-T a (v j)‖<1/((m:ℝ)+1) := by
    apply eventually_all.mpr
    intro j
    exact (tendsto_iff_norm_sub_tendsto_zero.mp (hk j)).eventually
      (gt_mem_nhds (by positivity : (0:ℝ)<1/((m:ℝ)+1)))
  obtain ⟨n,hn⟩ := hevent.exists
  exact ⟨S (k n) a,hma (k n),hba (k n),fun j => (hn j).le⟩

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FiniteCompression

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
@[simp] lemma averageIsometry_toCLM (c : ℝ) (U : I → K →ₗᵢ[ℂ] H) horth hscale :
    (averageIsometry c U horth hscale).toContinuousLinearMap =
      average c (fun i => (U i).toContinuousLinearMap) := rfl

end Kadison.FiniteCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

variable (hr : MulAut.conj d u=u⁻¹)

include hr in
lemma reflection_wave (n : ℤ) : (d : A)*wave u n=wave u (-n)*(d : A) := by
  have h : d*u^n=u^(-n)*d := by
    calc
      d*u^n = (MulAut.conj d (u^n))*d := by simp [MulAut.conj_apply, mul_assoc]
      _ = (u⁻¹)^n*d := by rw [map_zpow, hr]
      _ = u^(-n)*d := by simp
  exact congrArg (fun z : unitary A => (z : A)) h

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem selfAdjoint_contraction_finite_approx
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧ ‖a‖≤1 ∧ ∀ i, ‖a (x i)-T (x i)‖<ε := by
  let : IsClosed (S : Set (H →L[ℂ] H)) := hS
  let b := lift T
  have hb : b∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) :=
    cfc_bicommutant S hT rationalLift
  have hsb : IsSelfAdjoint b := lift_selfAdjoint T
  have hcb : clip b=T := clip_lift hsT hnT
  let v : SumSpace (H:=H) (ι⊕ι) := WithLp.toLp 2
    (Sum.elim (fun i => kernel b (x i)) (fun i => b (kernel b (x i))))
  obtain ⟨a,ha,hsa,he⟩ := selfAdjoint_finite_approx (ι⊕ι) S hb hsb v (ε/3) (by positivity)
  refine ⟨clip a,?_,clip_selfAdjoint a,clip_norm_le a,?_⟩
  · exact cfc_mem (𝕜:=ℝ) (𝕜':=ℂ) (s:=S) rationalClip ha
  · intro i
    have h₁ : ‖(a-b) (kernel b (x i))‖<ε/3 := by
      have h := (PiLp.norm_apply_le (p:=2)
        (diagonal (H:=H) (ι⊕ι) a v-diagonal (H:=H) (ι⊕ι) b v) (Sum.inl i)).trans_lt he
      simpa only [PiLp.sub_apply,diagonal_apply,v,WithLp.ofLp_toLp,
        Sum.elim_inl,sub_apply] using h
    have h₂ : ‖(a-b) (b (kernel b (x i)))‖<ε/3 := by
      have h := (PiLp.norm_apply_le (p:=2)
        (diagonal (H:=H) (ι⊕ι) a v-diagonal (H:=H) (ι⊕ι) b v) (Sum.inr i)).trans_lt he
      simpa only [PiLp.sub_apply,diagonal_apply,v,WithLp.ofLp_toLp,
        Sum.elim_inr,sub_apply] using h
    rw [←hcb]
    exact (clip_difference_apply hsa hsb (x i)).trans_lt (by linarith)

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

open CyclicColumns CyclicSpatial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixAlgebraDensityDecidableEq
variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

lemma matrixUnit_mem_fullMatrixAlgebra (i j : ι) :
    matrixUnit (H:=H) ι i j∈fullMatrixAlgebra ι S := by
  rw [mem_fullMatrixAlgebra_iff]
  intro k l
  have he : entry ι (matrixUnit (H:=H) ι i j) k l=if k=i ∧ j=l then 1 else 0 := by
    ext x
    by_cases hki : k=i <;> by_cases hjl : j=l <;>
      simp [entry_apply,matrixUnit_apply,single_apply,hki,hjl]
  rw [he]
  split_ifs <;> simp

lemma bicommutant_fullMatrix_of_entries (i₀ : ι)
    (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (hT : ∀ i j, entry ι T i j∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    T∈Set.centralizer (Set.centralizer (fullMatrixAlgebra ι S :
      Set (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι))) := by
  intro R hR
  have hU : ∀ i j, matrixUnit ι i j*R=R*matrixUnit ι i j :=
    fun i j => hR _ (matrixUnit_mem_fullMatrixAlgebra ι S i j)
  have he := diagonal_of_matrixUnits ι i₀ R hU
  let a := entry ι R i₀ i₀
  have ha : a∈Set.centralizer (S : Set (H →L[ℂ] H)) := by
    intro b hb
    exact entry_commutes ι R b (hR _ (diagonal_mem_fullMatrixAlgebra ι S hb)) i₀ i₀
  rw [he]
  exact commutes_of_entries ι T a (fun i j => hT i j a ha)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFull
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

attribute [local instance] OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma offDiagonal_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S : Set (H →L[ℂ] H))] {a : H →L[ℂ] H}
    (ha : a∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    offDiagonal a∈Set.centralizer (Set.centralizer (fullMatrixAlgebra (Fin 2) S :
      Set (SumSpace (H:=H) (Fin 2) →L[ℂ] SumSpace (H:=H) (Fin 2)))) := by
  apply bicommutant_fullMatrix_of_entries (Fin 2) S 0
  intro i j
  rw [entry_offDiagonal]
  split_ifs
  · exact ha
  · exact star_bicommutant S ha
  · intro T _
    simp

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A]

variable (x : J → A) (k : K → ℤ)

def slotIncrement (w : PartialUnitary A) : Slot K → A
  | none => 0
  | some none => w.support
  | some (some i) => w.power (k i)

def newLetter (w : PartialUnitary A) (i : Letter J K) : A := x i.1*slotIncrement k w i.2

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialWordContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

namespace Words

variable (x : J → A) (k : K → ℤ)

def wordCost (l : List (Letter J K)) : ℕ := (l.map (fun i => slotCost k i.2)).sum

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialWordReindex
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.Words

variable {A J K J' K' : Type*} [CStarAlgebra A]

def mapLetter (f : J' → J) (g : K' → K) (i : Letter J' K') : Letter J K :=
  (f i.1,i.2.map (Option.map g))

end Kadison.FinitePatching.Words

end

end
end

end OAI
end


