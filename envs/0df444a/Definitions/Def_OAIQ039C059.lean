-- Prove2me | Definitions.Def_OAIQ039C059
-- name    : OAIQ039C059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:16:10.21341+00:00
-- url     : https://prove2.me/theorems/718341e7-323c-490d-b129-a70e472faa91
-- title:
--   Definitions bundle OAIQ039C059 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 9 definitions and 7 theorems. The definitions and types are `OAI.Kadison.Decomposable.fieldVonNeumann`, `OAI.Kadison.DihedralCorner.cornerPairFactors`, `OAI.Kadison.DihedralCorner.fejerCorner`, `OAI.Kadison.FinitePatching.Admissible`, `OAI.Kadison.FreeBlocks.ambientVonNeumann`, `OAI.Kadison.FreeBlocks.halfCornerState`, `OAI.Kadison.FreeBlocks.innerRepresentation`, `OAI.Kadison.FreeBlocks.repeatedOutput`, `OAI.Kadison.cornerFactor`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CountableProjectionJoin`, `Commutator_DihedralFejer`, `Commutator_FieldBicommutant`, `Commutator_FiniteFactorMatrices`, `Commutator_FiniteWordMaximalPatching`, `Commutator_FreeActualCovariance`, `Commutator_FreeDihedralColumns`, `Commutator_FreeFejerNorm`, `Commutator_FreeRepeatedWords`, `Commutator_HankelAlgebra`, `Commutator_NormalFreeCorner`.
--
--   **Imports.** It imports the bundles `OAIQ039C054`, `OAIQ039C055`, `OAIQ039C056` and `OAIQ039C057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C066` and `OAIQ039C068`; the statements `OAI.Kadison.DihedralCorner.compression_rotation_sandwich`, `OAI.Kadison.DihedralCorner.compression_symmetry_sandwich`, `OAI.Kadison.DihedralCorner.fejerCorner_centered`, `OAI.Kadison.DihedralCorner.fejerCorner_preGNS_norm`, `OAI.Kadison.FinitePatching.admissible_chain_upper`, `OAI.Kadison.FreeBlocks.base_block_compression`, `OAI.Kadison.FreeBlocks.base_block_intertwines`, `OAI.Kadison.FreeBlocks.base_intertwining`, `OAI.Kadison.FreeBlocks.dihedral_entry_pairing`, `OAI.Kadison.FreeBlocks.exists_free_symmetrization`, `OAI.Kadison.FreeBlocks.finite_fejer_entry`, `OAI.Kadison.FreeBlocks.free_fejer_norm`, `OAI.Kadison.FreeBlocks.free_hankel_bound`, `OAI.Kadison.FreeBlocks.free_stage_symmetrization`, `OAI.Kadison.FreeBlocks.free_word_structure`, `OAI.Kadison.FreeBlocks.innerRepresentation_commutes_other`, `OAI.Kadison.FreeBlocks.innerRepresentation_conj_mem_bicommutant`, `OAI.Kadison.FreeBlocks.innerRepresentation_continuous`, `OAI.Kadison.FreeBlocks.innerRepresentation_fixes_baseProjection`, `OAI.Kadison.FreeBlocks.innerRepresentation_word`, `OAI.Kadison.FreeBlocks.propagation_from_corner`, `OAI.Kadison.FreeBlocks.propagation_from_stage_all`, `OAI.Kadison.FreeBlocks.propagation_of_local_module`, `OAI.Kadison.FreeBlocks.repeated_error_norm` and `OAI.Kadison.FreeBlocks.stage_hankel_bound`; the proofs of `OAI.Kadison.Decomposable.factors_ae_of_central_geometry`, `OAI.Kadison.DihedralCorner.compression_rotation_sandwich`, `OAI.Kadison.DihedralCorner.compression_symmetry_sandwich`, `OAI.Kadison.DihedralCorner.fejerCorner_centered`, `OAI.Kadison.DihedralCorner.fejerCorner_preGNS_norm`, `OAI.Kadison.FinitePatching.admissible_chain_upper`, `OAI.Kadison.FinitePatching.exists_almost_full_finite_tests`, `OAI.Kadison.FreeBlocks.base_block_compression`, `OAI.Kadison.FreeBlocks.base_block_intertwines`, `OAI.Kadison.FreeBlocks.base_intertwining`, `OAI.Kadison.FreeBlocks.dihedral_entry_pairing`, `OAI.Kadison.FreeBlocks.exists_free_symmetrization`, `OAI.Kadison.FreeBlocks.finite_fejer_entry`, `OAI.Kadison.FreeBlocks.free_fejer_norm`, `OAI.Kadison.FreeBlocks.free_stage_symmetrization`, `OAI.Kadison.FreeBlocks.free_word_structure`, `OAI.Kadison.FreeBlocks.innerRepresentation_commutes_other`, `OAI.Kadison.FreeBlocks.innerRepresentation_conj_mem_bicommutant`, `OAI.Kadison.FreeBlocks.innerRepresentation_continuous`, `OAI.Kadison.FreeBlocks.innerRepresentation_fixes_baseProjection`, `OAI.Kadison.FreeBlocks.innerRepresentation_word`, `OAI.Kadison.FreeBlocks.norm_base_mul`, `OAI.Kadison.FreeBlocks.propagation_from_corner`, `OAI.Kadison.FreeBlocks.propagation_from_stage_all`, `OAI.Kadison.FreeBlocks.propagation_of_local_module`, `OAI.Kadison.FreeBlocks.repeated_error_norm`, `OAI.Kadison.FreeBlocks.repeated_norm`, `OAI.Kadison.FreeBlocks.stage_hankel_bound`, `OAI.Kadison.PartialIsometryOrder.finite_factor_unitary_subequivalence` and `OAI.Kadison.VectorGNS.gns_generation`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C055
import Definitions.Def_OAIQ039C056
import Definitions.Def_OAIQ039C057

section
-- module Solutions.OAIQ039_CM.Commutator_CountableProjectionJoin
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.ProjectionJoin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma finiteJoin_mono (P : ℕ → H →L[ℂ] H) : Monotone (finiteJoin P) :=
  monotone_nat_of_le_succ fun n => left_le (finiteJoin_projection P n) _

open PartialIsometryOrder PartialIsometryOrder.DyadicPartition

end Kadison.ProjectionJoin

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

def cornerFactor (D : StarSubalgebra ℂ A) (hpD : p∈D) : StarSubalgebra ℂ (Corner hp) where
  carrier := {a | (a : A)∈D}
  zero_mem' := zero_mem D
  add_mem' := by
    intro a b ha hb
    change (a : A)+(b : A)∈D
    exact add_mem ha hb
  mul_mem' := by
    intro a b ha hb
    change (a : A)*(b : A)∈D
    exact mul_mem ha hb
  one_mem' := hpD
  algebraMap_mem' c := by
    change c • p∈D
    exact D.smul_mem hpD c
  star_mem' := by
    intro a ha
    change star (a : A)∈D
    exact star_mem ha

end Kadison

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d : A)*(d : A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

def cornerPairFactors (hpD : p∈S i) : Bool → StarSubalgebra ℂ (Corner hp) :=
  fun b => if b then cosineAlgebra (d*s) d hr hp hpform hdp else cornerFactor hp (S i) hpD

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DihedralFejer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.DihedralCorner

open FreeMoments FejerTest

variable {A : Type*} [CStarAlgebra A]

variable {p : A} (hp : IsStarProjection p)

def fejerCorner (u : unitary A) (m : ℕ) : Corner hp :=
  compressCorner hp (testPolynomial (u:A) m)

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FieldBicommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma fieldMember_of_bicommutant_contraction (Q : Ω → VonNeumannAlgebra H)
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hA : A∈Set.centralizer (Set.centralizer (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ))))
    (hnA : ‖A‖≤1) : FieldMember μ Q A := by
  have hcomm (s : Set Ω) (hs : MeasurableSet s) : Commute A (indicatorOperator μ s hs) := by
    exact (hA (indicatorOperator μ s hs)
      (fun B hB => (fieldMember_commutes_indicator μ Q hB s hs).eq)).symm
  obtain ⟨T,hm,hb,he⟩ := exists_field_of_commutes_indicator μ A hcomm
  let v : ℕ → H := TopologicalSpace.denseSeq H
  have hap (n : ℕ) : ∃ B : Lp H 2 μ →L[ℂ] Lp H 2 μ,
      B∈fieldAlgebra μ Q ∧ ‖B‖≤1 ∧ ∀ j : Fin n,
      ‖B (Lp.const 2 μ (v j))-A (Lp.const 2 μ (v j))‖<1/((n:ℝ)+1) :=
    Kaplansky.contraction_finite_approx (Fin n) (fieldAlgebra μ Q) (fieldAlgebra_isClosed μ Q)
      hA hnA (fun j => Lp.const 2 μ (v j)) _ (by positivity)
  choose B hB hBn hBe using hap
  choose S hS hSb hSe hSm using (fun n => fieldMember_tight μ Q (hB n) (by norm_num : (0:ℝ)≤1) (hBn n))
  have hlim (j : ℕ) : Tendsto (fun n => operator μ (S n) (hS n) (hSb n)
      (Lp.const 2 μ (TopologicalSpace.denseSeq H j))) atTop
      (𝓝 (operator μ T hm hb (Lp.const 2 μ (TopologicalSpace.denseSeq H j)))) := by
    simp only [←hSe,←he]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop (j+1)] with n hn
    exact (hBe n ⟨j,by omega⟩).le
  exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,
    mem_ae_of_bounded_dense_const_limit μ Q T hm hb S hS (by norm_num) hSb hSm hlim⟩

lemma fieldMember_of_bicommutant (Q : Ω → VonNeumannAlgebra H)
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hA : A∈Set.centralizer (Set.centralizer (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))) :
    FieldMember μ Q A := by
  let d : ℂ := ((‖A‖+1:ℝ):ℂ)
  have hdR : 0<‖A‖+1 := by positivity
  have hd : d≠0 := by
    dsimp only [d]
    exact_mod_cast (ne_of_gt hdR)
  have hdn : ‖d⁻¹ • A‖≤1 := by
    rw [norm_smul,norm_inv]
    have hnd : ‖d‖=‖A‖+1 := by
      dsimp only [d]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdR]
    rw [hnd]
    have hi : (‖A‖+1)⁻¹*‖A‖=‖A‖/(‖A‖+1) := by ring
    rw [hi]
    exact (div_le_one hdR).mpr (by linarith)
  have hdc : d⁻¹ • A∈Set.centralizer (Set.centralizer
      (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ))) := by
    intro B hB
    change B*(d⁻¹ • A)=(d⁻¹ • A)*B
    rw [mul_smul_comm,smul_mul_assoc,hA B hB]
  have hmem := fieldMember_smul μ Q d
    (fieldMember_of_bicommutant_contraction μ Q (d⁻¹ • A) hdc hdn)
  simpa only [smul_smul,mul_inv_cancel₀ hd,one_smul] using hmem

def fieldVonNeumann (Q : Ω → VonNeumannAlgebra H) : VonNeumannAlgebra (Lp H 2 μ) where
  __ := fieldAlgebra μ Q
  centralizer_centralizer' := Set.Subset.antisymm
    (fun A hA => fieldMember_of_bicommutant μ Q A hA)
    (fun A hA _ hB => (hB A hA).symm)

end Kadison.Decomposable

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorMatrices
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_factor_equivalence_link (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (heq : τ ⟨e,heM⟩=τ ⟨f,hfM⟩) :
    ∃ v : Link M e f, v.initial=e ∧ v.final=f := by
  obtain ⟨v,hvi⟩ := finite_factor_comparison M hM τ hτ hfaith heM hfM he hf heq.le
  have hti : τ ⟨v.initial,v.initial_mem⟩=τ ⟨e,heM⟩ := congrArg τ (Subtype.ext hvi)
  have htf : τ ⟨v.final,v.final_mem⟩=τ ⟨f,hfM⟩ :=
    (v.trace_initial_final τ hτ).symm.trans (hti.trans heq)
  have hmem : f-v.final∈M := M.sub_mem hfM v.final_mem
  have hzero : τ ⟨f-v.final,hmem⟩=0 := by
    change τ ((⟨f,hfM⟩ : M)-⟨v.final,v.final_mem⟩)=0
    rw [map_sub,htf,sub_self]
  have hvf := (sub_eq_zero.mp (faithful_projection M τ hfaith hmem
    (v.residual_target_projection hf) hzero)).symm
  exact ⟨v,hvi,hvf⟩

end Kadison.PartialIsometryOrder

namespace Kadison.FiniteFactorMatrices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem partition_representation (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (p : I→M) (hp : ∀ i, IsStarProjection (p i))
    (heq : ∀ i j, τ (p i)=τ (p j))
    (horth : ∀ i j, i≠j → p i*p j=0) (hone : ∑ i,p i=1) :
    ∃ φ : Matrix I I ℂ →⋆ₐ[ℂ] M,
      ∀ i, φ (Matrix.single i i (1:ℂ))=p i := by
  let i₀ : I := Classical.choice inferInstance
  have hv : ∀ i, ∃ v : PartialIsometryOrder.Link M (p i₀) (p i),
      v.initial=p i₀ ∧ v.final=p i := by
    intro i
    exact PartialIsometryOrder.finite_factor_equivalence_link M hM τ hτ hfaith
      (p i₀).property (p i).property
      ((hp i₀).map M.toStarSubalgebra.subtype) ((hp i).map M.toStarSubalgebra.subtype)
      (heq i₀ i)
  choose v hvi hvf using hv
  let u : I→M := fun i => ⟨(v i).val,(v i).mem⟩
  have hsource : ∀ i, star (u i)*u i=p i₀ := fun i => Subtype.ext (hvi i)
  have hfinal : ∀ i, u i*star (u i)=p i := fun i => Subtype.ext (hvf i)
  have hfix : ∀ i, u i*p i₀=u i := by
    intro i
    apply Subtype.ext
    change (v i).val*(p i₀ : H →L[ℂ] H)=(v i).val
    simpa only [hvi i] using (v i).mul_initial
  have htarget : ∀ i, p i*u i=u i := by
    intro i
    apply Subtype.ext
    change (p i : H →L[ℂ] H)*(v i).val=(v i).val
    simpa only [hvf i] using (v i).final_mul
  refine ⟨MatrixUnits.ofPartialIsometries (p i₀) p u hsource hfinal hfix htarget
    (fun i => (hp i).isSelfAdjoint.star_eq) horth hone,?_⟩
  intro i
  rw [MatrixUnits.ofPartialIsometries_single,hfinal]

end Kadison.FiniteFactorMatrices

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteWordMaximalPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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

open Words

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))

variable {J K : Type*} (x : J → M) (k : K → ℤ)

def Admissible (N : ℕ) (ε η : ℝ) : Set (PartialUnitary M) :=
  {v | (v.val : H →L[ℂ] H)∈R ∧ (τ v.support).re ≤ 1-η ∧
    MomentBound τ x k v N (momentBudget ε (budgetSlope N η) (τ v.support).re)}

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualCovariance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

abbrev innerRepresentation : unitary D →* (t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS) :=
  representation t S hfree hgen (innerFamily f i) (innerFamily_mem f S i hS)
    (innerFamily_trace t ht f i) (innerFamily_one f i) (innerFamily_mul f i)

end Kadison.FreeBlocks

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeRepeatedWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

def repeatedOutput (d : D) (x : letterSpace t S i) (n : ℕ) :
    multiplicityLevel t S j n →L[ℂ] t.functional.GNS :=
  tensorOutput (Left := sourceScalar t f hf n) (Right := multiplicityLevel t S j n)
    (sourceLevelEmbedding t f hf S i j hS hfree hij n)
    (PreHilbert.word (factorFull t f hf) (factorZero t f hf) n
      (TracialGNS.algebraVector (factorTrace t f hf) d)
      (fun _ => letterGNSIso t f hf S i hS
        (HilbertCompletion.coeIsometry (dLetters t S i) x)))

lemma norm_repeatedOutput (d : D) (x : letterSpace t S i)
    (n : ℕ) (v : multiplicityLevel t S j n) :
    ‖repeatedOutput t S f hf hS hfree hij d x n v‖=
      ‖TracialGNS.algebraVector (factorTrace t f hf) d‖*‖x‖^n*‖v‖ := by
  rw [repeatedOutput, norm_tensorOutput]
  have hw := PreHilbert.norm_word (factorFull t f hf)
    (factorZero t f hf) n
    (TracialGNS.algebraVector (factorTrace t f hf) d)
    (fun _ => letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) x))
  have hxnorm (k : Fin n) : ‖letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) x)‖ = ‖x‖ := by
    exact (letterGNSIso t f hf S i hS).norm_map _ |>.trans
      ((HilbertCompletion.coeIsometry (dLetters t S i)).norm_map _)
  have hprod : ∏ k : Fin n, ‖letterGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (dLetters t S i) x)‖ = ‖x‖^n := by
    calc
      _ = ∏ _k : Fin n, ‖x‖ := Finset.prod_congr rfl (fun k _ => hxnorm k)
      _ = _ := by simp
  exact congrArg (fun r : ℝ => r*‖v‖)
    (hw.trans (congrArg (fun r : ℝ => ‖TracialGNS.algebraVector (factorTrace t f hf) d‖*r) hprod))

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeDihedralColumns
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

lemma norm_letterOf_unitary (i : Bool) (u : unitary A)
    (hu : (u:A)∈S i) (hu0 : t.functional (u:A)=0) :
    ‖letterOf t S i (u:A) hu hu0‖=1 := by
  change ‖t.functional.toPreGNS (u:A)‖=1
  rw [PositiveLinearMap.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [Unitary.star_mul_self_of_mem u.property,t.normalized,Complex.one_re,Real.sqrt_one]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeFejerNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

def halfCornerState (hpt : t.functional p=((1/2:ℝ):ℂ)) : FaithfulState (Corner hp) where
  functional := cornerFunctional hp t.functional (1/2) (by norm_num)
  normalized := cornerFunctional_normalized hp t.functional (by norm_num) hpt
  faithful := cornerFunctional_faithful hp t.functional (by norm_num) t.faithful

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalFreeCorner
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def ambientVonNeumann (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A) :
    VonNeumannAlgebra t.functional.GNS where
  toStarSubalgebra := ambientOperators t S
  centralizer_centralizer' := by
    have he : (ambientOperators t S).carrier =
        Set.centralizer (Set.centralizer (generatedOperators t S : Set (t.functional.GNS →L[ℂ] t.functional.GNS))) :=
      by ext x; exact mem_ambientOperators t S
    change Set.centralizer (Set.centralizer (ambientOperators t S).carrier)=(ambientOperators t S).carrier
    rw [he]
    simp only [Set.centralizer_centralizer_centralizer]

end Kadison.FreeBlocks

end

end
end

end OAI
end


