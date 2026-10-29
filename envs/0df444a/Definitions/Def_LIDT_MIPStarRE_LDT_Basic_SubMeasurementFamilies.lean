-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
-- name    : LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:52:37.531228+00:00
-- url     : https://prove2.me/theorems/ed0796e6-4385-4761-8f36-2e7a7e2e1e79
-- title:
--   LIDT definitions: LDT / Basic / SubMeasurementFamilies
-- statement:
--   This bundle defines question-indexed families of measurements and submeasurements, including projective and complete variants. It also provides the forgetful conversions used when a proof needs to discard completeness, projectivity, or both while retaining the same indexed effects.
--
--   Principal definitions:
--   - `IdxSubMeas`: a question-indexed family of submeasurements.
--   - `IdxMeas`: a question-indexed family of complete measurements.
--   - `IdxProjSubMeas`: a question-indexed family of projective submeasurements.
--   - `IdxProjMeas`: a question-indexed family of projective measurements.
--   - `toIdxSubMeas`: forgets completeness from an indexed measurement family.
--   - `toIdxSubMeas`: forgets projectivity from an indexed projective submeasurement family.
--   - `toIdxMeas`: forgets projectivity from an indexed projective measurement family.
--   - `toIdxSubMeas`: forgets both properties from an indexed projective measurement family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean#L20-L611

-- Generated from MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Indexed and bipartite submeasurement infrastructure

Indexed measurement families, tensor placements, and lift/placement constructors.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Indexed measurement families -/

/-- Question-indexed family of submeasurements. -/
abbrev IdxSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → SubMeas Outcome ι

/-- Question-indexed family of measurements. -/
abbrev IdxMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → Measurement Outcome ι

/-- Question-indexed family of projective submeasurements. -/
abbrev IdxProjSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjSubMeas Outcome ι

/-- Question-indexed family of projective measurements. -/
abbrev IdxProjMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjMeas Outcome ι

namespace IdxMeas

/-- Forget completeness from an indexed measurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxMeas

namespace IdxProjSubMeas

/-- Forget projectivity from an indexed projective submeasurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjSubMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxProjSubMeas

namespace IdxProjMeas

/-- Forget projectivity from an indexed projective measurement family. -/
def toIdxMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) :
    IdxMeas Question Outcome ι :=
  fun q => (A q).toMeasurement

/-- Forget both projectivity and completeness from an indexed projective measurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxProjMeas

open scoped Classical in
/-- Post-process the outcomes of a submeasurement. The processed operator at `b` is the
sum of the operators of all `a` with `f a = b`. -/
noncomputable def postprocess {α β : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (f : α → β) :
    SubMeas β ι where
  outcome := fun b =>
    ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
  total := A.total
  outcome_pos := fun _ => Finset.sum_nonneg fun a _ => A.outcome_pos a
  sum_eq_total := (Finset.sum_fiberwise Finset.univ f A.outcome).trans A.sum_eq_total
  total_le_one := A.total_le_one

namespace SubMeas

/-- The outcome of a postprocessed submeasurement is the sum over the fiber of
the readout map. -/
@[simp] theorem postprocess_outcome {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq β] [DecidableEq ι]
    (A : SubMeas α ι) (f : α → β) (b : β) :
    (postprocess A f).outcome b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a := by
  classical
  simp only [postprocess]
  refine Finset.sum_congr ?_ ?_
  · ext a
    simp
  · intro a _
    rfl

/-- Postprocessing a submeasurement by the identity readout leaves it unchanged. -/
@[simp] theorem postprocess_id {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    postprocess A (fun a : α => a) = A := by
  classical
  refine SubMeas.ext ?_ rfl
  intro a
  simp only [postprocess, Finset.sum_filter]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _hb hba
    simp [hba]
  · intro ha
    simp at ha

/-- Transport a submeasurement along an equivalence of outcome types. -/
noncomputable def transport {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : SubMeas α ι) :
    SubMeas β ι where
  outcome := fun b => A.outcome (e.symm b)
  total := A.total
  outcome_pos := fun b => A.outcome_pos (e.symm b)
  sum_eq_total := (Equiv.sum_comp e.symm A.outcome).trans A.sum_eq_total
  total_le_one := A.total_le_one

@[simp] theorem transport_outcome {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : SubMeas α ι) (b : β) :
    (transport e A).outcome b = A.outcome (e.symm b) :=
  rfl

@[simp] theorem transport_total {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : SubMeas α ι) :
    (transport e A).total = A.total :=
  rfl

/-- Postprocessing after transporting outcomes along an equivalence agrees with
postprocessing the original submeasurement after precomposing the readout map
with the same equivalence. -/
theorem postprocess_transport {α β γ : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : SubMeas α ι) (f : β → γ) :
    postprocess (transport e A) f = postprocess A (fun a => f (e a)) := by
  classical
  refine SubMeas.ext ?_ rfl
  intro c
  have hsum :
      (∑ b : β, if f b = c then A.outcome (e.symm b) else (0 : MIPStarRE.Quantum.Op ι)) =
        ∑ a : α, if f (e a) = c then A.outcome a else (0 : MIPStarRE.Quantum.Op ι) := by
    simpa using
      (Equiv.sum_comp e
        (fun b => if f b = c then A.outcome (e.symm b) else (0 : MIPStarRE.Quantum.Op ι))).symm
  calc
    (postprocess (transport e A) f).outcome c
        = ∑ a : β, if f a = c then A.outcome (e.symm a) else (0 : MIPStarRE.Quantum.Op ι) := by
            simp [postprocess, SubMeas.transport, Finset.sum_filter]
    _ = ∑ a : α, if f (e a) = c then A.outcome a else (0 : MIPStarRE.Quantum.Op ι) := by
            simpa using hsum
    _ = (postprocess A (fun a => f (e a))).outcome c := by
            symm
            simp [postprocess, Finset.sum_filter]

/-- Naturality of postprocessing with respect to transport along equivalences on
both the source and target outcome alphabets. -/
theorem postprocess_transport_equiv {α β γ δ : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ι] [DecidableEq ι]
    (eα : α ≃ β) (eγ : γ ≃ δ) (A : SubMeas α ι)
    (f : α → γ) (g : β → δ)
    (h : ∀ a, g (eα a) = eγ (f a)) :
    postprocess (transport eα A) g = transport eγ (postprocess A f) := by
  classical
  refine SubMeas.ext ?_ rfl
  intro d
  have hsum :
      (∑ b : β, if g b = d then A.outcome (eα.symm b) else 0) =
        ∑ a : α, if g (eα a) = d then A.outcome a else 0 := by
    simpa using
      (Equiv.sum_comp eα
        (fun b : β => if g b = d then A.outcome (eα.symm b) else 0)).symm
  calc
    (postprocess (transport eα A) g).outcome d
        = ∑ b : β, if g b = d then A.outcome (eα.symm b) else 0 := by
            simp [postprocess, transport, Finset.sum_filter]
    _ = ∑ a : α, if g (eα a) = d then A.outcome a else 0 := hsum
    _ = ∑ a : α, if eγ (f a) = d then A.outcome a else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [h a]
    _ = ∑ a : α, if f a = eγ.symm d then A.outcome a else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases ha : f a = eγ.symm d
            · simp [ha]
            · have hne : eγ (f a) ≠ d := by
                intro hfd
                exact ha (by simpa using congrArg eγ.symm hfd)
              simp [ha, hne]
    _ = (transport eγ (postprocess A f)).outcome d := by
            simp [postprocess, transport, Finset.sum_filter]

/-- Postprocessing is functorial: postprocessing by `f` and then by `g`
agrees with a single postprocessing by the composite `g ∘ f`. -/
@[simp] theorem postprocess_comp {α β γ : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (fun a => g (f a)) := by
  classical
  refine SubMeas.ext ?_ rfl
  intro c
  calc
    (postprocess (postprocess A f) g).outcome c
        = ∑ b : β,
            if g b = c then
              ∑ a : α, if f a = b then A.outcome a else 0
            else 0 := by
              simp [postprocess, Finset.sum_filter]
    _ = ∑ b : β, ∑ a : α,
          if g b = c ∧ f a = b then
            A.outcome a
          else (0 : MIPStarRE.Quantum.Op ι) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            by_cases hgc : g b = c
            · simp [hgc]
            · simp [hgc]
    _ = ∑ a : α, ∑ b : β,
          if g b = c ∧ f a = b then
            A.outcome a
          else (0 : MIPStarRE.Quantum.Op ι) := by
            rw [Finset.sum_comm]
    _ = ∑ a : α,
          if g (f a) = c then A.outcome a else (0 : MIPStarRE.Quantum.Op ι) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hgc : g (f a) = c
            · rw [Finset.sum_eq_single (f a)]
              · simp [hgc]
              · intro b _ hb
                by_cases hfa : f a = b
                · exact (hb hfa.symm).elim
                · simp [hfa]
              · simp
            · have hzero :
                  (∑ b : β,
                    if g b = c ∧ f a = b then
                      A.outcome a
                    else (0 : MIPStarRE.Quantum.Op ι)) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro b _
                by_cases hfa : f a = b
                · subst b
                  simp [hgc]
                · simp [hfa]
              simp [hgc, hzero]
    _ = (postprocess A (fun a => g (f a))).outcome c := by
          simp [postprocess, Finset.sum_filter]

end SubMeas

namespace Measurement

/-- Transport a measurement along an equivalence of outcome types. -/
noncomputable def transport {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : Measurement α ι) :
    Measurement β ι where
  toSubMeas := SubMeas.transport e A.toSubMeas
  total_eq_one := A.total_eq_one

end Measurement

namespace ProjSubMeas



/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
theorem postprocess_outcome_proj {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  classical
  let fiber : Finset α := Finset.univ.filter fun a => f a = b
  calc
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b
      = (∑ a ∈ fiber, P.outcome a) * (∑ a' ∈ fiber, P.outcome a') := by
          simp [postprocess, fiber]
    _ = ∑ a ∈ fiber, ∑ a' ∈ fiber, P.outcome a * P.outcome a' := by
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
    _ = ∑ a ∈ fiber, ∑ a' ∈ fiber, if a' = a then P.outcome a else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          refine Finset.sum_congr rfl ?_
          intro a' ha'
          by_cases h : a' = a
          · subst h
            simp [P.proj]
          · have hne : a ≠ a' := fun h' => h h'.symm
            simp [ProjSubMeas.outcome_orthogonal P _ _ hne, h]
    _ = ∑ a ∈ fiber, P.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [fiber, ha]
    _ = (postprocess P.toSubMeas f).outcome b := by
          simp [postprocess, fiber]

end ProjSubMeas

namespace ProjMeas

/-- Transport a projective measurement along an equivalence of outcome types. -/
noncomputable def transport {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : ProjMeas α ι) :
    ProjMeas β ι where
  toMeasurement := Measurement.transport e A.toMeasurement
  proj := fun b => A.proj (e.symm b)

@[simp] theorem transport_trivialDistinguishedOutcome {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (e : α ≃ α) (a₀ : α) :
    transport e (trivialDistinguishedOutcome (ι := ι) a₀) =
      trivialDistinguishedOutcome (e a₀) := by
  classical
  ext a i j
  by_cases h : a = e a₀
  · simp [transport, Measurement.transport, SubMeas.transport,
      trivialDistinguishedOutcome, Measurement.trivialDistinguishedOutcome, h]
  · have hs : e.symm a ≠ a₀ := by
      intro hs
      apply h
      calc
        a = e (e.symm a) := by simp
        _ = e a₀ := by rw [hs]
    simp [transport, Measurement.transport, SubMeas.transport,
      trivialDistinguishedOutcome, Measurement.trivialDistinguishedOutcome, h, hs]

@[simp] theorem transport_toSubMeas {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : ProjMeas α ι) :
    (transport e A).toSubMeas = SubMeas.transport e A.toSubMeas :=
  rfl

/-- Postprocess a projective measurement along a relabeling of the outcome type.

The fiber of each output value is a sum of mutually orthogonal projectors, so
postprocessing preserves projectivity as well as completeness. -/
noncomputable def postprocess {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : ProjMeas α ι) (f : α → β) :
    ProjMeas β ι where
  toMeasurement := {
    toSubMeas := MIPStarRE.LDT.postprocess A.toSubMeas f
    total_eq_one := A.total_eq_one
  }
  proj := fun b => ProjSubMeas.postprocess_outcome_proj ⟨A.toSubMeas, A.proj⟩ f b

@[simp] theorem postprocess_toSubMeas {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : ProjMeas α ι) (f : α → β) :
    (postprocess A f).toSubMeas = MIPStarRE.LDT.postprocess A.toSubMeas f :=
  rfl

end ProjMeas



/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
noncomputable def completeSubMeas {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : Measurement (Option α) ι where
  toSubMeas := {
    outcome := fun
      | some a => A.outcome a
      | none => 1 - A.total
    total := 1
    outcome_pos := fun
      | some a => A.outcome_pos a
      | none => sub_nonneg.mpr A.total_le_one
    sum_eq_total := (Fintype.sum_option _).trans <|
      (congrArg (1 - A.total + ·) A.sum_eq_total).trans (sub_add_cancel 1 A.total)
    total_le_one := le_rfl
  }
  total_eq_one := rfl

/-- Constant indexed family taking the same submeasurement on every question. -/
def constSubMeasFamily {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    IdxSubMeas Unit α ι :=
  fun _ => A

/-- Average an indexed submeasurement family against a finite distribution.

The hypothesis `∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1` says that `𝒟` is a sub-probability
distribution (total mass at most `1`); this is all that is needed to keep the
averaged total operator below `1`. -/
noncomputable def averageIdxSubMeas {Question Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    SubMeas Outcome ι where
  outcome := fun a =>
    averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
  total :=
    averageOperatorOverDistribution 𝒟 (fun q => (A q).total)
  outcome_pos := fun a =>
    averageOperatorOverDistribution_nonneg 𝒟
      (fun q => (A q).outcome a) (fun q => (A q).outcome_pos a)
  sum_eq_total :=
    (averageOperatorOverDistribution_sum 𝒟 (fun q a => (A q).outcome a)).symm.trans
      (averageOperatorOverDistribution_congr 𝒟 _ _ fun q => (A q).sum_eq_total)
  total_le_one :=
    averageOperatorOverDistribution_le_one_of_weight_sum_le_one 𝒟
      (fun q => (A q).total) h𝒟 (fun q => (A q).total_le_one)


/-! ### Tensor-placement constructors -/

def mkLeftPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => leftTensor (ι₂ := ιB) (A.outcome a)
  total := leftTensor (ι₂ := ιB) A.total
  outcome_pos := fun a => leftTensor_nonneg (ι₂ := ιB) (A.outcome_pos a)
  sum_eq_total := (leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome).trans
    (congrArg (leftTensor (ι₂ := ιB)) A.sum_eq_total)
  total_le_one := leftTensor_le_one (ι₂ := ιB) A.total_le_one

def mkRightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => rightTensor (ι₁ := ιA) (A.outcome a)
  total := rightTensor (ι₁ := ιA) A.total
  outcome_pos := fun a => rightTensor_nonneg (ι₁ := ιA) (A.outcome_pos a)
  sum_eq_total := (rightTensor_finset_sum (ι₁ := ιA) Finset.univ A.outcome).trans
    (congrArg (rightTensor (ι₁ := ιA)) A.sum_eq_total)
  total_le_one := rightTensor_le_one (ι₁ := ιA) A.total_le_one

/-- Helper-level projection equation for left-placed outcomes. -/
@[simp] theorem mkLeftPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) (a : α) :
    (mkLeftPlacedSubMeas (ιB := ιB) A).outcome a =
      leftTensor (ι₂ := ιB) (A.outcome a) :=
  rfl

/-- Helper-level projection equation for left-placed totals. -/
@[simp] theorem mkLeftPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    (mkLeftPlacedSubMeas (ιB := ιB) A).total =
      leftTensor (ι₂ := ιB) A.total :=
  rfl

/-- Helper-level projection equation for right-placed outcomes. -/
@[simp] theorem mkRightPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) (a : α) :
    (mkRightPlacedSubMeas (ιA := ιA) A).outcome a =
      rightTensor (ι₁ := ιA) (A.outcome a) :=
  rfl

/-- Helper-level projection equation for right-placed totals. -/
@[simp] theorem mkRightPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    (mkRightPlacedSubMeas (ιA := ιA) A).total =
      rightTensor (ι₁ := ιA) A.total :=
  rfl

/-! ### Square bipartite lifts -/

/-- Lift a submeasurement to the left tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `A_a ⊗ I : Op (ι × ι)`. -/
def SubMeas.liftLeft {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) :=
  mkLeftPlacedSubMeas (ιB := ι) A

/-- Lift an indexed submeasurement family to the left tensor factor. -/
def IdxSubMeas.liftLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  fun q => mkLeftPlacedSubMeas (ιB := ι) (A q)

/-- Lift a projective submeasurement to the left tensor factor of a bipartite
space `ι × ι`. -/
def ProjSubMeas.liftLeft {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : ProjSubMeas α ι) : ProjSubMeas α (ι × ι) :=
  { toSubMeas := A.toSubMeas.liftLeft
    proj := fun a => (leftTensor_mul_leftTensor (A.outcome a) (A.outcome a)).trans
      (congrArg (leftTensor (ι₂ := ι)) (A.proj a)) }

/-- Lift a submeasurement to the right tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `I ⊗ A_a : Op (ι × ι)`. -/
def SubMeas.liftRight {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) :=
  mkRightPlacedSubMeas (ιA := ι) A

/-- Lift an indexed submeasurement family to the right tensor factor. -/
def IdxSubMeas.liftRight {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  fun q => mkRightPlacedSubMeas (ιA := ι) (A q)

/-! ### General bipartite placement -/

/-- Place a submeasurement on the left tensor factor of `ιA × ιB`. -/
def leftPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιA) :
    SubMeas α (ιA × ιB) :=
  mkLeftPlacedSubMeas (ιB := ιB) A

/-- Outcome operators of a left-placed submeasurement are left tensor placements. -/
@[simp] theorem leftPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) (a : α) :
    (leftPlacedSubMeas (ιB := ιB) A).outcome a =
      leftTensor (ι₂ := ιB) (A.outcome a) :=
  rfl

/-- The total operator of a left-placed submeasurement is a left tensor placement. -/
@[simp] theorem leftPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    (leftPlacedSubMeas (ιB := ιB) A).total =
      leftTensor (ι₂ := ιB) A.total :=
  rfl

/-- Place a submeasurement on the right tensor factor of `ιA × ιB`. -/
def rightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιB) :
    SubMeas α (ιA × ιB) :=
  mkRightPlacedSubMeas (ιA := ιA) A

/-- Outcome operators of a right-placed submeasurement are right tensor placements. -/
@[simp] theorem rightPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) (a : α) :
    (rightPlacedSubMeas (ιA := ιA) A).outcome a =
      rightTensor (ι₁ := ιA) (A.outcome a) :=
  rfl

/-- The total operator of a right-placed submeasurement is a right tensor placement. -/
@[simp] theorem rightPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    (rightPlacedSubMeas (ιA := ιA) A).total =
      rightTensor (ι₁ := ιA) A.total :=
  rfl

/-- Lift an indexed submeasurement family to the left tensor factor of
`ιA × ιB` (general bipartite placement). -/
def IdxSubMeas.placeLeft {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιA) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => mkLeftPlacedSubMeas (ιB := ιB) (A q)

/-- Lift an indexed submeasurement family to the right tensor factor of
`ιA × ιB` (general bipartite placement). -/
def IdxSubMeas.placeRight {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιB) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => mkRightPlacedSubMeas (ιA := ιA) (A q)

end MIPStarRE.LDT

end

end LIDT


