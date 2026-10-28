-- Prove2me | Definitions.Def_OAIQ072A001
-- name    : OAIQ072A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:14:52.822408+00:00
-- url     : https://prove2.me/theorems/e4d8ab37-737e-4e59-b43f-ca591a8bb340
-- title:
--   Definitions bundle OAIQ072A001 of the split of OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 24 definitions, 1 inductive type or structure, 4 instances and 4 theorems. The definitions and types are `OAI.SKGap.LogDet.detMultilinear`, `OAI.SKGapCutoff.Recipe.LocalConstants`, `OAI.SKGapCutoff.Recipe.LocalConstants.argument`, `OAI.SKGapCutoff.Recipe.LocalConstants.fieldCost`, `OAI.SKGapCutoff.Recipe.LocalConstants.normBudget`, `OAI.SKGapCutoff.Recipe.LocalConstants.row`, `OAI.SKGapCutoff.Recipe.LocalConstants.sourceCost`, `OAI.SKGapCutoff.Recipe.LocalConstants.startedFieldCost`, `OAI.SKGapCutoff.Recipe.LocalConstants.startedNormBudget`, `OAI.SKGapCutoff.Recipe.LocalConstants.startedSourceCost`, `OAI.SKGapCutoff.Recipe.LocalConstants.traceCost`, `OAI.SKGapCutoff.Recipe.LocalConstants.withCoefficient`, `OAI.SKGapCutoff.Recipe.cutoffDeficit`, `OAI.SKGapCutoff.Recipe.cutoffWeight`, `OAI.SKGapCutoff.Recipe.errorBudget`, `OAI.SKGapCutoff.Recipe.initialTraceBudget`, `OAI.SKGapCutoff.Recipe.initialTraceFactor`, `OAI.SKGapCutoff.Recipe.physicalNormBound`, `OAI.SKGapCutoff.Recipe.recipeBudget`, `OAI.SKGapCutoff.Recipe.recipeCost`, `OAI.SKGapCutoff.Recipe.recipeNormTail`, `OAI.SKGapCutoff.Recipe.residualScalarCutoff`, `OAI.SKGapCutoff.Recipe.startedBudget`, `OAI.SKGapCutoff.Recipe.startedTraceBudget`, `OAI.SKGapCutoff.Recipe.traceBudget`.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKGap_Gaussian_GaussianRecipeEvent`, `SKGap_Localization_CoefficientInputBridge`, `SKGap_Localization_RecipeBound`, `SKGap_Localization_SelectionPartition`, `SKGap_Localization_SmoothSelection`, `SKGap_Localization_StartedSmall`, `SKGap_Matrix_FixedNormRecipeEvent`, `SKGap_Matrix_LiteralTrace`, `SKGap_Matrix_MatrixLogDet`, `SKGap_Matrix_PrimitiveTrace`, `SKGap_Matrix_RecipeTraceBudget`, `SKGap_Matrix_StartedTraceBudget`, `SKGap_Matrix_StartedWordClosure`, `SKGap_Stability_OrdinaryClosure`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ072A002`; the statement `OAI.SKGapCutoff.Recipe.disorder_norm_event`; the proofs of `OAI.SKGapCutoff.Recipe.disorder_norm_event`, `OAI.SKGap.actual_logdet_mean` and `OAI.SKGap.field_logdet_uniform`.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ072_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Matrix

def recipeBudget (c S : ℝ) (a : ℕ) : ℝ := c*(S+∑b:Fin a,recipeBudget c S b)
termination_by a

def recipeCost (A R L P j : ℝ) (d : ℕ) : ℝ :=
  (A+3*R)*(1+L+|j| *((d:ℝ)*(1+3*P)+1))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimitiveTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix
variable {n : ℕ}

def errorBudget (R : ℝ) (Cs Cf : ℕ→ℝ) (a : ℕ) : ℝ×ℝ :=
  let S:=Cs a+∑b:Fin a,(errorBudget R Cs Cf b).2
  (S,S+R*(∑b:Fin a,(errorBudget R Cs Cf b).1)+Cf a)
termination_by a

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeTraceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def traceBudget (c k : ℝ) (W : ℕ→ℝ) (a : ℕ) : ℝ := c*W a+k*∑b:Fin a,traceBudget c k W b
termination_by a

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Matrix

structure LocalConstants where
  A : ℝ
  C : ℝ
  P : ℝ
  L : ℝ
  E : ℝ
  V : ℝ
  S : ℝ
  one_le_A : 1≤A
  C_nonneg : 0≤C
  C_le_A : C≤A
  P_nonneg : 0≤P
  L_nonneg : 0≤L
  E_nonneg : 0≤E
  V_nonneg : 0≤V
  S_nonneg : 0≤S

namespace LocalConstants
variable (c : LocalConstants)
def argument (d : ℕ) : ℝ := (d:ℝ)*c.P+c.V
def row (d : ℕ) : ℝ := c.C*c.argument d
def normBudget (j : ℝ) (d : ℕ) : ℕ→ℝ := recipeBudget (recipeCost c.A (c.row d) c.L c.P j d) c.S
def traceCost (d : ℕ) : ℝ :=
  c.V+4*((2*(d:ℝ)*c.P)^2+((d:ℝ)*c.P)*c.V+c.V^2)+2*(2*(d:ℝ)*c.P+(d:ℝ)*c.P+c.V)
def sourceCost (j : ℝ) (d s : ℕ) (a : ℕ) : ℝ :=
  (s:ℝ)*(c.C*c.S*c.traceCost d)+(∑b:Fin a,c.C*c.normBudget j d b*c.traceCost d)+
    (d:ℝ)*(c.normBudget j d a*c.E)
def fieldCost (j : ℝ) (d : ℕ) (a : ℕ) : ℝ :=
  (d:ℝ)*(|j| *(c.normBudget j d a*c.E))+
    |j| *((d:ℝ)*(c.normBudget j d a*(1+2*c.P))+(∑b:Fin a,3*c.normBudget j d b*c.row d))
end LocalConstants

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientInputBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ σ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ] [Fintype τ]

namespace LocalConstants
def withCoefficient (c : LocalConstants) (K S : ℝ) (hK : 1≤K) (hS : 0≤S) : LocalConstants :=
  {c with A:=K,C:=K,S:=S,one_le_A:=hK,C_nonneg:=le_trans (by norm_num) hK,C_le_A:=le_rfl,S_nonneg:=hS}
end LocalConstants

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open MeasureTheory ProbabilityTheory Real Set

def recipeNormTail (j : ℝ) (n : ℕ) : ENNReal :=
  ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
    ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_FixedNormRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe

def physicalNormBound (j : ℝ) : ℝ := 2*Real.sqrt j+1+1

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SmoothSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal ContDiff
namespace SKGapCutoff.Recipe
variable {n : ℕ}

def residualScalarCutoff (u : ℝ) : ℝ :=
  Real.smoothTransition ((1-u)*4/3)*Real.smoothTransition ((1+u)*4/3)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SelectionPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ}

def cutoffWeight (C : ℕ→ℝ) (k : ℕ) : ℝ := C k*∏i∈Finset.range k,(1-C i)
def cutoffDeficit (C : ℕ→ℝ) (d : ℕ) : ℝ := 1-∑k∈Finset.range d,cutoffWeight C k

universe u

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
variable {n : ℕ}

def startedBudget (c S B : ℝ) (a : ℕ) : ℝ :=
  c*(S+∑b:Fin a,startedBudget c S B b)+B
termination_by a
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Matrix

namespace LocalConstants
variable (c : LocalConstants)
def startedNormBudget (j : ℝ) (d : ℕ) (B : ℝ) : ℕ→ℝ := startedBudget (recipeCost c.A (c.row d) c.L c.P j d) c.S B
def startedSourceCost (j : ℝ) (d s : ℕ) (B : ℝ) (a : ℕ) : ℝ :=
  (s:ℝ)*(c.C*c.S*c.traceCost d)+(∑b:Fin a,c.C*c.startedNormBudget j d B b*c.traceCost d)+
    (d:ℝ)*(c.startedNormBudget j d B a*c.E)
def startedFieldCost (j : ℝ) (d : ℕ) (B : ℝ) (a : ℕ) : ℝ :=
  (d:ℝ)*(|j| *(c.startedNormBudget j d B a*c.E))+
    |j| *((d:ℝ)*(c.startedNormBudget j d B a*(1+2*c.P))+(∑b:Fin a,3*c.startedNormBudget j d B b*c.row d))
end LocalConstants

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiteralTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
variable {n : ℕ}

def initialTraceFactor (Q T B : ℝ) : ℝ :=
  (T+B)+4*(Q^2+T*(T+B)+(T+B)^2)+2*(Q+T+(T+B))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixLogDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.LogDet
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def detMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by change Continuous (fun M : Matrix ι ι ℝ => M.det); fun_prop }

end SKGap.LogDet
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedTraceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap
variable {n : ℕ}

def startedTraceBudget (c k : ℝ) (W : ℕ→ℝ) (B : ℝ) (a : ℕ) : ℝ :=
  c*W a+k*∑b:Fin a,startedTraceBudget c k W B b+B
termination_by a
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedWordClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap
variable {n : ℕ}

def initialTraceBudget (j A B Q : ℝ) : ℝ := (2+|j| *A)*(B*((1+|j|)*Q))+|j| *B*Q
end SKGapCutoff.Recipe

end
end

end OAI
end


