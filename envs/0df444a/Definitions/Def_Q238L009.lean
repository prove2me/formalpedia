-- Prove2me | Definitions.Def_Q238L009
-- name    : Q238L009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:14.012222+00:00
-- url     : https://prove2.me/theorems/6b273173-aa42-4a64-8748-8c82d27eb45f
-- title:
--   Definitions bundle Q238L009 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 77 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.colorTensor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.colors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.labelTensor`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.labels`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape.tensors`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rationalMarginal`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.rationalScore`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.matrix`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.start`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.fuelPoly`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.best`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricCost.connection`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricCost.cost`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.sourceSummand`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.bottomIndices`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Parameters.bound`, `OAI.MetricKMedianRecovery.BlueDP.atoms`, `OAI.MetricKMedianRecovery.BlueDP.initialTable`, `OAI.MetricKMedianRecovery.BlueDP.lookup`, `OAI.MetricKMedianRecovery.BlueDP.score0`, `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan.common`, `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan.large`, `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan.root`, `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan.small`, `OAI.MetricKMedianRecovery.Dyadic.Canonical.draw`, `OAI.MetricKMedianRecovery.EffectiveOpenability.forms`, `OAI.MetricKMedianRecovery.EffectiveOpenability.kindRows`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedIntegerDecide`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.integerDecide`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.state`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve`, `OAI.MetricKMedianRecovery.Ellipsoid.advance`, `OAI.MetricKMedianRecovery.Ellipsoid.badRow`, `OAI.MetricKMedianRecovery.Ellipsoid.boundedIntegerDecide` and 37 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_GlobalOuter`, `KMedianRecovery_Branching_BlueChoice`, `KMedianRecovery_Branching_BlueDPValue`, `KMedianRecovery_Branching_BlueMerge`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_BranchSeedLayout`, `KMedianRecovery_Branching_CategoricalOutput`, `KMedianRecovery_Branching_CategoricalResources`, `KMedianRecovery_Branching_CategoricalScore`, `KMedianRecovery_Encoding_Matrix`, `KMedianRecovery_Encoding_RationalBottomIndices`, `KMedianRecovery_Encoding_RationalConstants`, `KMedianRecovery_Encoding_RationalInflatedShape`, `KMedianRecovery_Encoding_RationalMenus`, `KMedianRecovery_Geometry_LocalFuel`, `KMedianRecovery_Geometry_MetricCost2`, `KMedianRecovery_Recovery_BoundRow`, `KMedianRecovery_Recovery_CoordinateRow`, `KMedianRecovery_Recovery_DataHeight`, `KMedianRecovery_Recovery_Entry`, `KMedianRecovery_Recovery_EnumeratedRow`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_InitialState`, `KMedianRecovery_Recovery_KindRows`, `KMedianRecovery_Recovery_LowCandidate`, `KMedianRecovery_Recovery_ReverseRow`, `KMedianRecovery_Recovery_Row`, `KMedianRecovery_Recovery_State`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerParameters`, `KMedianRecovery_Sampling_SamplingPotential`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L000`, `Q238L001`, `Q238L002`, `Q238L003` and `Q238L004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L018`, `Q238L019` and `Q238L020`; the statements `OAI.MetricKMedianRecovery.Ellipsoid.advance_pos_lower_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238r`, `OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238r` and `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238r`; the proofs of `OAI.MetricKMedianRecovery.Ellipsoid.advance_pos_lower_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.selectFace_spec_s238r` and `OAI.MetricKMedianRecovery.IntegralAssembly.gamma_pos_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L000
import Definitions.Def_Q238L001
import Definitions.Def_Q238L002
import Definitions.Def_Q238L003
import Definitions.Def_Q238L004

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

def Row.value {n : ℕ} (r : Row n) (x : Fin n → ℚ) : ℚ := ∑ i, r.coeff i * x i

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EnumeratedRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
variable {V R : Type*} [Fintype V] {n : ℕ}

def Form.enumeratedRow (e : Fin n ≃ V) (f : Form V) : Row n :=
  ⟨fun i => f.coeff (e i),-f.constant⟩

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability
variable {D X : Type*} [Fintype D] [DecidableEq D] [DecidableEq X]

def forms (d : X → D → ℚ) (F W : Finset X) (v z lam eta : ℚ) (i : X) :
    Kind D W F → Form (Variables D F)
  | .lower j => if active d v z W j then (Form.const z).sub (bid F j) else Form.const 0
  | .upper j => if active d v z W j then (bid F j).sub (Form.const ((1+v^2)*z)) else Form.const 0
  | .cap j f => if active d v z W j then (bid F j).sub (Form.const ((1-3*v)*d f j)) else Form.const 0
  | .far j => if active d v z W j ∧ v*z<d i j then (bid F j).sub (Form.const z) else Form.const 0
  | .payment => (Form.const (lam-(Fintype.card D:ℚ)*eta)).sub (payment d F W v z i)
  | .slackZero f a j => if active d v z W a then (Form.const 0).sub (slack F f a j) else Form.const 0
  | .slackTerm f a j => if active d v z W a then (dual d F W v z f a j).sub (slack F f a j) else Form.const 0
  | .dual f a => if active d v z W a then (Form.sum (fun j => slack F f a j)).sub (Form.const lam) else Form.const 0

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability

section
open RationalOpenability
variable {D W F : Type*}

def kindRows (ds : List D) (ws : List W) (fs : List F) : List (Kind D W F) :=
  ds.map .lower ++ ds.map .upper ++
    ds.flatMap (fun j => ws.map (Kind.cap j)) ++ ds.map .far ++ [.payment] ++
    fs.flatMap (fun f => ds.flatMap (fun a => ds.map (Kind.slackZero f a))) ++
    fs.flatMap (fun f => ds.flatMap (fun a => ds.map (Kind.slackTerm f a))) ++
    fs.flatMap (fun f => ds.map (Kind.dual f))

end

open RationalOpenability

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalInflatedShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def rationalStepCenter (H : Matrix V V ℚ) (a c : V → ℚ) : V → ℚ :=
  c-(1/(((Fintype.card V:ℚ)+1)*rationalRootUpper (32*Fintype.card V) (rationalQuad H a))) • (H *ᵥ a)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

def badRow {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) : Option (Row n) :=
  rows.find? (fun r => decide (r.bound < r.value c))

def advance {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : State n :=
  match badRow rows S.center with
  | none => S
  | some r => if r.coeff=0 then S else
      ⟨rationalStepShape D S.shape r.coeff,rationalStepCenter S.shape r.coeff S.center⟩

def iterate {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : ℕ → State n
  | 0 => S
  | t+1 => advance D rows (iterate D rows S t)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

def weakSolve {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) : Option (Fin n → ℚ) :=
  let T := iterationBudget n p s
  let c := (iterate (gridDenominator n T) rows (initialState n R) T).center
  if badRow rows c=none then some c else none

def relaxedRow {n : ℕ} (eps : ℚ) (r : Row n) : Row n := ⟨r.coeff,r.bound+eps⟩

def relaxedRows {n : ℕ} (eps : ℚ) (rows : List (Row n)) : List (Row n) := rows.map (relaxedRow eps)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def boundedRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : List (Row n) :=
  List.ofFn (fun r => integerRow (A r) (b r)) ++
  List.ofFn (fun i => integerRow (boundedMatrix A (.inr (true,i))) B) ++
  List.ofFn (fun i => integerRow (boundedMatrix A (.inr (false,i))) B)

def integerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : Bool :=
  (weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B))
    ((n:ℚ)*(B+1)) (precisionLog m n H) (radiusLog n B)).isSome

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DataHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

def boundedIntegerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : Bool :=
  integerDecide (padMatrix A) b B (dataHeight (padMatrix A) b B)

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.Ellipsoid
open Matrix PolytopeCertificate RationalLinearFeasibility
open scoped BigOperators

def rowEntries {n : ℕ} (q : Row n) : Option (Fin n) → ℚ := Option.elim' q.bound q.coeff

def clearedMatrix {n : ℕ} (rows : List (Row n)) : Matrix (Fin rows.length) (Fin n) ℤ :=
  fun r j => rowNumerator (rowEntries rows[r]) (some j)

def clearedBounds {n : ℕ} (rows : List (Row n)) : Fin rows.length → ℤ :=
  fun r => rowNumerator (rowEntries rows[r]) none

def boundedRationalDecide {n : ℕ} (rows : List (Row n)) (B : ℕ) : Bool :=
  boundedIntegerDecide (clearedMatrix rows) (clearedBounds rows) B

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ReverseRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def reverseRow {n : ℕ} (q : Row n) : Row n := ⟨fun j => -q.coeff j,-q.bound⟩

def faceRows {n : ℕ} (rows picked : List (Row n)) : List (Row n) :=
  rows ++ picked ++ picked.map reverseRow

def selectFace {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    List (Row n) → List (Row n) → List (Row n)
  | [], picked => picked
  | q::todo, picked =>
    if boundedRationalDecide (faceRows rows (q::picked)) B then
      selectFace rows B todo (q::picked)
    else selectFace rows B todo picked

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoordinateRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def coordinateRow {n : ℕ} (i : Fin n) (c b : ℚ) : Row n :=
  ⟨fun j => if j=i then c else 0,b⟩

def boxRows (n B : ℕ) : List (Row n) :=
  List.ofFn (fun i => coordinateRow i 1 B) ++ List.ofFn (fun i => coordinateRow i (-1) B)

def withBox {n : ℕ} (rows : List (Row n)) (B : ℕ) := rows++boxRows n B

def finalFace {n : ℕ} (rows : List (Row n)) (B : ℕ) : List (Row n) :=
  selectFace (withBox rows B) B (withBox rows B) []

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

def sourceSummand {m d : ℕ} (distance : Fin m → Fin d → ℚ) (W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (j : Fin d) : ℚ :=
  if EffectiveOpenability.active distance v z W j then
    if distance i j≤v*z then -((1-3*v)*distance i j)
    else max (z-(1-3*v)*distance i j) 0
  else max ((1-3*v)*RationalOpenability.nearest distance W j-(1-3*v)*distance i j) 0
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

def state {n : ℕ} (S : State n) : State n := ⟨matrix S.shape,vector S.center⟩
@[simp] lemma state_eq {n : ℕ} (S : State n) : state S=S := by
  cases S
  simp only [state,matrix_eq,vector_eq]

def iterate {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : ℕ → State n
  | 0 => state S
  | t+1 => state (advance D rows (iterate D rows S t))

@[simp] lemma iterate_eq {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) (t : ℕ) :
    iterate D rows S t=Ellipsoid.iterate D rows S t := by
  induction t with
  | zero => simp only [iterate,Ellipsoid.iterate,state_eq]
  | succ t ih => simp only [iterate,Ellipsoid.iterate,state_eq,ih]

def weakSolve {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) : Option (Fin n → ℚ) :=
  let T := iterationBudget n p s
  let c := (iterate (gridDenominator n T) rows (initialState n R) T).center
  if badRow rows c=none then some c else none
@[simp] lemma weakSolve_eq {n : ℕ} (rows : List (Row n)) (R : ℚ) (p s : ℕ) :
    weakSolve rows R p s=Ellipsoid.weakSolve rows R p s := by
  simp only [weakSolve,Ellipsoid.weakSolve,iterate_eq]

def integerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : Bool :=
  (weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B))
    ((n:ℚ)*(B+1)) (precisionLog m n H) (radiusLog n B)).isSome
@[simp] lemma integerDecide_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    integerDecide A b B H=Ellipsoid.integerDecide A b B H := by
  simp only [integerDecide,Ellipsoid.integerDecide,weakSolve_eq]

def boundedIntegerDecide {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) : Bool :=
  integerDecide (padMatrix A) b B (dataHeight (padMatrix A) b B)
@[simp] lemma boundedIntegerDecide_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    boundedIntegerDecide A b B=Ellipsoid.boundedIntegerDecide A b B := by
  simp only [boundedIntegerDecide,Ellipsoid.boundedIntegerDecide,integerDecide_eq]

def boundedRationalDecide {n : ℕ} (rows : List (Row n)) (B : ℕ) : Bool :=
  boundedIntegerDecide (clearedMatrix rows) (clearedBounds rows) B
@[simp] lemma boundedRationalDecide_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    boundedRationalDecide rows B=Ellipsoid.boundedRationalDecide rows B := by
  simp only [boundedRationalDecide,Ellipsoid.boundedRationalDecide,boundedIntegerDecide_eq]

def selectFace {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    List (Row n) → List (Row n) → List (Row n)
  | [],picked => picked
  | q::todo,picked =>
    if boundedRationalDecide (faceRows rows (q::picked)) B then
      selectFace rows B todo (q::picked)
    else selectFace rows B todo picked
@[simp] lemma selectFace_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) (todo picked : List (Row n)) :
    selectFace rows B todo picked=Ellipsoid.selectFace rows B todo picked := by
  induction todo generalizing picked with
  | nil => rfl
  | cons q todo ih => simp only [selectFace,Ellipsoid.selectFace,boundedRationalDecide_eq,ih]

def finalFace {n : ℕ} (rows : List (Row n)) (B : ℕ) : List (Row n) :=
  selectFace (withBox rows B) B (withBox rows B) []
@[simp] lemma finalFace_eq {n : ℕ} (rows : List (Row n)) (B : ℕ) :
    finalFace rows B=Ellipsoid.finalFace rows B := selectFace_eq _ _ _ _

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Entry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Maximal (loc : D → X) (F Q : Finset X) (v z lam : ℝ) : Prop :=
  ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i

end PhaseSequence
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

def Plan.root : Plan X → X
  | .free i _ => i
  | .paid _ _ i => i

def Plan.common (H : List X) : Plan X → List X
  | .free _ _ => H
  | .paid C T _ => C++T

def Plan.small (T U : List (List X)) : Plan X → List (List X)
  | .free _ _ => U
  | .paid _ _ _ => T

def Plan.large (T U : List (List X)) : Plan X → List (List X)
  | .free _ _ => T
  | .paid _ _ _ => U

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBottomIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordList BinaryArithmetic
def bottomIndices {r : ℕ} (v : Fin r→ℚ) (k : ℕ) : List ℕ :=
  (((Finset.univ.image (ranking v)).sort (·≤·)).take k).map (fun p=>(ofLex p).2)
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalMenus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def leafValues (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) : List ℚ :=
  s.leaves.map (fun z=>δ w z.1+z.2)
def nearestLeaf (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) : Option ℚ :=
  if s.leaves=[] then none else some (RationalMin.minimum (leafValues δ s w))
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
def menuRadius (D : Finset (Fin n)) (P κ : ℚ) (m M E J : ℕ) (s : State n) (w : Fin n) :
    Sampling.Entry M E J → Option ℚ
  | .inl j=>some ((j.val+1)*κ*BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w))
  | .inr (.inl e)=>(nearestLeaf δ s w).map (fun r=>r/(1+κ)^e.val)
  | .inr (.inr j)=>some ((j.val+1)*κ*BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w))
end Metric
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
noncomputable def clientWeight (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) : ℚ :=
  max 0 (reference δ S Δ s w)
noncomputable def totalWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) : ℚ :=
  ∑ w∈D,clientWeight δ S Δ s w
noncomputable def transitionWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) : ℚ :=
  match s with
  | none=>if a=Sum.inl () then 1 else 0
  | some s=>if 0<totalWeight δ D S Δ s then
      match a with
      | .inl _=>0
      | .inr (.inl w)=>clientWeight δ S Δ s w/(2*totalWeight δ D S Δ s)
      | .inr (.inr (w,e))=>clientWeight δ S Δ s w/(2*totalWeight δ D S Δ s)*menuWeight M E J e
    else if a=Sum.inl () then 1 else 0
def State.remove (s : State n) (v : Fin n) : State n := ⟨insert v s.deleted,s.leaves⟩
def State.add (s : State n) (w : Fin n) (R : ℚ) : State n := ⟨s.deleted,s.leaves++[(w,R)]⟩
def retain (m : ℕ) (s : State n) : Option (State n) :=
  if s.leaves.length ≤ m ∧ s.deleted.card ≤ m then some s else none
noncomputable def update (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ)
    (m M E J : ℕ) (s : Option (State n)) (a : Sampling.Action D M E J) : Option (State n) :=
  match s with
  | none=>none
  | some s=>if 0<totalWeight δ D S Δ s then
      match a with
      | .inl _=>none
      | .inr (.inl w)=>if h : chosenId δ S Δ s w<n then retain m (s.remove ⟨chosenId δ S Δ s w,h⟩) else none
      | .inr (.inr (w,e))=>match menuRadius δ D P κ m M E J s w e with
        | none=>none
        | some R=>if (F.filter (fun v=>δ w.val v≤R)).Nonempty then retain m (s.add w R) else none
    else none
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic.Canonical
open FiniteSampling
variable {A : Type*}
variable [Fintype A] [DecidableEq A]
noncomputable def draw (p : A→ℝ) (b : ℕ) (default : A) (as : List A) (bits : Fin b→Bool) : A :=
  select default (list p b as) (Categorical.uniformBits b bits).val
end MetricKMedianRecovery.Dyadic.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordList BinaryArithmetic
variable {q a T L : ℕ}
def rationalMarginal (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (e : Fin q) (s : Fin a→Fin T) : ℚ :=
  let S:=Categorical.draw a (Function.update r (part e) (fun _=>none)) s ∅
  G (insert e S)-G S
def rationalScore (G : Finset (Fin q)→ℚ) (part : Fin q→Fin a)
    (r : Fin a→Fin T→Option (Fin q)) (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) : ℚ :=
  (∑ l,rationalMarginal G part r e (seed e l)) / L
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordList
variable {n : ℕ}
def connection (δ : Fin n→Fin n→ℚ) (S : Finset (Fin n)) (x : Fin n) : ℚ :=
  RationalMin.minimum (List.ofFn (fun j:Fin S.card=>δ x (SortedIndex.enum S j)))
def cost (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) : ℚ :=
  ∑ i:Fin D.card,connection δ S (SortedIndex.enum D i)
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordList
variable {n : ℕ}
def best (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) : Finset (Fin n) :=
  OrderedMaximum.run (fun U=> -BinaryMetricCost.cost δ D U) S xs
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Explicit
open FiniteSampling

lemma steps_upper (a : ℕ) : steps a ≤ 4096*(a+2)^2 := by
  have hh := pow_size_bound (a+1)
  have hs:=Nat.pow_le_pow_left hh 2
  unfold steps exponent
  rw [pow_add,show 2*(a+1).size=(a+1).size*2 by omega,pow_mul]
  norm_num
  nlinarith
attribute [local irreducible] steps exponent

attribute [local irreducible] samples
end MetricKMedianRecovery.Categorical.Explicit

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape
open BinarySeed
variable (q a b L : ℕ)

def tensors : (Categorical.BinaryOracleIndex (Fin q) a b L→Bool)≃
    Tensor [2^b,q,L,a] b × Tensor [a] b where
  toFun bits := (fun t e l j i=>bits (.inl (t,e,l,j),i),fun j i=>bits (.inr j,i))
  invFun s := fun idx=>match idx.1 with
    | .inl (t,e,l,j)=>s.1 t e l j idx.2
    | .inr j=>s.2 j idx.2
  left_inv bits := by
    funext idx
    rcases idx with ⟨idx,i⟩
    rcases idx with ⟨t,e,l,j⟩ | j <;> rfl
  right_inv s := by rfl

def layout : (Fin (M q a b L+K a b)→Bool)≃(Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :=
  (tensorPair q a b L).trans (tensors q a b L).symm

def raw (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) : List Bool :=
  BinarySeed.raw ((tensors q a b L bits).1)++BinarySeed.raw ((tensors q a b L bits).2)
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
lemma value_choose (x y : Candidate A) : value (choose x y)=min (value x) (value y) := by
  cases x with
  | none=>simp [choose,value]
  | some x=>
    cases y with
    | none=>simp [choose,value]
    | some y=>
      dsimp [choose,value]
      split_ifs with h
      · apply (min_eq_left ?_).symm
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast h)
      · apply (min_eq_right ?_).symm
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast (le_of_not_ge h))
lemma fold_value (xs : List (Candidate A)) (s : Candidate A) :
    value (xs.foldl choose s)=min (value s) ((xs.map value).foldr min ⊤) := by
  induction xs generalizing s with
  | nil=>simp
  | cons x xs ih=>simp only [List.foldl_cons,ih,value_choose,List.map_cons,List.foldr_cons,min_assoc]
lemma select_value (xs : List (Candidate A)) : value (select xs)=((xs.map value).foldr min ⊤) := by
  unfold select
  rw [fold_value]
  change min ⊤ _=_
  exact min_top_left _
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueDPValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A L : Type*}
lemma select_finset [DecidableEq L] (xs : List L) (f : L→Candidate A) :
    value (select (xs.map f))=xs.toFinset.inf (fun x=>value (f x)) := by
  rw [select_value,List.map_map]
  exact list_min_inf xs _

variable [LinearOrder L]
lemma enumBlocks_set (U : Finset L) : (enumBlocks U).toFinset=BlueSubsetDP.blocks U := by
  ext V
  simp only [enumBlocks,List.mem_toFinset,List.mem_filter,List.mem_map,List.mem_sublists,decide_eq_true_eq,BlueSubsetDP.mem_blocks]
  constructor
  · rintro ⟨⟨xs,hxs,rfl⟩,hx⟩
    refine ⟨Finset.nonempty_iff_ne_empty.mpr hx,?_⟩
    intro l hl
    exact (Finset.mem_sort (·≤·)).mp (hxs.subset (List.mem_toFinset.mp hl))
  · intro h
    refine ⟨⟨(U.sort (·≤·)).filter (fun l=>l∈V),List.filter_sublist,?_⟩,h.1.ne_empty⟩
    ext l
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨h.2 hv,hv⟩⟩

end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {A : Type*}
def score0 : Candidate (List A)→ℚ := fun x=>x.map Prod.fst |>.getD 0
def atoms : Candidate (List A)→List A := fun x=>x.map Prod.snd |>.getD []
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
def lookup (U : Finset L) : Table L A → Candidate (List A)
  | []=>none
  | (V,x)::xs=>if U=V then x else lookup U xs
def initialTable (U : Finset L) : Table L A := (states U).map (fun V=>(V,if V=∅ then some (0,[]) else none))
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed
def colors (n : ℕ) : (Fin (colorCount n)→Bool)≃(Fin n→Fin 4) :=
  (tensorEquiv [n] 2).trans (Equiv.arrowCongr (Equiv.refl (Fin n)) (Categorical.uniformBits 2))
def labels (n b : ℕ) : (Fin (labelCount n b)→Bool)≃(Fin n→Fin (ColorLabel.labelRange b)) :=
  (tensorEquiv [n] (Nat.clog 2 b)).trans (Equiv.arrowCongr (Equiv.refl (Fin n)) (Categorical.uniformBits (Nat.clog 2 b)))
def colorTensor {n : ℕ} (s : Fin n→Fin 4) : Tensor [n] 2 := fun i=>(Categorical.uniformBits 2).symm (s i)
def labelTensor {n b : ℕ} (s : Fin n→Fin (ColorLabel.labelRange b)) : Tensor [n] (Nat.clog 2 b) :=
  fun i=>(Categorical.uniformBits (Nat.clog 2 b)).symm (s i)
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LowCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling FiniteSampling

noncomputable def gamma : ℝ := min (3/100) (strictnessGap (200*countConstant (1/100))/100)

end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
noncomputable def bound : Polynomial ℕ := X+C (⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(X+2)^2
attribute [local irreducible] bound
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
def State.initial : State n := ⟨∅,[]⟩
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
noncomputable def next (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (s : Option (State n)) (seed : Fin b→Bool) : Option (State n) :=
  update δ D F S Δ P κ m M E J s (Dyadic.Canonical.draw
    (fun a=>(transitionWeight δ D S Δ M E J s a:ℝ)) b (Sum.inl ()) (actions D M E J) seed)
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalFuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordList BinaryArithmetic RationalLeaves Polynomial
noncomputable def fuelPoly : Polynomial ℕ :=
  C (⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(X+2)^3
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
noncomputable def countRat : ℚ := 10+(600/(1/100:ℚ))*2^(Anchoring.rounds (1/100)-1)
noncomputable def gapRat : ℚ := (1/(200*(200*countRat+2)))^2/100
noncomputable def gammaRat : ℚ := min (3/100) (gapRat/100)
end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordList BinaryArithmetic
noncomputable abbrev matrix (I : RationalMetricInput) (M : ℚ) :=
  BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate I.distance)
    ((IntegralAssembly.gammaRat/16)*M/I.clients.card) (Rounding.cap I.clients.card (IntegralAssembly.gamma/16))
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordList LocalSearch Completion
noncomputable def start (I : RationalMetricInput) : Finset (Fin I.pointCount) := Canonical.pad I.facilities ∅ 1
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end


