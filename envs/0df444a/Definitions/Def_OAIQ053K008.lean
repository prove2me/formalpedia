-- Prove2me | Definitions.Def_OAIQ053K008
-- name    : OAIQ053K008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:54:16.142185+00:00
-- url     : https://prove2.me/theorems/eea423a2-6f0b-42ef-9fb3-a23bd673703f
-- title:
--   Definitions bundle OAIQ053K008 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 151 declarations of OpenAI's Lean: 94 definitions, 13 inductive types or structures, 4 instances and 40 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Input`, `OAI.MetricKMedian.LPBinary.Input.scale`, `OAI.MetricKMedian.LPBinary.baseBound`, `OAI.MetricKMedian.LPBinary.exponentBound`, `OAI.MetricKMedian.LPBinary.gradientBound`, `OAI.MetricKMedian.LPBinary.heightBound`, `OAI.MetricKMedian.LPBinary.heightPolynomial`, `OAI.MetricKMedian.LPBinary.stepsBound`, `OAI.MetricKMedian.LPBinary.stepsPolynomial`, `OAI.MetricKMedian.PCP.Advice`, `OAI.MetricKMedian.PCP.Advice.BitIndex`, `OAI.MetricKMedian.PCP.Advice.bitsEquiv`, `OAI.MetricKMedian.PCP.Advice.get`, `OAI.MetricKMedian.PCP.AlphabetReduction.EdgeSample`, `OAI.MetricKMedian.PCP.AlphabetReduction.Interior`, `OAI.MetricKMedian.PCP.AlphabetReduction.PaddedNode`, `OAI.MetricKMedian.PCP.AlphabetReduction.PaddedPosition`, `OAI.MetricKMedian.PCP.AlphabetReduction.Position`, `OAI.MetricKMedian.PCP.AlphabetReduction.RelationInterior`, `OAI.MetricKMedian.PCP.AlphabetReduction.Relations`, `OAI.MetricKMedian.PCP.AlphabetReduction.Test`, `OAI.MetricKMedian.PCP.AlphabetReduction.UniversalInterior`, `OAI.MetricKMedian.PCP.AlphabetReduction.UniversalPad`, `OAI.MetricKMedian.PCP.AlphabetReduction.binary`, `OAI.MetricKMedian.PCP.AlphabetReduction.decoded`, `OAI.MetricKMedian.PCP.AlphabetReduction.firstTable`, `OAI.MetricKMedian.PCP.AlphabetReduction.localMap`, `OAI.MetricKMedian.PCP.AlphabetReduction.reduced`, `OAI.MetricKMedian.PCP.AlphabetReduction.relation`, `OAI.MetricKMedian.PCP.AlphabetReduction.secondTable`, `OAI.MetricKMedian.PCP.AlphabetReduction.vertexTable`, `OAI.MetricKMedian.PCP.BinaryCSP`, `OAI.MetricKMedian.PCP.Bit`, `OAI.MetricKMedian.PCP.BitVector`, `OAI.MetricKMedian.PCP.FourCSP`, `OAI.MetricKMedian.PCP.FourQuery`, `OAI.MetricKMedian.PCP.FourQuery.Rejects`, `OAI.MetricKMedian.PCP.FourQuery.map`, `OAI.MetricKMedian.PCP.IncidenceReduction.Label`, `OAI.MetricKMedian.PCP.IncidenceReduction.Position` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_LabelTransport`, `KMedian_Amplification_PaddedAlphabet`, `KMedian_Amplification_PoweringObjects`, `KMedian_Geometry_NearestFillingFormula`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_RationalArgmin`, `KMedian_Optimization_TruncatedListOperations`, `KMedian_Optimization_TruncatedRepair`, `KMedian_PCP_AlphabetReduction`, `KMedian_PCP_BinaryReduction`, `KMedian_PCP_Boundary`, `KMedian_PCP_FiniteTest`, `KMedian_PCP_Hadamard`, `KMedian_PCP_LocalReduction`, `KMedian_PCP_Quadratic`, `KMedian_PCP_QuadraticEncoding`, `KMedian_PCP_Queries`, `KMedian_PCP_Tester`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Process_CountRunHeight`, `KMedian_Process_CountRunProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_ScaleListProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Reduction_NormalizationGuesses`, `KMedian_Rounding_GridRoundingProgram`, `KMedian_Rounding_TargetSubsetProgram`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K020`, `OAIQ053K021`, `OAIQ053K022`, `OAIQ053K023`, `OAIQ053K024`, `OAIQ053K025` and `OAIQ053K026`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringObjects
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

abbrev Advice (D A : Type) (cap : ℕ) := (n : Fin (cap+1)) → (Fin n.val → D) → A

namespace Advice
variable {D A : Type} {cap : ℕ}
variable [Inhabited A]

def get (a : Advice D A cap) (n : ℕ) (c : Fin n → D) : A :=
  if h : n ≤ cap then a ⟨n,by omega⟩ c else default

@[simp] theorem get_le (a : Advice D A cap) (n : ℕ) (c : Fin n → D) (h : n ≤ cap) :
    a.get n c = a ⟨n,by omega⟩ c := by simp [get,h]

end Advice

end MetricKMedian.PCP

end Inline_PCPPoweringObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

noncomputable def testRate {S : Type} [Fintype S] (reject : S → Prop) : ℝ := by
  classical
  exact 𝔼 s, if reject s then 1 else 0

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Hadamard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPHadamard

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

abbrev Bit := ZMod 2
abbrev BitVector (V : Type) := V → Bit

section Vectors
variable {V W : Type} [Fintype V] [Fintype W]

def dot (x y : BitVector V) : Bit := ∑ i, x i * y i

def tensor (x : BitVector V) (y : BitVector W) : BitVector (V × W) :=
  fun p => x p.1 * y p.2

@[simp] theorem dot_add_left (x y z : BitVector V) : dot (x+y) z = dot x z + dot y z := by
  simp [dot, add_mul, sum_add_distrib]
@[simp] theorem dot_add_right (x y z : BitVector V) : dot x (y+z) = dot x y + dot x z := by
  simp [dot, mul_add, sum_add_distrib]
@[simp] theorem dot_zero_left (x : BitVector V) : dot 0 x = 0 := by simp [dot]
@[simp] theorem dot_zero_right (x : BitVector V) : dot x 0 = 0 := by simp [dot]

def dotHom (x : BitVector V) : BitVector V →+ Bit where
  toFun := dot x
  map_zero' := dot_zero_right x
  map_add' := dot_add_right x

omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_add_left (x y : BitVector V) (z : BitVector W) :
    tensor (x+y) z = tensor x z + tensor y z := by ext; simp [tensor, add_mul]
omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_add_right (x : BitVector V) (y z : BitVector W) :
    tensor x (y+z) = tensor x y + tensor x z := by ext; simp [tensor, mul_add]
omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_zero_left (x : BitVector W) : tensor (0 : BitVector V) x = 0 := by
  ext; simp [tensor]
omit [Fintype V] [Fintype W] in
@[simp] theorem tensor_zero_right (x : BitVector V) : tensor x (0 : BitVector W) = 0 := by
  ext; simp [tensor]

end Vectors
end MetricKMedian.PCP

end Inline_PCPHadamard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Quadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQuadratic

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Quadratic
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

structure QuadraticSystem (V E : Type) [Fintype V] [Fintype E] where
  form : E → BitVector (V × V)
  rhs : BitVector E

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

def combination (t : BitVector E) : BitVector (V × V) := ∑ e, t e • Q.form e

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem combination_add (t u : BitVector E) :
    Q.combination (t+u) = Q.combination t + Q.combination u := by
  simp [combination, add_smul, sum_add_distrib]
omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem combination_zero : Q.combination 0 = 0 := by simp [combination]

omit [DecidableEq V] in
@[simp] theorem combination_single (e : E) :
    Q.combination (Pi.single e 1) = Q.form e := by
  simp [combination, Pi.single_apply, ite_smul]

def equationDiscrepancy (h : BitVector (V × V) →+ Bit) : BitVector E →+ Bit where
  toFun t := h (Q.combination t) - dot Q.rhs t
  map_zero' := by simp
  map_add' := by intros; simp; ring

omit [DecidableEq V] in
@[simp] theorem equationDiscrepancy_single
    (h : BitVector (V × V) →+ Bit) (e : E) :
    Q.equationDiscrepancy h (Pi.single e 1) = h (Q.form e) - Q.rhs e := by
  simp [equationDiscrepancy, dot, Pi.single_apply, mul_ite]

end QuadraticSystem

end Quadratic
end MetricKMedian.PCP

end Inline_PCPQuadratic

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_QuadraticEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQuadraticEncoding

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Algebra
variable {I T : Type} [Fintype I] [Fintype T]

@[simp] theorem dot_sum (a : BitVector I) (x : T → BitVector I) :
    dot a (∑ t, x t) = ∑ t, dot a (x t) := map_sum (dotHom a) _ _

@[simp] theorem dot_smul (a x : BitVector I) (c : Bit) :
    dot a (c • x) = c * dot a x := ZMod.map_smul (dotHom a) c x

def unitForm [DecidableEq I] (i j : I) : BitVector (I × I) := Pi.single (i,j) 1

@[simp] theorem dot_unitForm [DecidableEq I] (a : BitVector (I × I)) (i j : I) :
    dot a (unitForm i j) = a (i,j) := by
  simp [unitForm, dot, Pi.single_apply, mul_ite]

end Algebra

namespace RelationEncoding
variable {I A : Type} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

abbrev Variable (I A : Type) := I ⊕ A
abbrev Equation (I A : Type) := Unit ⊕ ((A × A) ⊕ I)

def system (label : A → BitVector I) : QuadraticSystem (Variable I A) (Equation I A) where
  form q := match q with
    | .inl _ => ∑ a : A, unitForm (Sum.inr a) (Sum.inr a)
    | .inr (.inl (a,b)) => if a = b then 0 else unitForm (Sum.inr a) (Sum.inr b)
    | .inr (.inr i) => unitForm (Sum.inl i) (Sum.inl i) +
        ∑ a : A, label a i • unitForm (Sum.inr a) (Sum.inr a)
  rhs q := match q with | .inl _ => 1 | .inr _ => 0

def witness (label : A → BitVector I) (a : A) : BitVector (Variable I A) :=
  Sum.elim (label a) (Pi.single a 1)

omit [Fintype I] [Fintype A] [DecidableEq I] in
@[simp] theorem witness_left (label : A → BitVector I) (a : A) (i : I) :
    witness label a (.inl i) = label a i := rfl

omit [Fintype I] [Fintype A] [DecidableEq I] in
@[simp] theorem witness_right (label : A → BitVector I) (a b : A) :
    witness label a (.inr b) = if b = a then 1 else 0 := by
  simp [witness, Pi.single_apply]

end RelationEncoding
end MetricKMedian.PCP

end Inline_PCPQuadraticEncoding

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBoundary

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Code
variable {I : Type} [Fintype I] [DecidableEq I]

@[simp] theorem dot_single (a : BitVector I) (i : I) :
    dot a (Pi.single i 1) = a i := by
  simp [dot, Pi.single_apply, mul_ite]

theorem exists_nearest (f : BitVector I → Bit) :
    ∃ a : BitVector I, ∀ b, testRate (fun x => f x ≠ dot a x) ≤
      testRate (fun x => f x ≠ dot b x) := by
  classical
  obtain ⟨a,_,ha⟩ := univ.exists_min_image
    (fun b : BitVector I => testRate (fun x => f x ≠ dot b x)) univ_nonempty
  exact ⟨a,fun b => ha b (mem_univ b)⟩

noncomputable def nearestLabel (f : BitVector I → Bit) : BitVector I :=
  Classical.choose (exists_nearest f)

end Code

section Boundary
variable {I V : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

def liftQuery (embed : I → V) (x : BitVector I) : BitVector V :=
  ∑ i, x i • Pi.single (embed i) 1

omit [DecidableEq I] in
@[simp] theorem dot_liftQuery (embed : I → V) (a : BitVector V) (x : BitVector I) :
    dot a (liftQuery embed x) = dot (a ∘ embed) x := by
  simp only [liftQuery, dot_sum, dot_smul, dot_single]
  unfold dot
  apply sum_congr rfl
  intro i _
  simp only [Function.comp_apply, mul_comm]

end Boundary
end MetricKMedian.PCP

end Inline_PCPBoundary

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Tester
attribute [-simp] _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_left _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_right _root_.OAI.MetricKMedian.PCP.dot_liftQuery _root_.OAI.MetricKMedian.PCP.dot_single _root_.OAI.MetricKMedian.PCP.dot_smul _root_.OAI.MetricKMedian.PCP.dot_sum _root_.OAI.MetricKMedian.PCP.dot_unitForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTester

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

omit [DecidableEq V] [DecidableEq E] in
@[simp] theorem dot_combination (a : BitVector (V × V)) (t : BitVector E) :
    dot a (Q.combination t) = ∑ e, t e * dot a (Q.form e) := by
  change (dotHom a) (∑ e, t e • Q.form e) = _
  rw [map_sum]
  apply sum_congr rfl
  intro e _
  rw [ZMod.map_smul]
  rfl

end QuadraticSystem
end MetricKMedian.PCP

end Inline_PCPTester

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_LocalReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]

abbrev Relation (K : Type) := Set (BitVector K × BitVector K)

variable (R : Relation K) [DecidablePred (· ∈ R)]

abbrev Allowed := {p : BitVector K × BitVector K // p ∈ R}
abbrev Vars := RelationEncoding.Variable (K ⊕ K) (Allowed R)
abbrev Eqs := RelationEncoding.Equation (K ⊕ K) (Allowed R)

instance instDecidableEqVars : DecidableEq (Vars R) := by
  letI : DecidableEq (Allowed R) := inferInstance
  infer_instance

def label (p : Allowed R) : BitVector (K ⊕ K) := Sum.elim p.val.1 p.val.2

def quadratic : QuadraticSystem (Vars R) (Eqs R) := RelationEncoding.system (label R)

def leftEmbed (i : K) : Vars R := .inl (.inl i)
def rightEmbed (i : K) : Vars R := .inl (.inr i)

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Queries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQueries

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

structure FourQuery (P : Type) where
  address : Fin 4 → P
  accept : BitVector (Fin 4) → Bool

namespace FourQuery
variable {P : Type}
def Rejects (q : FourQuery P) (a : P → Bit) : Prop := q.accept (a ∘ q.address) ≠ true
end FourQuery

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]
variable (R : Relation K) [DecidablePred (· ∈ R)]

abbrev LocalPosition := BitVector (Vars R) ⊕
  (BitVector (Vars R × Vars R) ⊕ (Fin 2 × BitVector K))

def firstPos (x : BitVector (Vars R)) : LocalPosition R := .inl x
def secondPos (x : BitVector (Vars R × Vars R)) : LocalPosition R := .inr (.inl x)
def leftPos (x : BitVector K) : LocalPosition R := .inr (.inr (0,x))
def rightPos (x : BitVector K) : LocalPosition R := .inr (.inr (1,x))

def assignment (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) :
    LocalPosition R → Bit
  | .inl x => f x
  | .inr (.inl x) => h x
  | .inr (.inr (b,x)) => if b = 0 then u x else v x

abbrev Sample : Fin 6 → Type
  | 0 => BitVector (Vars R) × BitVector (Vars R)
  | 1 => BitVector (Vars R × Vars R) × BitVector (Vars R × Vars R)
  | 2 => (BitVector (Vars R) × BitVector (Vars R)) × BitVector (Vars R × Vars R)
  | 3 => BitVector (Eqs R) × BitVector (Vars R × Vars R)
  | 4 => BitVector K × BitVector (Vars R)
  | 5 => BitVector K × BitVector (Vars R)

def query : (i : Fin 6) → Sample R i → FourQuery (LocalPosition R)
  | 0, (x,y) => ⟨![firstPos R (x+y), firstPos R x, firstPos R y, firstPos R x],
      fun z => decide (z 0 = z 1 + z 2)⟩
  | 1, (x,y) => ⟨![secondPos R (x+y), secondPos R x, secondPos R y, secondPos R x],
      fun z => decide (z 0 = z 1 + z 2)⟩
  | 2, ((x,y),z) => ⟨![firstPos R x, firstPos R y,
      secondPos R (tensor x y + z), secondPos R z],
      fun w => decide (w 0 * w 1 = w 2 - w 3)⟩
  | 3, (t,z) => ⟨![secondPos R ((quadratic R).combination t + z),
      secondPos R z, secondPos R z, secondPos R z],
      fun w => decide (w 0 - w 1 = dot (quadratic R).rhs t)⟩
  | 4, (x,z) => ⟨![firstPos R (liftQuery (leftEmbed R) x + z),
      firstPos R z, leftPos R x, leftPos R x],
      fun w => decide (w 0 - w 1 = w 2)⟩
  | 5, (x,z) => ⟨![firstPos R (liftQuery (rightEmbed R) x + z),
      firstPos R z, rightPos R x, rightPos R x],
      fun w => decide (w 0 - w 1 = w 2)⟩

abbrev Pad := (i : Fin 6) → Sample R i

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPQueries

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_AlphabetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]

structure BinaryCSP (V E A : Type) where
  left : E → V
  right : E → V
  allowed : E → Finset (A × A)

structure FourCSP (P T : Type) where
  query : T → FourQuery P

namespace FourQuery
variable {P Q : Type}
def map (q : FourQuery P) (f : P → Q) : FourQuery Q := ⟨f ∘ q.address, q.accept⟩
@[simp] theorem map_rejects (q : FourQuery P) (f : P → Q) (a : Q → Bit) :
    (q.map f).Rejects a ↔ q.Rejects (a ∘ f) := Iff.rfl
end FourQuery

namespace AlphabetReduction
variable (K)
abbrev Relations := Finset (BitVector K × BitVector K)
abbrev UniversalPad := (R : Relations K) → LocalRelation.Pad (R : LocalRelation.Relation K)
abbrev EdgeSample := Fin 6 × UniversalPad K

variable {K}
variable (C : BinaryCSP V E (BitVector K))
abbrev relation (e : E) : LocalRelation.Relation K := (C.allowed e : Set _)
abbrev Interior (e : E) := BitVector (LocalRelation.Vars (relation C e)) ⊕
  BitVector (LocalRelation.Vars (relation C e) × LocalRelation.Vars (relation C e))
abbrev Position := (V × BitVector K) ⊕ ((e : E) × Interior C e)
abbrev Test := E × EdgeSample K

def localMap (e : E) : LocalRelation.LocalPosition (relation C e) → Position C
  | .inl x => .inr ⟨e,.inl x⟩
  | .inr (.inl x) => .inr ⟨e,.inr x⟩
  | .inr (.inr (b,x)) => .inl (if b = 0 then C.left e else C.right e, x)

def reduced : FourCSP (Position C) (Test (E := E) (K := K)) where
  query t := (LocalRelation.query (relation C t.1) t.2.1
    (t.2.2 (C.allowed t.1) t.2.1)).map (localMap C t.1)

def vertexTable (a : Position C → Bit) (v : V) : BitVector K → Bit :=
  fun x => a (.inl (v,x))
def firstTable (a : Position C → Bit) (e : E) :
    BitVector (LocalRelation.Vars (relation C e)) → Bit := fun x => a (.inr ⟨e,.inl x⟩)
def secondTable (a : Position C → Bit) (e : E) :
    BitVector (LocalRelation.Vars (relation C e) × LocalRelation.Vars (relation C e)) → Bit :=
  fun x => a (.inr ⟨e,.inr x⟩)

omit [Fintype V] [Fintype E] [Fintype K] [DecidableEq K] in
@[simp] theorem restriction (a : Position C → Bit) (e : E) :
    a ∘ localMap C e = LocalRelation.assignment (relation C e)
      (firstTable C a e) (secondTable C a e)
      (vertexTable C a (C.left e)) (vertexTable C a (C.right e)) := by
  funext p
  rcases p with x | x
  · rfl
  rcases x with x | ⟨b,x⟩
  · rfl
  by_cases hb : b = 0 <;> simp [localMap, LocalRelation.assignment, vertexTable, hb]

noncomputable def decoded (a : Position C → Bit) : V → BitVector K :=
  fun v => nearestLabel (vertexTable C a v)

end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPAlphabetReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_LabelTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLabelTransport

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Advice
abbrev BitIndex (D K : Type) (cap : ℕ) := (n : Fin (cap+1)) × ((Fin n.val → D) × K)
def bitsEquiv (D K : Type) (cap : ℕ) :
    Advice D (BitVector K) cap ≃ BitVector (BitIndex D K cap) where
  toFun a p := a p.1 p.2.1 p.2.2
  invFun b n w k := b ⟨n,w,k⟩
  left_inv _ := rfl
  right_inv _ := rfl
end Advice
end MetricKMedian.PCP

end Inline_PCPLabelTransport

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_BinaryReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace IncidenceReduction
variable {P T : Type} [Fintype T] (C : FourCSP P T)
abbrev Label := BitVector (Fin 4)
abbrev Position := P ⊕ T
abbrev Test := T × Fin 4

def reduced : BinaryCSP (Position (P := P) (T := T)) (Test (T := T)) Label where
  left t := .inr t.1
  right t := .inl ((C.query t.1).address t.2)
  allowed t := univ.filter (fun p => (C.query t.1).accept p.1 = true ∧ p.1 t.2 = p.2 0)

omit [Fintype T] in
@[simp] theorem allowed_iff (t : T × Fin 4) (x y : Label) :
    (x,y) ∈ (reduced C).allowed t ↔ (C.query t.1).accept x = true ∧ x t.2 = y 0 := by
  simp [reduced]

end IncidenceReduction

namespace AlphabetReduction
variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))

def binary := IncidenceReduction.reduced (reduced C)

end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPBinaryReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PaddedAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPaddedAlphabet
namespace MetricKMedian.PCP.AlphabetReduction
open Finset
open scoped BigOperators Classical

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
abbrev RelationInterior (R : Relations K) :=
  BitVector (LocalRelation.Vars (R : LocalRelation.Relation K)) ⊕
    BitVector (LocalRelation.Vars (R : LocalRelation.Relation K) × LocalRelation.Vars (R : LocalRelation.Relation K))
abbrev UniversalInterior (K : Type) [Fintype K] [DecidableEq K] :=
  (R : Relations K) × RelationInterior R
abbrev PaddedPosition (V E K : Type) [Fintype K] [DecidableEq K] :=
  (V × BitVector K) ⊕ (E × UniversalInterior K)
abbrev PaddedNode (V E K : Type) [Fintype K] [DecidableEq K] :=
  PaddedPosition V E K ⊕ (E × EdgeSample K)
end MetricKMedian.PCP.AlphabetReduction

end Inline_PCPPaddedAlphabet

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPListFacts
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset

 theorem sum_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).sum=∑ i∈univ.filter (fun i => p (f i)), f i := by
  rw [Finset.sum_filter]
  have he : ((List.ofFn f).filter p).sum=((List.ofFn f).map (fun a => if p a then a else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

 theorem length_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).length=(univ.filter (fun i => p (f i))).card := by
  have he : ((List.ofFn f).filter p).length=((List.ofFn f).map (fun a => if p a then (1:ℕ) else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih,Nat.add_comm]
  rw [he,List.map_ofFn,List.sum_ofFn]
  simp

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_NearestFillingFormula
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

def before (d : Fin n → ℚ) (j i : Fin n) : Prop := d j  <  d i ∨ d j=d i ∧ j < i
instance instDecidableBefore (d : Fin n → ℚ) (j i : Fin n) : Decidable (before d j i) := by unfold before; infer_instance
def priorMass (U : Finset (Fin n)) (y d : Fin n → ℚ) (i : Fin n) : ℚ :=
  ∑ j∈U.filter (fun j => before d j i), y j

theorem priorMass_erase (U : Finset (Fin n)) (y d : Fin n → ℚ) (a i : Fin n)
    (ha : a∈U) (hai : before d a i) : priorMass U y d i=priorMass (U.erase a) y d i+y a := by
  have he : (U.erase a).filter (fun j => before d j i)=(U.filter (fun j => before d j i)).erase a := by
    ext j
    simp only [mem_filter,mem_erase,and_assoc]
  unfold priorMass
  rw [he]
  exact (sum_erase_add _ y (mem_filter.mpr ⟨ha,hai⟩)).symm

theorem priorMass_nonneg (U : Finset (Fin n)) (y d : Fin n → ℚ) (i : Fin n)
    (hy : ∀ j∈U, 0 ≤ y j) : 0 ≤ priorMass U y d i :=
  sum_nonneg (fun j hj => hy j (mem_filter.mp hj).1)

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def nearWeight (d x : κ → ι → ℚ) (j : κ) (i : ι) : ℚ :=
  if d j i ≤ 1 then x j i else 0

def nearMass (d x : κ → ι → ℚ) (j : κ) : ℚ := ∑ i, nearWeight d x j i

def repairedOpening (y : ι → ℚ) (ρ : ℚ) (i : ι) : ℚ := min 1 (y i/(1-ρ))

def repairedAssignment (d x : κ → ι → ℚ) (j : κ) (i : ι) : ℚ :=
  nearWeight d x j i/nearMass d x j

omit [Fintype ι] [Fintype κ] in
theorem nearWeight_nonneg (d x : κ → ι → ℚ) (hx : ∀ j i, 0 ≤ x j i) (j : κ) (i : ι) :
    0 ≤ nearWeight d x j i := by
  unfold nearWeight
  split_ifs
  · exact hx j i
  · exact le_rfl

omit [Fintype ι] [Fintype κ] in
theorem nearWeight_le (d x : κ → ι → ℚ) (hx : ∀ j i, 0 ≤ x j i) (j : κ) (i : ι) :
    nearWeight d x j i ≤ x j i := by unfold nearWeight; split_ifs <;> simp_all

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_NormalizationGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Normalization

theorem dyadic_bracket (c d : ℚ) (N : ℕ) (hd : 0 < d) (hc : d ≤ c)
    (hupper : c ≤ d*(2:ℚ)^N) :
    ∃ t ≤ N, c ≤ d*(2:ℚ)^t ∧ d*(2:ℚ)^t ≤ 2*c := by
  induction N with
  | zero =>
    refine ⟨0,le_rfl,hupper,?_⟩
    simp only [pow_zero,mul_one]
    linarith
  | succ N ih =>
    by_cases h : c ≤ d*(2:ℚ)^N
    · obtain ⟨t,ht,h1,h2⟩ := ih h
      exact ⟨t,by omega,h1,h2⟩
    · refine ⟨N+1,le_rfl,hupper,?_⟩
      rw [pow_succ]
      have hh := lt_of_not_ge h
      nlinarith

end Normalization
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_RationalArgmin
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

def rationalArgmin (A : Finset ℚ) (f : ℚ → ℚ) : ℚ :=
  if hA : A.Nonempty then
    let v := (A.image f).min' (hA.image f)
    let B := A.filter (fun t => f t=v)
    if hB : B.Nonempty then B.min' hB else 0
  else 0

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Polynomial Finset

structure Input where
  n : ℕ
  m : ℕ
  k : ℕ
  npos : 0 < n
  mpos : 0 < m
  kpos : 0 < k
  kle : k ≤ n
  distance : Fin m → Fin n → ℚ

namespace Input
instance instNeZeroNatN (I : Input) : NeZero I.n := ⟨I.npos.ne'⟩
instance instNeZeroNatM (I : Input) : NeZero I.m := ⟨I.mpos.ne'⟩
end Input

def gradientBound (r L : ℕ) := L*(L*(4*r*(L+1)))^2
def baseBound (r L : ℕ) := 2*r*gradientBound r L*L
def stepsBound (r L : ℕ) := 8*r^2*gradientBound r L*L^2
def exponentBound (r L : ℕ) := baseBound r L+L*(L*L)+L+1
def heightBound (r L : ℕ) := exponentBound r L*(stepsBound r L+1)

noncomputable def stepsPolynomial (r : ℕ) : Polynomial ℕ := 8*C r^2*(X*(X*(4*C r*(X+1)))^2)*X^2
noncomputable def heightPolynomial (r : ℕ) : Polynomial ℕ :=
  (2*C r*(X*(X*(4*C r*(X+1)))^2)*X+X*(X*X)+X+1)*(stepsPolynomial r+1)
 theorem stepsPolynomial_eval (r L : ℕ) : (stepsPolynomial r).eval L=stepsBound r L := by
  simp only [stepsPolynomial,stepsBound,gradientBound,eval_add,eval_mul,eval_pow,eval_ofNat,eval_C,eval_X,eval_one]
 theorem heightPolynomial_eval (r L : ℕ) : (heightPolynomial r).eval L=heightBound r L := by
  simp only [heightPolynomial,heightBound,exponentBound,baseBound,gradientBound,eval_add,eval_mul,eval_pow,eval_ofNat,eval_C,eval_X,eval_one,stepsPolynomial_eval]
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Finset
theorem range_ofFn (n : ℕ) : List.range n=List.ofFn (fun i : Fin n => i.val) := by
  apply List.ext_getElem
  · simp
  · intros; simp

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Function

theorem head_ofFn {α : Type} {n : ℕ} [NeZero n] (f : Fin n → α) (a : α) :
    (List.ofFn f).head?.getD a=f ⟨0,NeZero.pos n⟩ := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rw [List.ofFn_succ]; rfl

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestListProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Function Finset

theorem sum_map_filter_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) (v : α → ℚ) :
    (((List.ofFn f).filter p).map v).sum=∑ i ∈ univ.filter (fun i => p (f i)), v (f i) := by
  rw [Finset.sum_filter]
  have he (xs : List α) : ((xs.filter p).map v).sum=(xs.map (fun a => if p a then v a else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalListChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Function Finset

theorem all_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).all p=true ↔ ∀ i, p (f i)=true := by
  simp only [List.all_eq_true,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]

end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
structure Input where
  n : ℕ
  D : Finset (Fin n)
  q : ℚ
  feasible : 0≤q ∧ q≤1
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  q : Fin m → ℚ
  feasible : ∀ e, 0≤q e ∧ q e≤1

def Input.column (x : Input) (e : Fin x.m) : SparseTargetSubset.Program.Input :=
  ⟨x.n,x.D e,x.q e,x.feasible e⟩
def Input.columns (x : Input) := List.ofFn x.column

def dummy : SparseTargetSubset.Program.Input := ⟨0,∅,0,by norm_num⟩
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseCounts
variable {n m : ℕ}

def stepHeight (n m N L H : ℕ) :=
  let d := n*m+(n*m)*(n*m)
  L+((2*(d+1)*(d+1+(H+H)*((d+1)*N+1)))*((d+1)*N+1))*((d+1)*N)

end MetricKMedian.SparseCounts
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseCounts.Program
open Function Polynomial

def supportBound (L : ℕ) := L*L+(L*L)*(L*L)+1
def heightBound (L : ℕ) := SparseCounts.stepHeight L L L L L*L
def graphSize (L : ℕ) := L*(2*(L*(2*(L+1)+1))+1)
def sizeBound (L : ℕ) :=
  2*(3*L+2)+1+(2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*graphSize L+1))
noncomputable def SPoly : Polynomial ℕ := X*X+(X*X)*(X*X)+1
noncomputable def HPoly : Polynomial ℕ := (X+(2*SPoly*(SPoly+(X+X)*(SPoly*X+1)))*(SPoly*X+1)*(SPoly*X))*X
noncomputable def APoly : Polynomial ℕ := X*(2*(X*(2*(X+1)+1))+1)
noncomputable def sizePolynomial : Polynomial ℕ :=
  2*(3*X+2)+1+(2*(2*(HPoly+4)+1+SPoly*(2*(HPoly+4)+1))+1+SPoly*(2*APoly+1))
theorem sizePolynomial_eval (L : ℕ) : sizePolynomial.eval L=sizeBound L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,graphSize,HPoly,SPoly,APoly,
    SparseCounts.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridRoundingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program
structure Input where
  n : ℕ
  q : Fin n → ℚ
  nonnegative : ∀ i, 0≤q i
abbrev Input.raw (x : Input) := List.ofFn x.q
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Function
open SparseCounts.Program

structure QInput where
  n : ℕ
  m : ℕ
  q : Fin n → Fin m → ℚ
  feasible : ∀ h i, 0≤q h i

def QInput.raw (x : QInput) : List Unit × List (List ℚ) :=
  (List.replicate x.n (),List.ofFn fun i => List.ofFn fun h => x.q h i)

def QInput.column (x : QInput) (i : Fin x.m) : SparseGridRounding.Program.Input :=
  ⟨x.n,fun h => x.q h i,fun h => x.feasible h i⟩
def QInput.columns (x : QInput) : List SparseGridRounding.Program.Input := List.ofFn x.column
def emptyColumn : SparseGridRounding.Program.Input := ⟨0,Fin.elim0,fun i => Fin.elim0 i⟩
end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  q : Fin m → ℚ
  c_unit : ∀ e,0 ≤ c e ∧ c e≤1
  q_nonnegative : ∀ e,0≤q e
end MetricKMedian.SparseOuterLaw.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
structure Input where
  n : ℕ
  m : ℕ
  f : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  q : Fin m → ℚ
  P : Fin n → Finset (Fin f)
  y : Fin f → ℚ
  p : Fin n → ℚ
  Δ : ℕ
  hy : ∀ i,0≤y i
  hp : ∀ j,0<p j
  hc : ∀ e,0 ≤ c e ∧ c e≤1
  hq : ∀ e,0≤q e

def Input.outer (x : Input) : SparseOuterLaw.Program.Input := ⟨x.n,x.m,x.D,x.c,x.q,x.hc,x.hq⟩
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Polynomial

structure Input where
  n : ℕ
  R : Fin n → ℚ
  d : Fin n → Fin n → ℚ
  M : ℚ
  U : Finset (Fin n)
abbrev Cut (x : Input) := Finset (Fin x.n) × Finset (Fin x.n)
structure State where
  input : Input
  cut : Cut input
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset

theorem finSum_symm_castLE {m n : ℕ} (h : m ≤ m+n) (i : Fin m) :
    (finSumFinEquiv.symm (Fin.castLE h i) : Fin m ⊕ Fin n)=.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_ScaleListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Function Finset
namespace Input

def scale (I : Input) (B : ℚ) : Input := { I with distance := fun j i => I.distance j i/B }
end Input
end MetricKMedian.LPBinary
end

end OAI
end


