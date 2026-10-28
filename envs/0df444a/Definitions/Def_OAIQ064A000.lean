-- Prove2me | Definitions.Def_OAIQ064A000
-- name    : OAIQ064A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T00:28:36.165967+00:00
-- url     : https://prove2.me/theorems/074d802b-7d56-4859-bbc4-04d37cb1a3f4
-- title:
--   Definitions bundle OAIQ064A000 of the split of OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 467 declarations of OpenAI's Lean: 253 definitions, 19 inductive types or structures, 7 instances and 188 theorems. The definitions and types are `OAI.TuringRigidity.AntichainDecoding.Antichain`, `OAI.TuringRigidity.AntichainDecoding.Minimal`, `OAI.TuringRigidity.AntichainDecoding.Nontrivial`, `OAI.TuringRigidity.AntichainParameters.CodedAntichain`, `OAI.TuringRigidity.AntichainParameters.NontrivialCommonLower`, `OAI.TuringRigidity.Approximates`, `OAI.TuringRigidity.ArithmeticHierarchy.Form`, `OAI.TuringRigidity.ArithmeticHierarchy.Pi`, `OAI.TuringRigidity.ArithmeticHierarchy.Quant`, `OAI.TuringRigidity.ArithmeticHierarchy.RecursivePred`, `OAI.TuringRigidity.ArithmeticHierarchy.Sigma`, `OAI.TuringRigidity.ArithmeticHierarchy.item`, `OAI.TuringRigidity.ArithmeticModelDecoding.Copy`, `OAI.TuringRigidity.ArithmeticModelDecoding.Defined`, `OAI.TuringRigidity.ArithmeticModelDecoding.Path`, `OAI.TuringRigidity.ArithmeticModelDecoding.one`, `OAI.TuringRigidity.ArithmeticModelDecoding.oneIndex`, `OAI.TuringRigidity.ArithmeticModelDecoding.two`, `OAI.TuringRigidity.ArithmeticModelDecoding.twoIndex`, `OAI.TuringRigidity.ArithmeticPersistence.Criterion`, `OAI.TuringRigidity.ArithmeticPersistence.Matrix`, `OAI.TuringRigidity.ArithmeticPersistence.parameters`, `OAI.TuringRigidity.ArithmeticPrefixForcing.ArithmeticPrefix`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Avoid`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Decides`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Generic`, `OAI.TuringRigidity.ArithmeticPrefixForcing.PrefixPredicate`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Upward`, `OAI.TuringRigidity.ArithmeticTree.Approx`, `OAI.TuringRigidity.ArithmeticTree.Captures`, `OAI.TuringRigidity.ArithmeticTree.Extends`, `OAI.TuringRigidity.ArithmeticTree.HasTest`, `OAI.TuringRigidity.ArithmeticTree.NativeNonidentity`, `OAI.TuringRigidity.ArithmeticTree.NativePersistent`, `OAI.TuringRigidity.ArithmeticTree.SetGenericallyPersistent`, `OAI.TuringRigidity.ArithmeticTree.SetMoved`, `OAI.TuringRigidity.ArithmeticTree.Term`, `OAI.TuringRigidity.ArithmeticTree.Term.approx`, `OAI.TuringRigidity.ArithmeticTree.Term.eval`, `OAI.TuringRigidity.ArithmeticTree.Term.left` and 232 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DegreeRigidity_CohenForcing_AtomicForcing`, `DegreeRigidity_CohenForcing_CohenHalting`, `DegreeRigidity_CohenForcing_CountableForcing`, `DegreeRigidity_CohenForcing_EffectiveForcing`, `DegreeRigidity_CohenForcing_EncodedForcing`, `DegreeRigidity_Computability_ArithmeticAtoms`, `DegreeRigidity_Computability_ArithmeticBounded`, `DegreeRigidity_Computability_ArithmeticFiniteTest`, `DegreeRigidity_Computability_ArithmeticHierarchy`, `DegreeRigidity_Computability_ArithmeticModelDecoding`, `DegreeRigidity_Computability_ArithmeticOracles`, `DegreeRigidity_Computability_ArithmeticPersistence`, `DegreeRigidity_Computability_ArithmeticPrefixForcing`, `DegreeRigidity_Computability_ArithmeticPresentationProperty`, `DegreeRigidity_Computability_ArithmeticSkolem`, `DegreeRigidity_Computability_ArithmeticTestApproximation`, `DegreeRigidity_Computability_ArithmeticTreeDefinability`, `DegreeRigidity_Computability_ArithmeticTreeDescent`, `DegreeRigidity_Computability_ArithmeticWitnessTree`, `DegreeRigidity_Computability_BranchMachine`, `DegreeRigidity_Computability_BranchRecovery`, `DegreeRigidity_Computability_Introreducible`, `DegreeRigidity_Computability_Joins`, `DegreeRigidity_Computability_JumpIdealPresentation`, `DegreeRigidity_Computability_JumpProperties`, `DegreeRigidity_Computability_OracleCode`, `DegreeRigidity_Computability_OracleJump`, `DegreeRigidity_Computability_RationalCoding`, `DegreeRigidity_Computability_UniformArithmetic`, `DegreeRigidity_Constructibility_PersistenceWitnessTree`, `DegreeRigidity_Constructibility_PersistentRestrictions`, `DegreeRigidity_Effective_AntichainDecoding`, `DegreeRigidity_Effective_AntichainParameters`, `DegreeRigidity_Effective_CodingColumns`, `DegreeRigidity_Effective_CodingForcing`, `DegreeRigidity_Effective_EffectiveFamilies`, `DegreeRigidity_Effective_EffectivePresentation`, `DegreeRigidity_Effective_EffectiveWitness`, `DegreeRigidity_Effective_FiniteApproximation`, `DegreeRigidity_Effective_FiniteInjury`, `DegreeRigidity_Effective_FiniteInjurySchedule`, `DegreeRigidity_Effective_FiniteShuffle`, `DegreeRigidity_Effective_FiniteTuple`, `DegreeRigidity_Effective_GuardedComputability`, `DegreeRigidity_Effective_GuardedScan`, `DegreeRigidity_Effective_GuardedStage`, `DegreeRigidity_Effective_OrderNormalForm`, `DegreeRigidity_Effective_PartialComputability`, `DegreeRigidity_Effective_PrefixComputability`, `DegreeRigidity_Effective_SetCoding`, `DegreeRigidity_Effective_StageNormalization`, `DegreeRigidity_Effective_StageRecords`, `DegreeRigidity_Effective_TableIndices`, `DegreeRigidity_Effective_UniformOracle`, `DegreeRigidity_OrdinalCodes_IndexJoin`, `DegreeRigidity_OrdinalCodes_IndexMatrix`, `DegreeRigidity_OrdinalCodes_IndexPresentation`, `DegreeRigidity_OrdinalCodes_IndexTuples`, `DegreeRigidity_OrdinalCodes_IndexedOrder`, `DegreeRigidity_OrdinalCodes_NumericalAutomorphism`, `DegreeRigidity_OrdinalCodes_NumericalExtension`, `DegreeRigidity_OrdinalCodes_NumericalIdeal`, `DegreeRigidity_Representation_CommonIdeal`, `DegreeRigidity_Representation_CommonIdealSearch`, `DegreeRigidity_Representation_GenericSourceTransfer`, `DegreeRigidity_Representation_GenericTruth`, `DegreeRigidity_Representation_GlobalLocality`, `DegreeRigidity_Representation_NativeGenericWitness`, `DegreeRigidity_Representation_PairGenericSelection`, `DegreeRigidity_Representation_SourceTGenericPersistence`, `DegreeRigidity_Representation_SourceTNativeComparison`, `DegreeRigidity_SetModels_DecodingTheorem`, `DegreeRigidity_SetModels_Degrees`, `DegreeRigidity_SetModels_EnumerationConstruction`, `DegreeRigidity_SetModels_FixedArithmetic`, `DegreeRigidity_SetModels_IdealInterpretation`, `DegreeRigidity_SetModels_InternalAtomicTruth`, `DegreeRigidity_SetModels_InternalCollapseConditions`, `DegreeRigidity_SetModels_InternalInfinity`, `DegreeRigidity_SetModels_IntersectionName`, `DegreeRigidity_SetModels_NameEncoding`, `DegreeRigidity_SetModels_NameSupport`, `DegreeRigidity_SetModels_ParametricEval`, `DegreeRigidity_SetModels_RecursiveNames`, `DegreeRigidity_SetModels_RelationCoding`, `DegreeRigidity_SetModels_SetDegreeDecoding`, `DegreeRigidity_SetModels_SetModelActionSatisfaction`, `DegreeRigidity_SetModels_SetModelColumns`, `DegreeRigidity_SetModels_SetModelCountability`, `DegreeRigidity_SetModels_SetModelFunctionIteration`, `DegreeRigidity_SetModels_SetModelGraphImage`, `DegreeRigidity_SetModels_SetModelIdealSatisfaction`, `DegreeRigidity_SetModels_SetModelIteration`, `DegreeRigidity_SetModels_SetModelMultiplicationStep`, `DegreeRigidity_SetModels_SetModelPairing`, `DegreeRigidity_SetModels_SetModelPersistentSatisfaction`, `DegreeRigidity_SetModels_SetModelPresentedCountability`, `DegreeRigidity_SetModels_SetModelReals`, `DegreeRigidity_SetModels_SetModelSequences`, `DegreeRigidity_SetModels_SetModelTreeRelations`, `DegreeRigidity_SetModels_SetPresentationDecoding`, `DegreeRigidity_SetModels_ShuffleRequirements`, `DegreeRigidity_SetModels_TransitiveNameModel`, `DegreeRigidity_SetModels_UnionIteration`, `DegreeRigidity_Syntax_AtomicCertificate`, `DegreeRigidity_Syntax_AtomicDecisionFormula`, `DegreeRigidity_Syntax_AtomicFormula`, `DegreeRigidity_Syntax_AtomicGraph`, `DegreeRigidity_Syntax_AtomicGraphCorrect`, `DegreeRigidity_Syntax_AtomicRequirements`, `DegreeRigidity_Syntax_BoundedFormulaRename`, `DegreeRigidity_Syntax_BoundedRecursive`, `DegreeRigidity_Syntax_BoundedRelations`, `DegreeRigidity_Syntax_BoundedSetTheory`, `DegreeRigidity_Syntax_SigmaSyntax`.
--
--   **Imports.** It imports the published bundle `Def_DegreeRigidity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ064A002`, `OAIQ064A003` and `OAIQ064A004`; the statement `OAI.TuringRigidity.LocalCoding.selected_antichain`.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity

section
-- module Solutions.OAIQ064_DR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_Degrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem reduces_refl (A : Oracle) : Reduces A A := TuringReducible.refl _
theorem reduces_trans {A B C : Oracle} (h : Reduces A B) (k : Reduces B C) :
    Reduces A C := TuringReducible.trans h k

def degree (A : Oracle) : Degree := toAntisymmetrization Reduces A

@[simp] theorem degree_le_iff (A B : Oracle) : degree A ≤ degree B ↔ Reduces A B := Iff.rfl

theorem degree_eq_iff (A B : Oracle) :
    degree A = degree B ↔ Reduces A B ∧ Reduces B A := by
  exact Quotient.eq

theorem degree_surjective : Function.Surjective degree := by
  intro a
  exact ⟨ofAntisymmetrization Reduces a, toAntisymmetrization_ofAntisymmetrization _ a⟩

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CountableForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountableForcing
open Set

structure GenericFilter (P : Type*) [Preorder P] where
  carrier : Set P
  nonempty : carrier.Nonempty
  upper : ∀ {p q}, p ≤ q → p ∈ carrier → q ∈ carrier
  directed : ∀ {p q}, p ∈ carrier → q ∈ carrier → ∃ r ∈ carrier, r ≤ p ∧ r ≤ q

def Dense {P : Type*} [Preorder P] (D : Set P) : Prop := ∀ p, ∃ q, q ≤ p ∧ q ∈ D

end TuringRigidity.CountableForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RecursiveNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u}

inductive Name (P : Type u) : Type (u+1) where
  | mk (ι : Type u) (child : ι → Name P) (tag : ι → P) : Name P

namespace Name
noncomputable def val (G : Set P) : Name P → ZFSet.{u}
  | .mk _ child tag => ZFSet.range (fun i : {i // tag i ∈ G} => val G (child i.val))

end Name
end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set
universe u
variable {P : Type u}

noncomputable def Name.encode (label : P → ZFSet.{u}) : Name P → ZFSet.{u}
  | .mk _ child tag => ZFSet.range (fun i => ZFSet.pair (encode label (child i)) (label (tag i)))

end TuringRigidity.RecursiveNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_AtomicForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

def Below (p t : P) (A : P → Prop) : Prop :=
  ∀ q, q ≤ p → q ≤ t → ∃ r, r ≤ q ∧ A r

def EqForces : Name P → Name P → P → Prop
  | .mk _ a s, .mk _ b t, p =>
    (∀ i, Below p (s i) (fun r => ∃ j, r ≤ t j ∧ EqForces (a i) (b j) r)) ∧
    (∀ j, Below p (t j) (fun r => ∃ i, r ≤ s i ∧ EqForces (a i) (b j) r))

def MemForces (a : Name P) : Name P → P → Prop
  | .mk _ b t, p => ∀ q, q ≤ p → ∃ r, r ≤ q ∧ ∃ j, r ≤ t j ∧ EqForces a (b j) r

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

inductive OracleCode where
  | zero | succ | left | right | query
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | find : OracleCode → OracleCode
  deriving Encodable

namespace OracleCode

def eval (g : ℕ →. ℕ) : OracleCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .query => g
  | .pair c d => fun n => Nat.pair <$> eval g c n <*> eval g d n
  | .comp c d => fun n => eval g d n >>= eval g c
  | .prec c d => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (eval g c a) fun y ih => do
        let i ← ih
        eval g d (Nat.pair a (Nat.pair y i))
  | .find c => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> eval g c (Nat.pair a n)

theorem exists_code {g f : ℕ →. ℕ} (hf : Nat.RecursiveIn {g} f) :
    ∃ c : OracleCode, eval g c = f := by
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | oracle f hf =>
      have hfg : f = g := Set.mem_singleton_iff.mp hf
      subst f
      exact ⟨.query, rfl⟩
  | pair _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.pair c d, rfl⟩
  | comp _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.comp c d, rfl⟩
  | prec _ _ hc hd =>
      obtain ⟨c, rfl⟩ := hc
      obtain ⟨d, rfl⟩ := hd
      exact ⟨.prec c d, rfl⟩
  | rfind _ hc =>
      obtain ⟨c, rfl⟩ := hc
      exact ⟨.find c, rfl⟩

end OracleCode

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

def Approximates {α : Type*} (p : Part α) (ps : ℕ → Part α) : Prop :=
  (∀ m a, a ∈ ps m → a ∈ p) ∧
  (∀ a, a ∈ p → ∃ M, ∀ m, M ≤ m → a ∈ ps m)

namespace Approximates
variable {α β : Type*}

theorem const (p : Part α) : Approximates p (fun _ => p) :=
  ⟨fun _ _ h => h, fun _ h => ⟨0,fun _ _ => h⟩⟩

theorem bind {p : Part α} {ps : ℕ → Part α} {f : α → Part β}
    {fs : ℕ → α → Part β} (hp : Approximates p ps)
    (hf : ∀ a, Approximates (f a) (fun m => fs m a)) :
    Approximates (p.bind f) (fun m => (ps m).bind (fs m)) := by
  constructor
  · intro m b hb
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hb
    exact Part.mem_bind_iff.mpr ⟨a,hp.1 m a ha,(hf a).1 m b hb⟩
  · intro b hb
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hb
    obtain ⟨M,hM⟩ := hp.2 a ha
    obtain ⟨N,hN⟩ := (hf a).2 b hb
    exact ⟨max M N,fun m hm => Part.mem_bind_iff.mpr
      ⟨a,hM m ((le_max_left _ _).trans hm),hN m ((le_max_right _ _).trans hm)⟩⟩

theorem map {p : Part α} {ps : ℕ → Part α} (hp : Approximates p ps) (f : α → β) :
    Approximates (p.map f) (fun m => (ps m).map f) := by
  simpa only [Part.bind_some_eq_map] using hp.bind (fun a => const (Part.some (f a)))

theorem finite_bounds (P : ℕ → ℕ → Prop) (n : ℕ)
    (h : ∀ i, i < n → ∃ M, ∀ m, M ≤ m → P i m) :
    ∃ M, ∀ m, M ≤ m → ∀ i, i < n → P i m := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨M,hM⟩ := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨N,hN⟩ := h n (Nat.lt_succ_self n)
    refine ⟨max M N, fun m hm i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hM m ((le_max_left _ _).trans hm) i hi
    · exact hN m ((le_max_right _ _).trans hm)

theorem rfind {p : ℕ → Part Bool} {ps : ℕ → ℕ → Part Bool}
    (hp : ∀ n, Approximates (p n) (fun m => ps m n)) :
    Approximates (Nat.rfind p) (fun m => Nat.rfind (ps m)) := by
  constructor
  · intro m n hn
    obtain ⟨ht,hf⟩ := Nat.mem_rfind.mp hn
    exact Nat.mem_rfind.mpr ⟨(hp n).1 m true ht,fun {k} hk => (hp k).1 m false (hf hk)⟩
  · intro n hn
    obtain ⟨ht,hf⟩ := Nat.mem_rfind.mp hn
    obtain ⟨M,hM⟩ := (hp n).2 true ht
    obtain ⟨N,hN⟩ := finite_bounds (fun k m => false ∈ ps m k) n
      (fun k hk => (hp k).2 false (hf hk))
    exact ⟨max M N, fun m hm => Nat.mem_rfind.mpr
      ⟨hM m ((le_max_left _ _).trans hm),fun {k} hk => hN m ((le_max_right _ _).trans hm) k hk⟩⟩
end Approximates

namespace OracleCode

theorem eval_approximates {g : ℕ →. ℕ} {gs : ℕ → ℕ →. ℕ}
    (hg : ∀ n, Approximates (g n) (fun m => gs m n)) (c : OracleCode) :
    ∀ n, Approximates (eval g c n) (fun m => eval (gs m) c n) := by
  induction c with
  | zero => intro n; exact Approximates.const _
  | succ => intro n; exact Approximates.const _
  | left => intro n; exact Approximates.const _
  | right => intro n; exact Approximates.const _
  | query => exact hg
  | pair c d hc hd =>
    intro n
    exact (hc n).bind (fun a => (hd n).map (Nat.pair a))
  | comp c d hc hd => intro n; exact (hd n).bind hc
  | prec c d hc hd =>
    intro p
    have hr : ∀ k, Approximates
        (Nat.rec (eval g c (Nat.unpair p).1)
          (fun y ih => ih.bind (fun i => eval g d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k)
        (fun m => Nat.rec (eval (gs m) c (Nat.unpair p).1)
          (fun y ih => ih.bind (fun i => eval (gs m) d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k) := by
      intro k
      induction k with
      | zero => exact hc _
      | succ k ih => exact ih.bind (fun i => hd _)
    exact hr _
  | find c hc =>
    intro n
    exact Approximates.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

end OracleCode
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_PartialComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Computable

theorem partrec_code {α : Type*} [Primcodable α] {f : α →. ℕ} (hf : Partrec f) :
    ∃ c : Nat.Partrec.Code, ∀ a, c.eval (Encodable.encode a) = f a := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c, fun a => ?_⟩
  simp [hc, Encodable.encodek, Part.map_id']

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ParametricEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleCode
open Computable

theorem eval_partrec {α : Type*} [Primcodable α] {g : α → ℕ →. ℕ}
    (hg : Partrec₂ g) (c : OracleCode) : Partrec₂ (fun a n => eval (g a) c n) := by
  induction c with
  | zero => exact Computable.const 0
  | succ => exact Computable.succ.comp snd
  | left => exact (fst.comp Computable.unpair).comp snd
  | right => exact (snd.comp Computable.unpair).comp snd
  | query => exact hg
  | pair c d hc hd =>
    change Partrec (fun z : α × ℕ =>
      (eval (g z.1) c z.2).bind (fun a => (eval (g z.1) d z.2).map (Nat.pair a)))
    apply Partrec.bind hc
    apply Partrec.map (hd.comp (fst.comp fst) (snd.comp fst))
    exact Primrec₂.natPair.to_comp.comp (snd.comp fst) snd
  | comp c d hc hd =>
    exact hd.bind (hc.comp (fst.comp fst) snd)
  | prec c d hc hd =>
    exact Partrec.nat_rec ((snd.comp Computable.unpair).comp snd)
      (hc.comp fst ((fst.comp Computable.unpair).comp snd))
      (hd.comp (fst.comp fst)
        (Primrec₂.natPair.to_comp.comp ((fst.comp Computable.unpair).comp (snd.comp fst))
          (Primrec₂.natPair.to_comp.comp (fst.comp snd) (snd.comp snd)))).to₂
  | find c hc =>
    exact Partrec.rfind ((hc.comp (fst.comp fst)
      (Primrec₂.natPair.to_comp.comp (snd.comp fst) snd)).map
        ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).to_comp))

end TuringRigidity.OracleCode

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Computable

def partialJoin (f g : ℕ →. ℕ) (k : ℕ) : Part ℕ :=
  if k.bodd then g (k/2) else f (k/2)

namespace BranchMachine

variable {α : Type*} [Primcodable α]

def lookup (L : List ℕ) (k : ℕ) : Part ℕ := (L[k]? : Part ℕ)

theorem lookup_partrec : Partrec₂ lookup :=
  Computable.ofOption Primrec.list_getElem?.to_comp

end BranchMachine
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Encodable

namespace UniformOracle
variable {O : Set (ℕ →. ℕ)}

theorem total_comp {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) := by
  simpa using Nat.RecursiveIn.comp hf hg

theorem total_pair {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
  simpa [Seq.seq] using Nat.RecursiveIn.pair hf hg

theorem total_primrec {f : ℕ → ℕ} (hf : Primrec f) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

def oraclePrefix (g : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map g

def appendEncoded (a b : ℕ) : ℕ := encode ((decode (α := List ℕ) a).getD [] ++ [b])

theorem appendEncoded_primrec : Primrec₂ appendEncoded :=
  Primrec.encode.comp (Primrec.list_append.comp
    (Primrec.option_getD_default.comp (Primrec.decode.comp Primrec.fst))
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

theorem prefix_recursive (g : ℕ → ℕ) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun m => Part.some (encode (oraclePrefix g m))) := by
  have hquery : Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (g n)) :=
    .oracle _ (Set.mem_singleton _)
  have hy := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp ((total_primrec (O := {fun n => Part.some (g n)})) (appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hquery hy))
  have hp := Nat.RecursiveIn.prec ((total_primrec (O := {fun n => Part.some (g n)})) (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair ((total_primrec (O := {fun n => Part.some (g n)})) (Primrec.const 0)) ((total_primrec (O := {fun n => Part.some (g n)})) Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [appendEncoded, oraclePrefix, List.range_succ]

theorem prefix_approximates (g : ℕ → ℕ) (k : ℕ) :
    Approximates (Part.some (g k)) (fun m => BranchMachine.lookup (oraclePrefix g m) k) := by
  have he (m : ℕ) : (oraclePrefix g m)[k]? = if k < m then some (g k) else none := by
    simp only [oraclePrefix, List.getElem?_map]
    by_cases hk : k < m
    · rw [List.getElem?_range hk, ite_eq_left hk]
      rfl
    · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk), ite_eq_right hk]
      rfl
  constructor
  · intro m a ha
    change a ∈ ((oraclePrefix g m)[k]? : Part ℕ) at ha
    rw [he] at ha
    split at ha
    · simpa using ha
    · simp at ha
  · intro a ha
    have ha' : a = g k := Part.mem_some_iff.mp ha
    subst a
    refine ⟨k+1,fun m hm => ?_⟩
    change g k ∈ ((oraclePrefix g m)[k]? : Part ℕ)
    rw [he, ite_eq_left (by omega)]
    exact Part.mem_some _

def trial (g : ℕ → ℕ) (c : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  c.evaln (Nat.unpair z).2 (Nat.pair (encode (oraclePrefix g (Nat.unpair z).1)) n)

end UniformOracle
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle

noncomputable def RecursivePred (Y : Oracle) (P : ℕ → Prop) : Prop := by
  classical
  exact Nat.RecursiveIn {oracleFunction Y} (fun x => Part.some (if P x then 1 else 0))

def Quant (s : Bool) (P : ℕ → Prop) : Prop :=
  if s then ∃ a, P a else ∀ a, P a

def Form (Y : Oracle) : ℕ → Bool → (ℕ → Prop) → Prop
  | 0, _, P => RecursivePred Y P
  | n+1, s, P => ∃ Q : ℕ → Prop, Form Y n (!s) Q ∧
      ∀ x, P x ↔ Quant s (fun a => Q (Nat.pair x a))

abbrev Sigma (Y : Oracle) (n : ℕ) (P : ℕ → Prop) := Form Y n true P
abbrev Pi (Y : Oracle) (n : ℕ) (P : ℕ → Prop) := Form Y n false P

theorem Form.congr {Y n s P Q} (h : Form Y n s P) (he : ∀ x, P x ↔ Q x) :
    Form Y n s Q := by
  have : P = Q := funext (fun x => propext (he x))
  exact this ▸ h

theorem recursive_comp {Y P} (h : RecursivePred Y P) {f : ℕ → ℕ} (hf : Primrec f) :
    RecursivePred Y (fun x => P (f x)) := by
  classical
  exact _root_.OAI.TuringRigidity.UniformOracle.total_comp h (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hf)

theorem Form.comp {Y n s P} (h : Form Y n s P) {f : ℕ → ℕ} (hf : Primrec f) :
    Form Y n s (fun x => P (f x)) := by
  induction n generalizing s P f with
  | zero => exact recursive_comp h hf
  | succ n ih =>
    obtain ⟨Q, hQ, he⟩ := h
    refine ⟨fun v => Q (Nat.pair (f (Nat.unpair v).1) (Nat.unpair v).2),
      ih hQ (Primrec₂.natPair.comp (hf.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair)), ?_⟩
    intro x
    simpa using he (f x)

theorem recursive_not {Y P} (h : RecursivePred Y P) : RecursivePred Y (fun x => ¬ P x) := by
  classical
  have hf : Primrec (fun v : ℕ => if v = 1 then 0 else 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 0) (Primrec.const 1)
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hf) h).of_eq (fun x => by by_cases hp : P x <;> simp [hp])

theorem quant_not (s : Bool) (P : ℕ → Prop) :
    (¬ Quant s P) ↔ Quant (!s) (fun x => ¬ P x) := by
  cases s <;> simp [Quant]

theorem Form.neg {Y n s P} (h : Form Y n s P) :
    Form Y n (!s) (fun x => ¬ P x) := by
  induction n generalizing s P with
  | zero => exact recursive_not h
  | succ n ih =>
    obtain ⟨Q, hQ, he⟩ := h
    exact ⟨fun v => ¬ Q v, ih hQ, fun x => (not_congr (he x)).trans (quant_not s _)⟩

theorem recursive_and {Y P Q} (hP : RecursivePred Y P) (hQ : RecursivePred Y Q) :
    RecursivePred Y (fun x => P x ∧ Q x) := by
  classical
  have hf : Primrec (fun v : ℕ => if (Nat.unpair v).1 = 1 ∧ (Nat.unpair v).2 = 1 then 1 else 0) :=
    Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0)
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hf) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hP hQ)).of_eq (fun x => by
    by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq])

theorem quant_and (s : Bool) (P Q : ℕ → Prop) :
    (Quant s P ∧ Quant s Q) ↔
      Quant s (fun v => P (Nat.unpair v).1 ∧ Q (Nat.unpair v).2) := by
  cases s
  · simp only [Quant, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h v => ⟨h.1 _, h.2 _⟩,
      fun h => ⟨fun a => by simpa using (h (Nat.pair a 0)).1, fun b => by simpa using (h (Nat.pair 0 b)).2⟩⟩
  · simp only [Quant, ↓reduceIte]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨Nat.pair a b, by simpa using And.intro ha hb⟩
    · rintro ⟨v, ha, hb⟩
      exact ⟨⟨_, ha⟩, ⟨_, hb⟩⟩

theorem Form.and {Y n s P Q} (hP : Form Y n s P) (hQ : Form Y n s Q) :
    Form Y n s (fun x => P x ∧ Q x) := by
  induction n generalizing s P Q with
  | zero => exact recursive_and hP hQ
  | succ n ih =>
    obtain ⟨A, hA, heA⟩ := hP
    obtain ⟨B, hB, heB⟩ := hQ
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    have h := ih (hA.comp (Primrec₂.natPair.comp f (f.comp r)))
      (hB.comp (Primrec₂.natPair.comp f (r.comp r)))
    refine ⟨_, h, fun x => ?_⟩
    simpa only [Nat.unpair_pair] using
      (and_congr (heA x) (heB x)).trans (quant_and s _ _)

theorem Form.or {Y n s P Q} (hP : Form Y n s P) (hQ : Form Y n s Q) :
    Form Y n s (fun x => P x ∨ Q x) := by
  have h := (hP.neg.and hQ.neg).neg
  simpa only [Bool.not_not, not_and_or, not_not] using h

theorem Form.raise {Y n s P} (h : Form Y n s P) : Form Y (n+1) s P := by
  induction n generalizing s P with
  | zero =>
    refine ⟨fun v => P (Nat.unpair v).1, recursive_comp h (Primrec.fst.comp Primrec.unpair), ?_⟩
    intro x
    cases s <;> simp [Quant]
  | succ n ih =>
    obtain ⟨Q, hQ, he⟩ := h
    exact ⟨Q, ih hQ, he⟩

theorem Form.ex {Y n P} (h : Form Y (n+1) true P) :
    Form Y (n+1) true (fun x => ∃ a, P (Nat.pair x a)) := by
  obtain ⟨Q, hQ, he⟩ := h
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  refine ⟨fun v => Q (Nat.pair (Nat.pair (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1)
    (Nat.unpair (Nat.unpair v).2).2),
    hQ.comp (Primrec₂.natPair.comp (Primrec₂.natPair.comp f (f.comp r)) (r.comp r)), ?_⟩
  intro x
  simp only [Quant, ↓reduceIte, Nat.unpair_pair]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := (he _).mp ha
    exact ⟨Nat.pair a b, by simpa using hb⟩
  · rintro ⟨v, hv⟩
    exact ⟨(Nat.unpair v).1, (he _).mpr ⟨(Nat.unpair v).2, hv⟩⟩

end TuringRigidity.ArithmeticHierarchy

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedRecursive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedRecursive
open UniformOracle

def allBelow (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => if allBelow f a n = 1 ∧ f (Nat.pair a n) = 1 then 1 else 0

theorem allBelow_spec (f : ℕ → ℕ) (a n : ℕ) :
    allBelow f a n = 1 ↔ ∀ i < n, f (Nat.pair a i) = 1 := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not, ih]
    exact ⟨fun ⟨h, hn⟩ i hi => (Nat.lt_succ_iff_lt_or_eq.mp hi).elim (h i) (fun he => he ▸ hn),
      fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩⟩

theorem allBelow_binary (f : ℕ → ℕ) (a n : ℕ) : allBelow f a n = 0 ∨ allBelow f a n = 1 := by
  cases n with
  | zero => exact Or.inr rfl
  | succ n => unfold allBelow; split <;> simp

theorem allBelow_recursive {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n))) :
    Nat.RecursiveIn O (fun z => Part.some (allBelow f (Nat.unpair z).1 (Nat.unpair z).2)) := by
  have harg := _root_.OAI.TuringRigidity.UniformOracle.total_pair (O := O) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.fst.comp Primrec.unpair))
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hval := _root_.OAI.TuringRigidity.UniformOracle.total_comp hf harg
  have hprev := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have htest := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)
    (Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0))
  have hstep := _root_.OAI.TuringRigidity.UniformOracle.total_comp htest (_root_.OAI.TuringRigidity.UniformOracle.total_pair hprev hval)
  have hrec := Nat.RecursiveIn.prec (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.const 1)) hstep
  apply hrec.of_eq
  intro z
  generalize hz : Nat.unpair z = v
  obtain ⟨a, n⟩ := v
  simp only [Nat.unpair_pair, Part.bind_eq_bind]
  clear hz
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih, Part.bind_some, allBelow]

end TuringRigidity.BoundedRecursive

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open Encodable UniformOracle BoundedRecursive

theorem recursive_bounded_all {Y P} (h : RecursivePred Y P) {b : ℕ → ℕ} (hb : Primrec b) :
    RecursivePred Y (fun x => ∀ i < b x, P (Nat.pair x i)) := by
  classical
  let f : ℕ → ℕ := fun x => if P x then 1 else 0
  have hr := _root_.OAI.TuringRigidity.UniformOracle.total_comp (allBelow_recursive (f := f) h)
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp Primrec.id hb))
  apply hr.of_eq
  intro x
  simp only [Nat.unpair_pair, id_eq]
  have hs := allBelow_spec f x (b x)
  have hbin := allBelow_binary f x (b x)
  by_cases hp : ∀ i < b x, P (Nat.pair x i)
  · have hv : allBelow f x (b x) = 1 := hs.mpr (fun i hi => by simp [f,hp i hi])
    rw [ite_eq_left hp,hv]
  · have hn : allBelow f x (b x) ≠ 1 := by
      intro h1
      apply hp
      intro i hi
      have hx := (hs.mp h1) i hi
      simpa [f] using hx
    have hz : allBelow f x (b x) = 0 := hbin.resolve_right hn
    rw [ite_eq_right hp,hz]

def item (t i : ℕ) : ℕ := ((decode (α := List ℕ) t).getD []).getD i 0

theorem item_primrec : Primrec₂ item :=
  (Primrec.list_getD 0).comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const [])) Primrec.snd

theorem exists_items (b : ℕ) (P : ℕ → ℕ → Prop) :
    (∀ i < b, ∃ a, P i a) ↔ ∃ t, ∀ i < b, P i (item t i) := by
  classical
  constructor
  · intro h
    choose a ha using (fun i : Fin b => h i.val i.isLt)
    refine ⟨encode (List.ofFn a), fun i hi => ?_⟩
    simpa [item, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using ha ⟨i,hi⟩
  · rintro ⟨t,ht⟩ i hi
    exact ⟨item t i, ht i hi⟩

theorem Form.bounded_all {Y n s P} (h : Form Y n s P) {b : ℕ → ℕ} (hb : Primrec b) :
    Form Y n s (fun x => ∀ i < b x, P (Nat.pair x i)) := by
  induction n generalizing s P b with
  | zero => exact recursive_bounded_all h hb
  | succ n ih =>
    obtain ⟨Q,hQ,he⟩ := h
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    cases s with
    | false =>
      have hR := ih (hQ.comp (Primrec₂.natPair.comp (Primrec₂.natPair.comp (f.comp f) r) (r.comp f)))
        (hb.comp f)
      refine ⟨_, hR, fun x => ?_⟩
      simp only [Nat.unpair_pair, Quant, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h a i hi
        exact (he _).mp (h i hi) a
      · intro h i hi
        exact (he _).mpr (fun a => h a i hi)
    | true =>
      have hR := ih (hQ.comp (Primrec₂.natPair.comp (Primrec₂.natPair.comp (f.comp f) r)
        (item_primrec.comp (r.comp f) r))) (hb.comp f)
      refine ⟨_, hR, fun x => ?_⟩
      simp only [Nat.unpair_pair, Quant, ↓reduceIte]
      exact (forall_congr' (fun i => forall_congr' (fun _ => he (Nat.pair x i)))).trans
        (exists_items (b x) (fun i a => Q (Nat.pair (Nat.pair x i) a)))

end TuringRigidity.ArithmeticHierarchy

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_PrefixComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PrefixComputability
open Encodable

variable {O : Set (ℕ →. ℕ)}

def oraclePrefix (g : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map g

end TuringRigidity.PrefixComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_Introreducible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace Introreducible
open Encodable PrefixComputability

def bit (X : Oracle) (n : ℕ) : ℕ := if X n then 1 else 0

def prefixCode (X : Oracle) (n : ℕ) : ℕ := encode (oraclePrefix (bit X) n)

def codeList (c : ℕ) : List ℕ := (decode (α := List ℕ) c).getD []
def codeLength (c : ℕ) : ℕ := (codeList c).length

def prefixSet (X : Oracle) (c : ℕ) : Bool := decide (prefixCode X (codeLength c) = c)

@[simp] theorem codeList_prefix (X : Oracle) (n : ℕ) :
    codeList (prefixCode X n) = oraclePrefix (bit X) n := by
  simp [codeList, prefixCode]

@[simp] theorem codeLength_prefix (X : Oracle) (n : ℕ) :
    codeLength (prefixCode X n) = n := by
  simp [codeLength, oraclePrefix]

@[simp] theorem prefixSet_prefix (X : Oracle) (n : ℕ) :
    prefixSet X (prefixCode X n) = true := by
  simp [prefixSet]

def codeBit (n c : ℕ) : ℕ := (codeList c).getD n 0

@[simp] theorem codeBit_prefix (X : Oracle) (n m : ℕ) (h : n < m) :
    codeBit n (prefixCode X m) = bit X n := by
  simp [codeBit, oraclePrefix, List.getD_eq_getElem?_getD, List.getElem?_range h]

end Introreducible
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingForcing

structure Condition where
  left : List Bool
  right : List Bool
  sameLength : left.length = right.length
  active : ℕ

def CodingLocation (A : ℕ → Oracle) (p : Condition) (m : ℕ) : Prop :=
  p.left.length ≤ m ∧ (Nat.unpair m).1 < p.active ∧
    A (Nat.unpair m).1 (Nat.unpair m).2 = true

def Extends (A : ℕ → Oracle) (p q : Condition) : Prop :=
  p.left <+: q.left ∧ p.right <+: q.right ∧ p.active ≤ q.active ∧
    ∀ m, CodingLocation A p m → m < q.left.length →
      q.left.getD m false = q.right.getD m false

theorem extends_refl (A : ℕ → Oracle) (p : Condition) : Extends A p p := by
  refine ⟨List.prefix_rfl, List.prefix_rfl, le_rfl, ?_⟩
  intro m hm hlt
  exact False.elim (Nat.not_lt_of_ge hm.1 hlt)

end TuringRigidity.CodingForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_EncodedForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EncodedForcing
open Encodable UniformOracle ArithmeticHierarchy CodingForcing

def word (e : ℕ) : List Bool := (decode e).getD []
def left (e : ℕ) : List Bool := word (Nat.unpair e).1
def rawRight (e : ℕ) : List Bool := word (Nat.unpair (Nat.unpair e).2).1
def right (e : ℕ) : List Bool := if (rawRight e).length = (left e).length then rawRight e else left e
def active (e : ℕ) : ℕ := (Nat.unpair (Nat.unpair e).2).2

def condition (e : ℕ) : Condition := ⟨left e, right e, by
  unfold right
  split <;> simp_all, active e⟩

def code (p : Condition) : ℕ := Nat.pair (encode p.left) (Nat.pair (encode p.right) p.active)

theorem condition_code (p : Condition) : condition (code p) = p := by
  cases p with
  | mk l r h k => simp [condition,code,left,right,rawRight,word,active,h]

theorem word_primrec : Primrec word := Primrec.option_getD.comp Primrec.decode (Primrec.const [])
theorem left_primrec : Primrec left := word_primrec.comp (Primrec.fst.comp Primrec.unpair)
theorem rawRight_primrec : Primrec rawRight := word_primrec.comp
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
theorem right_primrec : Primrec right := Primrec.ite
  (Primrec.eq.comp (Primrec.list_length.comp rawRight_primrec) (Primrec.list_length.comp left_primrec))
  rawRight_primrec left_primrec
theorem active_primrec : Primrec active := Primrec.snd.comp
  (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem recursive_primrecPred (Y : Oracle) {P : ℕ → Prop} [DecidablePred P]
    (h : PrimrecPred P) : RecursivePred Y P := by
  classical
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.ite h (Primrec.const 1) (Primrec.const 0))).of_eq
    (fun x => by by_cases hp : P x <;> simp [hp])

theorem prefix_recursive (Y : Oracle) {l r : ℕ → List Bool} (hl : Primrec l) (hr : Primrec r) :
    RecursivePred Y (fun v => l v <+: r v) := by
  have h : RecursivePred Y (fun v => l v = (r v).take (l v).length) := recursive_primrecPred Y
    (Primrec.eq.comp hl (Primrec.list_take.comp (Primrec.list_length.comp hl) hr))
  exact Form.congr (n := 0) (s := true) h (fun v => List.prefix_iff_eq_take.symm)

def columns (B : Oracle) (k n : ℕ) : Bool := B (Nat.pair k n)

theorem bounded_conjunction_iff {n : ℕ} {P Q R S : ℕ → Prop} :
    (∀ i < n, ¬ P i ∨ ¬ Q i ∨ ¬ R i ∨ S i) ↔
      (∀ i, P i ∧ Q i ∧ R i → i < n → S i) := by
  classical
  constructor
  · intro h i hi hin
    exact (((h i hin).resolve_left (fun hn => hn hi.1)).resolve_left
      (fun hn => hn hi.2.1)).resolve_left (fun hn => hn hi.2.2)
  · intro h i hin
    by_cases hp : P i
    · by_cases hq : Q i
      · by_cases hr : R i
        · exact Or.inr (Or.inr (Or.inr (h i ⟨hp, hq, hr⟩ hin)))
        · exact Or.inr (Or.inr (Or.inl hr))
      · exact Or.inr (Or.inl hq)
    · exact Or.inl hp

theorem extends_recursive (B : Oracle) :
    RecursivePred B (fun v => Extends (columns B) (condition (Nat.unpair v).1) (condition (Nat.unpair v).2)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hl := prefix_recursive B (left_primrec.comp f) (left_primrec.comp r)
  have hr := prefix_recursive B (right_primrec.comp f) (right_primrec.comp r)
  have ha := recursive_primrecPred B
    (Primrec.nat_le.comp (active_primrec.comp f) (active_primrec.comp r))
  let p := f.comp f
  let q := r.comp f
  let m := r
  have hlen := recursive_primrecPred B (Primrec.nat_le.comp (Primrec.list_length.comp (left_primrec.comp p)) m)
  have hcol := recursive_primrecPred B (Primrec.nat_lt.comp (f.comp m) (active_primrec.comp p))
  have hquery : RecursivePred B (fun v => B (Nat.unpair v).2 = true) := by
    have hq : Nat.RecursiveIn {oracleFunction B} (oracleFunction B) := .oracle _ (Set.mem_singleton _)
    exact (Nat.RecursiveIn.comp hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec m)).of_eq (fun v => by
      change (Part.some (Nat.unpair v).2).bind (fun input => oracleFunction B input) = _
      rw [Part.bind_some]
      cases hb : B (Nat.unpair v).2 <;> simp [oracleFunction,hb])
  have heq := recursive_primrecPred B (Primrec.eq.comp
    ((Primrec.list_getD false).comp (left_primrec.comp q) m)
    ((Primrec.list_getD false).comp (right_primrec.comp q) m))
  have himp := Form.or (n := 0) (s := true) (recursive_not hlen)
    (Form.or (n := 0) (s := true) (recursive_not hcol)
      (Form.or (n := 0) (s := true) (recursive_not hquery) heq))
  have hb := recursive_bounded_all himp (Primrec.list_length.comp (left_primrec.comp r))
  apply Form.congr (n := 0) (s := true) (recursive_and hl (recursive_and hr (recursive_and ha hb)))
  intro v
  simp only [Extends,condition,CodingLocation,columns,Nat.pair_unpair,Nat.unpair_pair]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => bounded_conjunction_iff

end TuringRigidity.EncodedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_Joins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

def join (A B : Oracle) (n : ℕ) : Bool := if n.bodd then B (n / 2) else A (n / 2)

theorem total_comp {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (f (g n))) := by
  simpa using Nat.RecursiveIn.comp hf hg

theorem total_pair {O : Set (ℕ →. ℕ)} {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
  simpa [Seq.seq] using Nat.RecursiveIn.pair hf hg

theorem total_primrec {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Primrec f) : Nat.RecursiveIn O (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp hf.computableIn

@[simp] theorem join_even (A B : Oracle) (n : ℕ) : join A B (2*n) = A n := by
  simp [join, Nat.bodd_mul]

@[simp] theorem join_odd (A B : Oracle) (n : ℕ) : join A B (2*n+1) = B n := by
  simp [join, Nat.bodd_mul]
  congr 1
  omega

theorem reduces_join_left (A B : Oracle) : Reduces A (join A B) := by
  apply RecursiveIn.iff_nat.mpr
  have horacle : Nat.RecursiveIn {oracleFunction (join A B)} (oracleFunction (join A B)) :=
    .oracle _ (Set.mem_singleton _)
  have h := total_comp horacle (total_primrec (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
  change Nat.RecursiveIn {oracleFunction (join A B)} (fun n => Part.some (if A n then 1 else 0))
  simpa [oracleFunction] using h

theorem reduces_join_right (A B : Oracle) : Reduces B (join A B) := by
  apply RecursiveIn.iff_nat.mpr
  have horacle : Nat.RecursiveIn {oracleFunction (join A B)} (oracleFunction (join A B)) :=
    .oracle _ (Set.mem_singleton _)
  have h := total_comp horacle (total_primrec
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)))
  change Nat.RecursiveIn {oracleFunction (join A B)} (fun n => Part.some (if B n then 1 else 0))
  simpa [oracleFunction] using h

def selectPair (k : ℕ) : ℕ :=
  if (Nat.unpair k).1.bodd then (Nat.unpair (Nat.unpair k).2).2
  else (Nat.unpair (Nat.unpair k).2).1

theorem selectPair_primrec : Primrec selectPair := by
  apply (Primrec.cond (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).of_eq
  intro n
  cases hb : (Nat.unpair n).1.bodd <;> simp [selectPair, hb]

theorem join_reduces {A B C : Oracle} (hA : Reduces A C) (hB : Reduces B C) :
    Reduces (join A B) C := by
  apply RecursiveIn.iff_nat.mpr
  have hA' := RecursiveIn.iff_nat.mp hA
  have hB' := RecursiveIn.iff_nat.mp hB
  have hdiv : Nat.RecursiveIn {oracleFunction C} (fun n => Part.some (n / 2)) :=
    total_primrec (Primrec.nat_div.comp Primrec.id (Primrec.const 2))
  have hp := total_pair (total_primrec Primrec.id)
    (total_pair (total_comp hA' hdiv) (total_comp hB' hdiv))
  have h := total_comp (total_primrec selectPair_primrec) hp
  apply Nat.RecursiveIn.of_eq h
  intro n
  simp only [selectPair, Nat.unpair_pair, oracleFunction, join, id_eq]
  by_cases hb : n.bodd = true <;> simp [hb]

theorem join_mono {A B C D : Oracle} (hA : Reduces A C) (hB : Reduces B D) :
    Reduces (join A B) (join C D) :=
  join_reduces (reduces_trans hA (reduces_join_left C D))
    (reduces_trans hB (reduces_join_right C D))

def degreeJoin (a b : Degree) : Degree :=
  Quotient.liftOn₂ a b (fun A B => degree (join A B))
    (fun _ _ _ _ hA hB => (degree_eq_iff _ _).mpr
      ⟨join_mono hA.1 hB.1, join_mono hA.2 hB.2⟩)

@[simp] theorem degree_join (A B : Oracle) :
    degreeJoin (degree A) (degree B) = degree (join A B) := rfl

instance instSemilatticeSupDegree : SemilatticeSup Degree where
  sup := degreeJoin
  le_sup_left a b := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    obtain ⟨B, rfl⟩ := degree_surjective b
    exact reduces_join_left A B
  le_sup_right a b := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    obtain ⟨B, rfl⟩ := degree_surjective b
    exact reduces_join_right A B
  sup_le a b c := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    obtain ⟨B, rfl⟩ := degree_surjective b
    obtain ⟨C, rfl⟩ := degree_surjective c
    exact join_reduces

instance instOrderBotDegree : OrderBot Degree where
  bot := degree (fun _ => false)
  bot_le a := by
    obtain ⟨A, rfl⟩ := degree_surjective a
    apply RecursiveIn.iff_nat.mpr
    change Nat.RecursiveIn {oracleFunction A} (fun _ => Part.some 0)
    exact .zero

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Set Encodable

def bit (b : Bool) : ℕ := if b then 1 else 0

def initialWord (G : Oracle) (m : ℕ) : List Bool := (List.range m).map G

@[simp] theorem prefix_length (G : Oracle) (m : ℕ) : (initialWord G m).length = m := by
  simp [initialWord]

@[simp] theorem prefix_getD (G : Oracle) (m i : ℕ) (hi : i < m) :
    (initialWord G m).getD i false = G i := by
  simp [initialWord,List.getD,List.getElem?_range hi]

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdealSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Encodable Computable UniformOracle

theorem bit_primrec : Primrec bit := by
  apply (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq
  intro b
  cases b <;> rfl

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TableIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TableIndices
open Encodable UniformOracle CommonIdeal

def run (Y : Oracle) (d : Nat.Partrec.Code) (n z : ℕ) : Option ℕ :=
  trial (fun k => bit (Y k)) d n z

def Represents (Y : Oracle) (d : Nat.Partrec.Code) (A : Oracle) : Prop :=
  (∀ n z a, a ∈ run Y d n z → a = bit (A n)) ∧
    ∀ n, ∃ z a, a ∈ run Y d n z

def Valid (Y : Oracle) (d : Nat.Partrec.Code) : Prop :=
  (∀ n, ∃ z b, run Y d n z = some (bit b)) ∧
    ∀ n z w a b, a ∈ run Y d n z → b ∈ run Y d n w → a = b

theorem valid_iff_represents (Y : Oracle) (d : Nat.Partrec.Code) :
    Valid Y d ↔ ∃ A : Oracle, Represents Y d A := by
  constructor
  · rintro ⟨htotal, hconsistent⟩
    choose z A hA using htotal
    refine ⟨A, ?_, ?_⟩
    · intro n w a ha
      exact hconsistent n w (z n) a (bit (A n)) ha (Option.mem_def.mpr (hA n))
    · intro n
      exact ⟨z n, bit (A n), Option.mem_def.mpr (hA n)⟩
  · rintro ⟨A, hs, ht⟩
    refine ⟨?_, ?_⟩
    · intro n
      obtain ⟨z, a, ha⟩ := ht n
      exact ⟨z, A n, by rw [← hs n z a ha]; exact Option.mem_def.mp ha⟩
    · intro n z w a b ha hb
      exact (hs n z a ha).trans (hs n w b hb).symm

noncomputable def output (Y : Oracle) (d : {d : Nat.Partrec.Code // Valid Y d}) : Oracle :=
  Classical.choose ((valid_iff_represents Y d.val).mp d.property)

end TuringRigidity.TableIndices

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexMatrix
open Encodable UniformOracle CommonIdeal TableIndices

def machine (e : ℕ) : Nat.Partrec.Code := (decode e).getD .zero

theorem machine_primrec : Primrec machine :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const Nat.Partrec.Code.zero)

@[simp] theorem machine_encode (d : Nat.Partrec.Code) : machine (encode d) = d := by
  simp [machine]

theorem run_uniform_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (encode (run Y (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let e := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let n := Primrec.fst.comp (Primrec.unpair.comp rest)
  let z := Primrec.snd.comp (Primrec.unpair.comp rest)
  have he := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) e
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) n
  have hm := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp z))
  have ht := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp z))
  have hL := _root_.OAI.TuringRigidity.UniformOracle.total_comp (prefix_recursive (fun k => bit (Y k))) hm
  let r := Primrec.snd.comp Primrec.unpair
  have hdecode := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair
      (machine_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp r)))).pair
      (Primrec.snd.comp (Primrec.unpair.comp r)))))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp hdecode (_root_.OAI.TuringRigidity.UniformOracle.total_pair ht (_root_.OAI.TuringRigidity.UniformOracle.total_pair he (_root_.OAI.TuringRigidity.UniformOracle.total_pair hL hn)))).of_eq
    (fun v => by simp [TableIndices.run, trial])

end TuringRigidity.IndexMatrix

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexedOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexedOrder
open Encodable CommonIdeal UniformOracle TableIndices IndexMatrix

def Reads (Y : Oracle) (e : Nat.Partrec.Code) (L : List (ℕ × ℕ)) : Prop :=
  ∀ j : Fin L.length, TableIndices.run Y e j.val (L[j].2) = some (L[j].1)

def values (L : List (ℕ × ℕ)) : List ℕ := L.map Prod.fst

def Certificate (Y : Oracle) (e d : Nat.Partrec.Code) (n a z : ℕ) : Prop :=
  let L := (decode (α := List (ℕ × ℕ)) (Nat.unpair z).1).getD []
  Reads Y e L ∧ d.evaln (Nat.unpair z).2 (Nat.pair (encode (values L)) n) = some a

end TuringRigidity.IndexedOrder

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_OrderNormalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrderNormalForm
open Encodable TableIndices IndexMatrix IndexedOrder

def orderMatrix (Y : Oracle) (e₀ e₁ d q r : ℕ) : Prop :=
  let n := (Nat.unpair q).1
  let challenge := (Nat.unpair q).2
  let m := (Nat.unpair challenge).1
  let a := (Nat.unpair (Nat.unpair challenge).2).1
  let b := (Nat.unpair (Nat.unpair (Nat.unpair challenge).2).2).1
  let z := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair challenge).2).2).2).1
  let w := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair challenge).2).2).2).2
  let answer := (Nat.unpair r).1
  let cert := (Nat.unpair (Nat.unpair r).2).1
  let trial := (Nat.unpair (Nat.unpair r).2).2
  (Certificate Y (machine e₁) (machine d) n answer cert ∧
    TableIndices.run Y (machine e₀) n trial = some answer) ∧
    (Certificate Y (machine e₁) (machine d) m a z →
      Certificate Y (machine e₁) (machine d) m b w → a = b)

end TuringRigidity.OrderNormalForm

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexJoin
open Encodable Computable UniformOracle CommonIdeal TableIndices

def dispatch (v : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ) : Part ℕ :=
  let n := (Nat.unpair v.2).2
  let c := if n.bodd then v.1.2 else v.1.1
  c.eval (Nat.pair (Nat.unpair v.2).1 (n / 2))

theorem dispatch_partrec : Partrec dispatch := by
  let n : Computable (fun v : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ => (Nat.unpair v.2).2) :=
    snd.comp (Computable.unpair.comp snd)
  have hc : Computable (fun v : (Nat.Partrec.Code × Nat.Partrec.Code) × ℕ =>
      cond (Nat.unpair v.2).2.bodd v.1.2 v.1.1) :=
    Computable.cond (Computable.nat_bodd.comp n) (snd.comp fst) (fst.comp fst)
  have hi := Primrec₂.natPair.to_comp.comp (fst.comp (Computable.unpair.comp snd))
    ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.comp n)
  exact (Nat.Partrec.Code.eval_part.comp hc hi).of_eq (fun v => by
    cases hb : (Nat.unpair v.2).2.bodd <;> simp [dispatch, hb])

noncomputable def dispatcher : Nat.Partrec.Code := Classical.choose (partrec_code dispatch_partrec)

noncomputable def joined (e f : Nat.Partrec.Code) : Nat.Partrec.Code :=
  dispatcher.curry (encode (e, f))

end TuringRigidity.IndexJoin

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexPresentation
open Encodable TableIndices IndexMatrix OrderNormalForm

abbrev Dom (Y : Oracle) (e : ℕ) := Valid Y (machine e)
def LE (Y : Oracle) (e f : ℕ) : Prop := ∃ d, ∀ q, ∃ r, orderMatrix Y e f d q r
noncomputable def joinIndex (e f : ℕ) : ℕ := encode (IndexJoin.joined (machine e) (machine f))

noncomputable def value (Y : Oracle) (e : ℕ) : Degree := by
  classical
  exact if h : Dom Y e then degree (output Y ⟨machine e, h⟩) else ⊥

end TuringRigidity.IndexPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle IndexMatrix OrderNormalForm IndexPresentation

theorem exists_form {Y n P} (h : Pi Y n P) :
    Sigma Y (n+1) (fun x => ∃ a, P (Nat.pair x a)) := ⟨P, h, fun _ => Iff.rfl⟩

end TuringRigidity.ArithmeticHierarchy

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleJump
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleJump
open Encodable UniformOracle CommonIdeal TableIndices IndexMatrix ArithmeticHierarchy

def Halts (Y : Oracle) (e n : ℕ) : Prop := ∃ z a, a ∈ TableIndices.run Y (machine e) n z

noncomputable def jump (Y : Oracle) : Oracle := by
  classical
  exact fun v => decide (Halts Y (Nat.unpair v).1 (Nat.unpair v).2)

theorem partial_table {Y : Oracle} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn {oracleFunction Y} f) :
    ∃ e, ∀ n, Halts Y e n ↔ (f n).Dom := by
  obtain ⟨c, hc⟩ := OracleCode.exists_code hf
  have hh : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) c n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec c
  obtain ⟨d, hd⟩ := partrec_code hh
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) c n :=
    fun L n => hd (L,n)
  have ha (n : ℕ) : Approximates (f n)
      (fun m => d.eval (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd', ← hc]
    exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (Y k))) c n
  refine ⟨encode d, fun n => ?_⟩
  constructor
  · rintro ⟨z,a,ha'⟩
    simp only [machine_encode] at ha'
    exact ((ha n).1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound ha')).1
  · intro hf'
    obtain ⟨m,hm⟩ := (ha n).2 ((f n).get hf') ⟨hf',rfl⟩
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t, (f n).get hf', by simpa [TableIndices.run, trial] using ht⟩

theorem domain_recursive_jump {Y : Oracle} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn {oracleFunction Y} f) :
    RecursivePred (jump Y) (fun n => (f n).Dom) := by
  classical
  obtain ⟨e,he⟩ := partial_table hf
  have hq : Nat.RecursiveIn {oracleFunction (jump Y)} (oracleFunction (jump Y)) :=
    .oracle _ (Set.mem_singleton _)
  have h := Nat.RecursiveIn.comp hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp (Primrec.const e) Primrec.id))
  exact h.of_eq (fun n => by
    change (Part.some (Nat.pair e n)).bind
      (fun input => Part.some (if jump Y input then 1 else 0)) = _
    rw [Part.bind_some]
    simp [jump, he])

theorem exists_recursive_jump {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    RecursivePred (jump Y) (fun x => ∃ a, P (Nat.pair x a)) := by
  classical
  have hN := recursive_not hP
  have hs := Nat.RecursiveIn.rfind hN
  have hd := domain_recursive_jump hs
  apply Form.congr (n := 0) (s := true) hd
  intro x
  erw [Nat.rfind_dom]
  simp

noncomputable def iterate (Y : Oracle) : ℕ → Oracle
  | 0 => Y
  | n+1 => jump (iterate Y n)

end TuringRigidity.OracleJump

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleJump
open Encodable UniformOracle CommonIdeal TableIndices IndexMatrix ArithmeticHierarchy

theorem recursive_transfer {Y Z : Oracle} {P : ℕ → Prop}
    (h : RecursivePred Y P) (hYZ : Reduces Y Z) : RecursivePred Z P :=
  RecursiveIn.iff_nat.mp (TuringReducible.trans (RecursiveIn.iff_nat.mpr h) hYZ)

theorem recursive_lift {Y : Oracle} {P : ℕ → Prop} (h : RecursivePred Y P) :
    RecursivePred (jump Y) P := by
  have hh := exists_recursive_jump (recursive_comp h (Primrec.fst.comp Primrec.unpair))
  exact Form.congr (n := 0) (s := true) hh (fun x => by simp)

theorem halts_sigma (Y : Oracle) :
    Sigma Y 1 (fun v => Halts Y (Nat.unpair v).1 (Nat.unpair v).2) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have ht := _root_.OAI.TuringRigidity.UniformOracle.total_comp (run_uniform_recursive Y) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (s.comp f) s)))
  have hcheck : Primrec (fun v : ℕ => bit ((decode (α := Option ℕ) v).getD none).isSome) :=
    bit_primrec.comp (Primrec.option_isSome.comp
      (Primrec.option_getD.comp Primrec.decode (Primrec.const none)))
  have h : RecursivePred Y (fun v =>
      (TableIndices.run Y (machine (Nat.unpair (Nat.unpair v).1).1)
        (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2).isSome = true) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hcheck) ht).of_eq (fun v => by
      simp only [Nat.unpair_pair, encodek, Option.getD_some, bit]
      congr 1
      split <;> rfl)
  apply (exists_form (n := 0) h).congr
  intro v
  simp only [Nat.unpair_pair, Halts]
  apply exists_congr
  intro z
  cases TableIndices.run Y (machine (Nat.unpair v).1) (Nat.unpair v).2 z <;> simp

theorem jump_mono {Y Z : Oracle} (hYZ : Reduces Y Z) : Reduces (jump Y) (jump Z) := by
  obtain ⟨Q,hQ,he⟩ := halts_sigma Y
  have h := exists_recursive_jump (recursive_transfer hQ hYZ)
  have h' : RecursivePred (jump Z) (fun v => Halts Y (Nat.unpair v).1 (Nat.unpair v).2) :=
    Form.congr (n := 0) (s := true) h (fun v => (he v).symm)
  apply RecursiveIn.iff_nat.mpr
  exact h'.of_eq (fun v => by
    classical
    by_cases h : Halts Y (Nat.unpair v).1 (Nat.unpair v).2 <;> simp [oracleFunction, jump, h])

noncomputable def degreeJump (x : Degree) : Degree :=
  Quotient.liftOn x (fun Y => degree (jump Y)) (fun Y Z h =>
    (degree_eq_iff (jump Y) (jump Z)).mpr ⟨jump_mono h.1, jump_mono h.2⟩)

@[simp] theorem degreeJump_degree (Y : Oracle) : degreeJump (degree Y) = degree (jump Y) := rfl

end TuringRigidity.OracleJump

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveWitness
open UniformOracle ArithmeticHierarchy OracleJump

noncomputable def least (P : ℕ → Prop) (ht : ∀ x, ∃ a, P (Nat.pair x a)) (x : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (ht x)

theorem least_spec (P : ℕ → Prop) (ht : ∀ x, ∃ a, P (Nat.pair x a)) (x : ℕ) :
    P (Nat.pair x (least P ht x)) := by
  classical
  exact Nat.find_spec (ht x)

theorem least_recursive {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P)
    (ht : ∀ x, ∃ a, P (Nat.pair x a)) :
    Nat.RecursiveIn {oracleFunction Y} (fun x => Part.some (least P ht x)) := by
  classical
  have hr := Nat.RecursiveIn.rfind (recursive_not hP)
  apply hr.of_eq_tot
  intro x
  apply Nat.mem_rfind.mpr
  constructor
  · simp [least_spec P ht x]
  · intro a ha
    have hn := Nat.find_min (ht x) (show a < Nat.find (ht x) from ha)
    simp [hn]

def Accept (P : ℕ → Prop) (v : ℕ) : Prop :=
  ((Nat.unpair v).2 = 0 ∧ ¬ ∃ a, P (Nat.pair (Nat.unpair v).1 a)) ∨
    (0 < (Nat.unpair v).2 ∧ P (Nat.pair (Nat.unpair v).1 ((Nat.unpair v).2 - 1)))

theorem accept_total (P : ℕ → Prop) : ∀ x, ∃ a, Accept P (Nat.pair x a) := by
  intro x
  by_cases h : ∃ a, P (Nat.pair x a)
  · obtain ⟨a,ha⟩ := h
    exact ⟨a+1, Or.inr ⟨by simp, by simpa using ha⟩⟩
  · exact ⟨0, Or.inl ⟨by simp, by simpa using h⟩⟩

theorem accept_recursive {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    RecursivePred (jump Y) (Accept P) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hz : RecursivePred (jump Y) (fun v => (Nat.unpair v).2 = 0) :=
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.ite (Primrec.eq.comp s (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0))).of_eq
      (fun v => by by_cases h : (Nat.unpair v).2 = 0 <;> simp [h])
  have hp : RecursivePred (jump Y) (fun v => 0 < (Nat.unpair v).2) :=
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) s) (Primrec.const 1) (Primrec.const 0))).of_eq
      (fun v => by by_cases h : 0 < (Nat.unpair v).2 <;> simp [h])
  have hn := recursive_comp (recursive_not (exists_recursive_jump hP)) f
  have hy := recursive_comp (recursive_lift hP)
    (Primrec₂.natPair.comp f (Primrec.nat_sub.comp s (Primrec.const 1)))
  exact Form.or (n := 0) (s := true) (recursive_and hz hn) (recursive_and hp hy)

noncomputable def witness (P : ℕ → Prop) (x : ℕ) : ℕ :=
  least (Accept P) (accept_total P) x

theorem witness_recursive {Y : Oracle} {P : ℕ → Prop} (hP : RecursivePred Y P) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (witness P x)) :=
  least_recursive (accept_recursive hP) (accept_total P)

theorem witness_spec (P : ℕ → Prop) (x : ℕ) :
    (witness P x = 0 ∧ ¬ ∃ a, P (Nat.pair x a)) ∨
      (0 < witness P x ∧ P (Nat.pair x (witness P x - 1))) := by
  simpa only [Accept, Nat.unpair_pair, witness] using least_spec (Accept P) (accept_total P) x

theorem sigma1_choice {Y : Oracle} {P : ℕ → Prop} (hP : Sigma Y 1 P) :
    ∃ f : ℕ → ℕ, Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (f x)) ∧
      ∀ x, (f x = 0 ∧ ¬ ∃ a, P (Nat.pair x a)) ∨
        (0 < f x ∧ P (Nat.pair x (f x - 1))) := by
  obtain ⟨Q,hQ,he⟩ := hP
  let Q' : ℕ → Prop := fun v => Q
    (Nat.pair (Nat.pair (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1)
      (Nat.unpair (Nat.unpair v).2).2)
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  have hQ' : RecursivePred Y Q' := recursive_comp hQ
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp fst (fst.comp snd)) (snd.comp snd))
  let f : ℕ → ℕ := fun x => if witness Q' x = 0 then 0 else (Nat.unpair (witness Q' x - 1)).1 + 1
  have hf : Primrec (fun v : ℕ => if v = 0 then 0 else (Nat.unpair (v-1)).1+1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
      (Primrec.succ.comp (fst.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))))
  have hrec := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (jump Y)}) hf) (witness_recursive hQ')
  refine ⟨f, hrec.of_eq (fun x => rfl), fun x => ?_⟩
  rcases witness_spec Q' x with ⟨hz,hn⟩ | ⟨hp,hy⟩
  · refine Or.inl ⟨by simp [f,hz], ?_⟩
    rintro ⟨a,ha⟩
    obtain ⟨b,hb⟩ := (he _).mp ha
    exact hn ⟨Nat.pair a b, by simpa [Q'] using hb⟩
  · have hn : witness Q' x ≠ 0 := by omega
    refine Or.inr ⟨by simp [f,hn], ?_⟩
    simp only [f, ite_eq_right hn, Nat.add_sub_cancel]
    exact (he _).mpr ⟨(Nat.unpair (witness Q' x - 1)).2, by simpa [Q'] using hy⟩

end TuringRigidity.EffectiveWitness

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenHalting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenHalting
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing IndexMatrix

def initial (G : Oracle) (m : ℕ) : List Bool := (List.range m).map G

@[simp] theorem initial_length (G : Oracle) (m : ℕ) : (initial G m).length = m := by simp [initial]

end TuringRigidity.CohenHalting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_EffectiveForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveForcing
open UniformOracle ArithmeticHierarchy OracleJump EffectiveWitness EncodedForcing CodingForcing

def answer (v : ℕ) : ℕ := if (Nat.unpair v).2 = 0 then (Nat.unpair v).1 else (Nat.unpair v).2 - 1

theorem answer_primrec : Primrec answer := Primrec.ite
  (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))
  (Primrec.fst.comp Primrec.unpair)
  (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1))

theorem uniform_open_decision (Y B : Oracle) (hB : Reduces B Y) :
    ∃ step : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (step x)) ∧
      ∀ e p, Extends (columns B) (condition p) (condition (step (Nat.pair e p))) ∧
        (Halts Y e (step (Nat.pair e p)) ∨
          ∀ q, Extends (columns B) (condition (step (Nat.pair e p))) (condition q) → ¬ Halts Y e q) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let P : ℕ → Prop := fun v =>
    Extends (columns B) (condition (Nat.unpair (Nat.unpair v).1).2) (condition (Nat.unpair v).2) ∧
      Halts Y (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair v).2
  have hext := recursive_transfer
    (recursive_comp (extends_recursive B) (Primrec₂.natPair.comp (r.comp f) r)) hB
  have hhalt := (halts_sigma Y).comp (Primrec₂.natPair.comp (f.comp f) r)
  have hP : Sigma Y 1 P := by
    simpa only [P,Nat.unpair_pair] using (Form.raise (n := 0) (s := true) hext).and hhalt
  obtain ⟨g,hg,hs⟩ := sigma1_choice hP
  let step : ℕ → ℕ := fun x => answer (Nat.pair (Nat.unpair x).2 (g x))
  have hstep := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (jump Y)}) answer_primrec)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r) hg)
  refine ⟨step,hstep,fun e p => ?_⟩
  rcases hs (Nat.pair e p) with ⟨hz,hn⟩ | ⟨hp,hw⟩
  · have he : step (Nat.pair e p) = p := by simp [step,answer,hz]
    rw [he]
    refine ⟨extends_refl _ _,Or.inr (fun q hq hhalt => ?_)⟩
    exact hn ⟨q,by simpa [P] using And.intro hq hhalt⟩
  · have hz : g (Nat.pair e p) ≠ 0 := by omega
    have he : step (Nat.pair e p) = g (Nat.pair e p) - 1 := by simp [step,answer,hz]
    rw [he]
    have hh : Extends (columns B) (condition p) (condition (g (Nat.pair e p)-1)) ∧
        Halts Y e (g (Nat.pair e p)-1) := by simpa [P] using hw
    exact ⟨hh.1,Or.inl hh.2⟩

end TuringRigidity.EffectiveForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_UniformArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable

abbrev Oracles := ℕ → Oracle
abbrev Predicate := Oracles → ℕ → Prop
abbrev left (v : ℕ) := (Nat.unpair v).1
abbrev right (v : ℕ) := (Nat.unpair v).2

theorem left_primrec : Primrec left := Primrec.fst.comp Primrec.unpair
theorem right_primrec : Primrec right := Primrec.snd.comp Primrec.unpair

inductive Arith : Predicate → Prop where
  | pure (P : ℕ → Prop) : PrimrecPred P → Arith (fun _ v => P v)
  | query (i : ℕ) : Arith (fun O v => O i v = true)
  | neg {P} : Arith P → Arith (fun O v => ¬ P O v)
  | and {P Q} : Arith P → Arith Q → Arith (fun O v => P O v ∧ Q O v)
  | ex {P} : Arith P → Arith (fun O v => ∃ n, P O (Nat.pair v n))
  | comp {P} (f : ℕ → ℕ) : Arith P → Primrec f → Arith (fun O v => P O (f v))

end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticFiniteTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic

inductive Term where
  | input : Term
  | const : ℕ → Term
  | prim (f : ℕ → ℕ) (hf : Primrec f) : Term → Term
  | pair : Term → Term → Term
  | witness : Term → Term

namespace Term

def eval (O : ℕ → ℕ) (v : ℕ) : Term → ℕ
  | .input => v
  | .const n => n
  | .prim f _ t => f (t.eval O v)
  | .pair t s => Nat.pair (t.eval O v) (s.eval O v)
  | .witness t => O (t.eval O v)

def left (t : Term) : Term := .prim UniformArithmetic.left left_primrec t
def right (t : Term) : Term := .prim UniformArithmetic.right right_primrec t

def subst (t : Term) (inputTerm : Term) (query : Term → Term) : Term :=
  match t with
  | .input => inputTerm
  | .const n => .const n
  | .prim f hf t => .prim f hf (t.subst inputTerm query)
  | .pair t s => .pair (t.subst inputTerm query) (s.subst inputTerm query)
  | .witness t => query (t.subst inputTerm query)

end Term

inductive Test where
  | pure (P : ℕ → Prop) (hP : PrimrecPred P) : Term → Test
  | query : ℕ → Term → Test
  | neg : Test → Test
  | and : Test → Test → Test

namespace Test

def eval (O : Oracles) (f : ℕ → ℕ) (v : ℕ) : Test → Prop
  | .pure P _ t => P (t.eval f v)
  | .query i t => O i (t.eval f v) = true
  | .neg t => ¬ t.eval O f v
  | .and t s => t.eval O f v ∧ s.eval O f v

def subst (inputTerm : Term) (query : Term → Term) : Test → Test
  | .pure P hP t => .pure P hP (t.subst inputTerm query)
  | .query i t => .query i (t.subst inputTerm query)
  | .neg t => .neg (t.subst inputTerm query)
  | .and t s => .and (t.subst inputTerm query) (s.subst inputTerm query)

def or (t s : Test) : Test := .neg (.and (.neg t) (.neg s))

@[simp] theorem eval_or (t s : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    (t.or s).eval O f v ↔ t.eval O f v ∨ s.eval O f v := by
  classical
  change (¬ (¬ t.eval O f v ∧ ¬ s.eval O f v)) ↔ _
  tauto

def Presents (t : Test) (P : Predicate) : Prop :=
  ∀ O v, P O v ↔ ∃ f : ℕ → ℕ, ∀ n, t.eval O f (Nat.pair v n)
end Test

end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingColumns
open PrefixComputability

def column (A : Oracle) (k cutoff : ℕ) (m : ℕ) : Bool :=
  if cutoff ≤ m ∧ (Nat.unpair m).1 = k then A (Nat.unpair m).2 else false

@[simp] theorem column_pair (A : Oracle) (k cutoff a : ℕ) :
    column A k cutoff (Nat.pair k a) = (if cutoff ≤ Nat.pair k a then A a else false) := by
  simp [column]

end TuringRigidity.CodingColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_AntichainParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AntichainParameters

def NontrivialCommonLower (b g₀ g₁ x : Degree) : Prop :=
  x ≤ b ∧ ∃ z : Degree, z ≤ g₀ ⊔ x ∧ z ≤ g₁ ⊔ x ∧ ¬ z ≤ x

def CodedAntichain (b g₀ g₁ x : Degree) : Prop :=
  NontrivialCommonLower b g₀ g₁ x ∧
    ∀ y : Degree, NontrivialCommonLower b g₀ g₁ y → y ≤ x → x ≤ y

end TuringRigidity.AntichainParameters

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_SetCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetCoding
open AntichainParameters

structure AntichainCode where
  bound : Degree
  left : Degree
  right : Degree

def AntichainCode.Holds (p : AntichainCode) (x : Degree) : Prop :=
  CodedAntichain p.bound p.left p.right x

structure SetCode where
  bound : Degree
  tags : AntichainCode
  decorated : AntichainCode

def SetCode.Graph (p : SetCode) (x c : Degree) : Prop :=
  x ≤ p.bound ∧ p.tags.Holds c ∧ p.decorated.Holds (x ⊔ c)

end TuringRigidity.SetCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RelationCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCoding
open SetCoding

structure RelationCode (n : ℕ) where
  coordinates : Fin n → SetCode
  tuples : AntichainCode

def RelationCode.Holds {n : ℕ} (p : RelationCode n) (v : Fin n → Degree) : Prop :=
  ∃ c : Fin n → Degree,
    (∀ i, (p.coordinates i).Graph (v i) (c i)) ∧
      p.tuples.Holds (Finset.univ.sup c)

end TuringRigidity.RelationCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_AntichainDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AntichainDecoding
open IndexPresentation ArithmeticHierarchy SetCoding

def Nontrivial (Y : Oracle) (b l r x : ℕ) : Prop :=
  LE Y x b ∧ ∃ z, Dom Y z ∧ LE Y z (joinIndex l x) ∧
    LE Y z (joinIndex r x) ∧ ¬ LE Y z x

def Minimal (Y : Oracle) (b l r x : ℕ) : Prop :=
  ∀ w, Dom Y w → Nontrivial Y b l r w → LE Y w x → LE Y x w

def Antichain (Y : Oracle) (b l r x : ℕ) : Prop :=
  Nontrivial Y b l r x ∧ Minimal Y b l r x

end TuringRigidity.AntichainDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexTuples
open Encodable IndexPresentation IndexMatrix TableIndices

def entry : ℕ → ℕ → ℕ
  | 0, t => (Nat.unpair t).1
  | i+1, t => entry i (Nat.unpair t).2

end TuringRigidity.IndexTuples

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DecodingTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.DecodingTheorem
open IndexPresentation IndexTuples ArithmeticHierarchy
open SetCoding RelationCoding OracleJump

def Presented {n} (Y : Oracle) (p : RelationCode n) (t : ℕ) : Prop :=
  (∀ i : Fin n, Dom Y (entry i.val t)) ∧ p.Holds (fun i => value Y (entry i.val t))

end TuringRigidity.DecodingTheorem

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticModelDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticModelDecoding
open IndexPresentation IndexTuples ArithmeticHierarchy DecodingTheorem
open SetCoding RelationCoding OracleJump

def one (a : Degree) : Fin 1 → Degree := ![a]
def two (a b : Degree) : Fin 2 → Degree := ![a,b]
def oneIndex (a : ℕ) : ℕ := Nat.pair a 0
def twoIndex (a b : ℕ) : ℕ := Nat.pair a (Nat.pair b 0)

structure Copy (U : ℕ → Prop) where
  node : ℕ → Degree
  injective : Function.Injective node
  successor : RelationCode 2
  predicate : RelationCode 1
  successor_spec : ∀ a b, successor.Holds (two a b) ↔ ∃ k, a = node k ∧ b = node (k+1)
  predicate_spec : ∀ a, predicate.Holds (one a) ↔ ∃ k, U k ∧ a = node k

def Path (Y : Oracle) (S : RelationCode 2) (z n t : ℕ) : Prop :=
  Dom Y (item t 0) ∧ LE Y (item t 0) z ∧ LE Y z (item t 0) ∧
    ∀ i < n, Presented Y S (twoIndex (item t i) (item t (i+1)))

def Defined (Y : Oracle) (S : RelationCode 2) (P : RelationCode 1) (z n : ℕ) : Prop :=
  ∃ t, Path Y S z n t ∧ Presented Y P (oneIndex (item t n))

end TuringRigidity.ArithmeticModelDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticOracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing
noncomputable section

def tableGraph (B : Oracle) (e n : ℕ) : Prop :=
  ∃ z, run B (machine e) n z = some 1

def tableOracle (B : Oracle) (e : ℕ) : Oracle := by
  classical
  exact fun n => decide (tableGraph B e n)

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentRestrictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentRestrictions
open Set

structure CountableIdeal where
  carrier : Set Degree
  nonempty : carrier.Nonempty
  countable : carrier.Countable
  lower : ∀ ⦃a b : Degree⦄, a ≤ b → b ∈ carrier → a ∈ carrier
  join_mem : ∀ ⦃a b : Degree⦄, a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier

instance instCoeSortCountableIdealType : CoeSort CountableIdeal Type := ⟨fun I => {a : Degree // a ∈ I.carrier}⟩

end TuringRigidity.PersistentRestrictions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjury
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjury

open CodingForcing

def atLevel (p : Condition) (t : ℕ) : Condition :=
  ⟨p.left, p.right, p.sameLength, t⟩

end TuringRigidity.FiniteInjury

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjurySchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjurySchedule
open FiniteInjury

theorem exists_missing (seen : Finset ℕ) : ∃ t, t ∉ seen := by
  refine ⟨seen.sup id + 1,?_⟩
  intro h
  have hh : seen.sup id + 1 ≤ seen.sup id := Finset.le_sup (f := id) h
  omega

noncomputable def visit (seen : Finset ℕ) : ℕ := Nat.find (exists_missing seen)

end TuringRigidity.FiniteInjurySchedule

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StageRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StageRecords
open Encodable UniformOracle EncodedForcing FiniteInjurySchedule

def record (n : ℕ) : List ℕ := (decode n).getD []

def members (n : ℕ) : Finset ℕ := (record n).toFinset

noncomputable def nextVisit (n : ℕ) : ℕ := visit (members n)

def seenInsert (n t : ℕ) : ℕ := encode (t :: record n)

@[simp] theorem members_seenInsert (n t : ℕ) : members (seenInsert n t) = insert t (members n) := by
  simp [members,seenInsert,record]

end TuringRigidity.StageRecords

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StageNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StageNormalization
open Encodable UniformOracle EncodedForcing StageRecords

def normalized (A : Oracle) : Oracle := fun v =>
  Introreducible.prefixSet (columns A (Nat.unpair v).1) (Nat.unpair v).2

@[simp] theorem normalized_column (A : Oracle) (k : ℕ) :
    columns (normalized A) k = Introreducible.prefixSet (columns A k) := by
  funext n
  simp [normalized,columns]

end TuringRigidity.StageNormalization

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

def openProcedure (A : Oracle) : ℕ → ℕ :=
  Classical.choose (EffectiveForcing.uniform_open_decision A A (reduces_refl A))

structure State where
  condition : Condition
  done : Finset ℕ
  seen : Finset ℕ

def generic (A : Oracle) (p : State) : Condition :=
  EncodedForcing.condition (openProcedure A (Nat.pair (FiniteInjurySchedule.visit p.seen) (code p.condition)))

end
end TuringRigidity.GuardedStage

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def levelCode (p t : ℕ) : ℕ := Nat.pair (encode (left p)) (Nat.pair (encode (right p)) t)

@[simp] theorem condition_levelCode (p t : ℕ) : condition (levelCode p t) = atLevel (condition p) t :=
  condition_code (atLevel (condition p) t)

end
end TuringRigidity.GuardedComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

def state (v : ℕ) : GuardedStage.State :=
  ⟨condition (Nat.unpair v).1,members (Nat.unpair (Nat.unpair v).2).1,members (Nat.unpair (Nat.unpair v).2).2⟩

def canonical (p : ℕ) : ℕ := levelCode p (active p)

def genericCanonical (A : Oracle) (v : ℕ) : ℕ := GuardedStage.openProcedure A
  (Nat.pair (nextVisit (Nat.unpair (Nat.unpair v).2).2) (canonical (Nat.unpair v).1))

@[simp] theorem generic_eq (A : Oracle) (v : ℕ) :
    condition (genericCanonical A v) = GuardedStage.generic A (state v) := rfl

end
end TuringRigidity.GuardedComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveFamilies
open Encodable EncodedForcing UniformOracle SetCoding

def slice (A : Oracle) (i : ℕ) : Oracle := fun m =>
  A (Nat.pair (Nat.pair i (Nat.unpair m).1) (Nat.unpair m).2)

@[simp] theorem slice_column (A : Oracle) (i j : ℕ) :
    columns (slice A i) j = columns A (Nat.pair i j) := by
  funext n
  simp [slice,columns]

def mix (A B : Oracle) : Oracle := fun m =>
  join (columns A (Nat.unpair m).1) (columns B (Nat.unpair m).1) (Nat.unpair m).2

@[simp] theorem mix_column (A B : Oracle) (j : ℕ) :
    columns (mix A B) j = join (columns A j) (columns B j) := by
  funext n
  simp [mix,columns]

end TuringRigidity.EffectiveFamilies

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectivePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectivePresentation
open EncodedForcing UniformOracle ArithmeticHierarchy EffectiveFamilies
open SetCoding RelationCoding AntichainParameters
noncomputable section
attribute [local instance] Classical.propDecidable

def pick (P : ℕ → Prop) (j₀ j : ℕ) : ℕ := if P j then j else j₀

def selected (A : Oracle) (P : ℕ → Prop) (j₀ : ℕ) : Oracle := fun v =>
  A (Nat.pair (Nat.pair (Nat.unpair (Nat.unpair v).1).1
    (pick P j₀ (Nat.unpair (Nat.unpair v).1).2)) (Nat.unpair v).2)

@[simp] theorem selected_column (A : Oracle) (P : ℕ → Prop) (j₀ i j : ℕ) :
    columns (selected A P j₀) (Nat.pair i j) = columns A (Nat.pair i (pick P j₀ j)) := by
  funext n
  simp [selected,columns]

end
end TuringRigidity.EffectivePresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FixedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FixedArithmetic
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding

def rows (C : Oracle) : Oracle := fun v =>
  C (Nat.pair (if (Nat.unpair (Nat.unpair v).1).1 = 0 then (Nat.unpair (Nat.unpair v).1).2
    else (Nat.unpair (Nat.unpair v).1).2+1) (Nat.unpair v).2)

@[simp] theorem row_zero (C : Oracle) (k : ℕ) : columns (rows C) (Nat.pair 0 k) = columns C k := by
  funext n
  simp [columns,rows]

@[simp] theorem row_one (C : Oracle) (k : ℕ) : columns (rows C) (Nat.pair 1 k) = columns C (k+1) := by
  funext n
  simp [columns,rows]

end TuringRigidity.FixedArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealInterpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation
open AntichainParameters SetCoding RelationCoding

structure DegreeIdeal where
  carrier : Set Degree
  nonempty : carrier.Nonempty
  lower : ∀ {x y}, x ≤ y → y ∈ carrier → x ∈ carrier
  join_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x ⊔ y ∈ carrier

structure Element (I : DegreeIdeal) where
  val : Degree
  property : val ∈ I.carrier

instance instCoeSortDegreeIdealType : CoeSort DegreeIdeal Type := ⟨Element⟩

@[ext] theorem Element.ext {I : DegreeIdeal} (x y : I) (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

instance instPartialOrderElement (I : DegreeIdeal) : PartialOrder I :=
  PartialOrder.lift Element.val (fun x y h => Element.ext x y h)

instance instSemilatticeSupElement (I : DegreeIdeal) : SemilatticeSup (Element I) where
  toPartialOrder := inferInstance
  sup x y := ⟨x.val ⊔ y.val,I.join_mem x.property y.property⟩
  le_sup_left := by
    intro x y
    change x.val ≤ x.val ⊔ y.val
    exact le_sup_left
  le_sup_right := by
    intro x y
    change y.val ≤ x.val ⊔ y.val
    exact le_sup_right
  sup_le := by
    intro x y z hx hy
    change x.val ⊔ y.val ≤ z.val
    exact sup_le hx hy

instance instOrderBotElement (I : DegreeIdeal) : OrderBot (Element I) where
  bot := ⟨⊥,by obtain ⟨x,hx⟩ := I.nonempty; exact I.lower bot_le hx⟩
  bot_le := by
    intro x
    change (⊥ : Degree) ≤ x.val
    exact bot_le

@[simp] theorem coe_sup {I : DegreeIdeal} (x y : I) : (x ⊔ y).val = x.val ⊔ y.val := rfl
@[simp] theorem coe_bot (I : DegreeIdeal) : (⊥ : I).val = (⊥ : Degree) := rfl

end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GlobalLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GlobalLocality
open OracleJump IdealInterpretation
noncomputable section

def degreeIterate (x : Degree) : ℕ → Degree
  | 0 => x
  | n+1 => degreeJump (degreeIterate x n)

@[simp] theorem degreeIterate_degree (X : Oracle) (n : ℕ) :
    degreeIterate (degree X) n = degree (iterate X n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [degreeIterate,ih,degreeJump_degree]; rfl

end
end TuringRigidity.GlobalLocality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_EnumerationConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EnumerationConstruction
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding

def rows (C H : Oracle) : Oracle := fun v =>
  if (Nat.unpair (Nat.unpair v).1).1 = 0 then C (Nat.pair (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2)
  else H (Nat.pair (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2)

@[simp] theorem row_zero (C H : Oracle) (k : ℕ) : columns (rows C H) (Nat.pair 0 k) = columns C k := by
  funext n; simp [columns,rows]

@[simp] theorem row_one (C H : Oracle) (k : ℕ) : columns (rows C H) (Nat.pair 1 k) = columns H k := by
  funext n; simp [columns,rows]

end TuringRigidity.EnumerationConstruction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericalAutomorphism
open EncodedForcing PersistentRestrictions
noncomputable section

structure Action (H : Oracle) (P : ℕ → Prop) : Prop where
  total : ∀ n, ∃ m, P (Nat.pair n m)
  onto : ∀ m, ∃ n, P (Nat.pair n m)
  order : ∀ n m n' m', P (Nat.pair n m) → P (Nat.pair n' m') →
    (degree (columns H n) ≤ degree (columns H n') ↔
      degree (columns H m) ≤ degree (columns H m'))
  saturated : ∀ n m m', P (Nat.pair n m) →
    degree (columns H m) = degree (columns H m') → P (Nat.pair n m')

end
end TuringRigidity.NumericalAutomorphism

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericalIdeal
open EncodedForcing OracleJump IndexPresentation IdealInterpretation
open PersistentRestrictions
noncomputable section

structure JumpCode (H : Oracle) : Prop where
  lower : ∀ n e, Dom (columns H n) e →
    ∃ m, value (columns H n) e = degree (columns H m)
  join : ∀ n m, ∃ k, degree (columns H n) ⊔ degree (columns H m) = degree (columns H k)
  jump : ∀ n, ∃ m, degreeJump (degree (columns H n)) = degree (columns H m)

def Includes (A H : Oracle) : Prop := ∀ n, ∃ m, degree (columns A n) = degree (columns H m)

end
end TuringRigidity.NumericalIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericalExtension
open EncodedForcing PersistentRestrictions NumericalAutomorphism
noncomputable section

def Compatible (A H : Oracle) (R P : ℕ → Prop) : Prop :=
  ∀ i j n m, R (Nat.pair i j) → P (Nat.pair n m) →
    degree (columns A i) = degree (columns H n) →
    degree (columns A j) = degree (columns H m)

end
end TuringRigidity.NumericalExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticPersistence
open Encodable EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic
open PersistentRestrictions
open NumericalAutomorphism NumericalIdeal NumericalExtension
noncomputable section

def Criterion (A R : Oracle) : Prop :=
  ∀ H : Oracle, JumpCode H → Includes A H →
    ∃ e : ℕ, Action H (fun v => tableOracle (iterate H 11) e v = true) ∧
      Compatible A H (fun v => R v = true) (fun v => tableOracle (iterate H 11) e v = true)

def Matrix (O : Oracles) (_ : ℕ) : Prop :=
  JumpCode (O 2) → Includes (O 0) (O 2) →
    ∃ e : ℕ, Action (O 2) (fun v => tableOracle (iterate (O 2) 11) e v = true) ∧
      Compatible (O 0) (O 2) (fun v => O 1 v = true)
        (fun v => tableOracle (iterate (O 2) 11) e v = true)

end
end TuringRigidity.ArithmeticPersistence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RationalCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Encodable

namespace RationalCoding

def magnitude (n : ℕ) : ℕ := n/2+n%2

end RationalCoding
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

@[simp] theorem partialJoin_oracle (A B : Oracle) :
    partialJoin (oracleFunction A) (oracleFunction B) = oracleFunction (join A B) := by
  funext k
  cases hk : k.bodd <;> simp [partialJoin, oracleFunction, join, hk]

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteShuffle
open UniformOracle

def Agree (n : ℕ) (A B : Oracle) : Prop := ∀ i, i < n → A i = B i

def initial (A : Oracle) (n : ℕ) : List Bool := (List.range n).map A

@[simp] theorem prefix_length (A : Oracle) (n : ℕ) : (initial A n).length = n := by
  simp [initial]

@[simp] theorem prefix_getD (A : Oracle) (n i : ℕ) (hi : i < n) :
    (initial A n).getD i false = A i := by
  simp [initial,List.getD,hi]

def DenseOpen (D : List Bool → Prop) : Prop :=
  (∀ s, ∃ t, s <+: t ∧ D t) ∧ (∀ s t, s <+: t → D s → D t)

end TuringRigidity.FiniteShuffle

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ShuffleRequirements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ShuffleRequirements
open FiniteShuffle Set

def Realizes (s : List Bool) (G : Oracle) : Prop :=
  Agree s.length (fun i => s.getD i false) G

end TuringRigidity.ShuffleRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPrefixForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticPrefixForcing
open Encodable UniformArithmetic FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

abbrev PrefixPredicate := Oracles → ℕ → List Bool → Prop
abbrev ArithmeticPrefix (Q : PrefixPredicate) :=
  Arith (fun O v => Q O (left v) (word (right v)))

def Upward (Q : List Bool → Prop) : Prop :=
  ∀ s t, s <+: t → Q s → Q t

def Avoid (Q : List Bool → Prop) (s : List Bool) : Prop :=
  ∀ t, s <+: t → ¬ Q t

def Decides (Q : List Bool → Prop) (s : List Bool) : Prop := Q s ∨ Avoid Q s

def Generic (O : Oracles) (G : Oracle) : Prop :=
  ∀ D : Oracles → List Bool → Prop,
    Arith (fun O n => D O (word n)) → DenseOpen (D O) →
    ∃ s, D O s ∧ Realizes s G

end TuringRigidity.ArithmeticPrefixForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPresentationProperty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticPersistence
open EncodedForcing OracleJump UniformArithmetic PersistentRestrictions
open NumericalAutomorphism
noncomputable section

def parameters (A R H : Oracle) : Oracles
  | 0 => A
  | 1 => R
  | _ => H

end
end TuringRigidity.ArithmeticPersistence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticSkolem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section

def HasTest (P : Predicate) : Prop := ∃ t : Test, t.Presents P

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTestApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Approx := ℕ → Option ℕ

def Extends (s t : Approx) : Prop := ∀ i a, s i = some a → t i = some a

def Captures (s : Approx) (f : ℕ → ℕ) (N : ℕ) : Prop := ∀ i < N, s i = some (f i)

namespace Term

def approx (s : Approx) (v : ℕ) : Term → Option ℕ
  | .input => some v
  | .const n => some n
  | .prim g _ t => (t.approx s v).bind (fun a => some (g a))
  | .pair t u => (t.approx s v).bind (fun a => (u.approx s v).bind (fun b => some (Nat.pair a b)))
  | .witness t => (t.approx s v).bind s

theorem approx_mono (t : Term) {s u : Approx} (h : Extends s u) (v a : ℕ)
    (ha : t.approx s v = some a) : t.approx u v = some a := by
  induction t generalizing a with
  | input => exact ha
  | const n => exact ha
  | prim g hg t ih =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,ih b hb,he⟩
  | pair t w ih ik =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,c,hc,he⟩ := ha
    exact ⟨b,ih b hb,c,ik c hc,he⟩
  | witness t ih =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,ih b hb,h b a he⟩

@[simp] theorem approx_full (t : Term) (f : ℕ → ℕ) (v : ℕ) :
    t.approx (fun i => some (f i)) v = some (t.eval f v) := by
  induction t <;> simp_all [approx,eval]

end Term

namespace Test

def approx (O : Oracles) (s : Approx) (v : ℕ) : Test → Option Bool
  | .pure P _ t => (t.approx s v).bind (fun a => some (decide (P a)))
  | .query i t => (t.approx s v).bind (fun a => some (O i a))
  | .neg t => (t.approx O s v).bind (fun a => some (!a))
  | .and t u => (t.approx O s v).bind (fun a => (u.approx O s v).bind (fun b => some (a && b)))

theorem approx_mono (t : Test) (O : Oracles) {s u : Approx} (h : Extends s u)
    (v : ℕ) (a : Bool) (ha : t.approx O s v = some a) : t.approx O u v = some a := by
  induction t generalizing a with
  | pure P hP t =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,t.approx_mono h v b hb,he⟩
  | query i t =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,t.approx_mono h v b hb,he⟩
  | neg t ih =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,he⟩ := ha
    exact ⟨b,ih b hb,he⟩
  | and t w ih ik =>
    simp only [approx,Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨b,hb,c,hc,he⟩ := ha
    exact ⟨b,ih b hb,c,ik c hc,he⟩

@[simp] theorem approx_full (t : Test) (O : Oracles) (f : ℕ → ℕ) (v : ℕ) :
    t.approx O (fun i => some (f i)) v = some (decide (t.eval O f v)) := by
  induction t with
  | pure P hP t =>
    by_cases h : P (t.eval f v) <;> simp [approx,eval,h]
  | query i t => cases h : O i (t.eval f v) <;> simp [approx,eval,h]
  | neg t ih => by_cases h : t.eval O f v <;> simp [approx,eval,ih,h]
  | and t w ih ik =>
    by_cases ht : t.eval O f v <;> by_cases hw : w.eval O f v <;> simp [approx,eval,ih,ik,ht,hw]

theorem rejection_mono (t : Test) (O : Oracles) {s u : Approx} (h : Extends s u)
    (v : ℕ) (ha : t.approx O s v = some false) : t.approx O u v = some false :=
  t.approx_mono O h v false ha
end Test

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticWitnessTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev listApprox (s : List ℕ) : Approx := fun i => s[i]?

theorem listApprox_append (s t : List ℕ) : Extends (listApprox s) (listApprox (s ++ t)) := by
  intro i a ha
  obtain ⟨hi,_⟩ := List.getElem?_eq_some_iff.mp ha
  simpa only [listApprox,List.getElem?_append_left hi] using ha

def initialSegment (f : ℕ → ℕ) (n : ℕ) : List ℕ := List.ofFn (fun i : Fin n => f i.val)

@[simp] theorem prefix_length (f : ℕ → ℕ) (n : ℕ) : (initialSegment f n).length = n := by
  simp [initialSegment]

namespace Test

def accepts (t : Test) (O : Oracles) (v : ℕ) (s : List ℕ) : Prop :=
  ∀ n < s.length, t.approx O (listApprox s) (Nat.pair v n) ≠ some false

def tree (t : Test) (O : Oracles) (v : ℕ) : Descriptive.tree ℕ :=
  ⟨{s | t.accepts O v s},by
    intro s a h n hn he
    exact h n (by simp; omega) (t.rejection_mono O (listApprox_append s [a]) _ he)⟩

end Test

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTreeDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic Encodable
noncomputable section
attribute [local instance] Classical.propDecidable

def decodeNode (n : ℕ) : List ℕ := (decode (α := List ℕ) n).getD []

@[simp] theorem decodeNode_encode (s : List ℕ) : decodeNode (encode s) = s := by
  simp [decodeNode]

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistenceWitnessTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Test

def bindOracle (q : ℕ → Term → Test) : Test → Test
  | .pure P hP t => .pure P hP t
  | .query i t => q i t
  | .neg t => .neg (t.bindOracle q)
  | .and t s => .and (t.bindOracle q) (s.bindOracle q)

def realQuery : ℕ → Term → Test
  | 0, t => .query 0 t
  | 1, t => .query 1 t
  | _+2, t => .pure (fun n => n = 1)
      (Primrec.eq.comp Primrec.id (Primrec.const 1)) (.witness (.pair (.const 0) t))

def mergeReal (t : Test) : Test :=
  (t.subst .input (fun s => .witness (.pair (.const 1) s))).bindOracle realQuery

def realPart (f : ℕ → ℕ) : Oracle := fun n => decide (f (Nat.pair 0 n) = 1)
def witnessPart (f : ℕ → ℕ) : ℕ → ℕ := fun n => f (Nat.pair 1 n)

end Test

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_TransitiveNameModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open Set RecursiveNames
universe u

abbrev Conditions (p : ZFSet.{u}) : Type u := Shrink p

noncomputable def label (p : ZFSet.{u}) (q : Conditions p) : ZFSet.{u} :=
  ((equivShrink p).symm q).val

theorem label_injective (p : ZFSet.{u}) : Function.Injective (label p) :=
  fun _ _ h => (equivShrink p).symm.injective (Subtype.ext h)

def Transitive (M : ZFSet.{u}) : Prop := ∀ x ∈ M, ∀ y ∈ x, y ∈ M

noncomputable def valueOnCode (p : ZFSet.{u}) (G : Set (Conditions p))
    (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ τ : Name (Conditions p), Name.encode (label p) τ = x
    then Name.val G h.choose else ∅

noncomputable def genericExtensionSet (M p : ZFSet.{u}) (G : Set (Conditions p)) :
    ZFSet.{u} := ZFSet.range
      (fun x : {x : M // ∃ τ : Name (Conditions p), Name.encode (label p) τ = x.val} =>
        valueOnCode p G x.val.val)

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedSetTheory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open Set
open TransitiveNameModel (Transitive)
universe u

inductive Formula where
  | equal (i j : ℕ)
  | member (i j : ℕ)
  | conj (φ ψ : Formula)
  | neg (φ : Formula)
  | existsMem (i : ℕ) (φ : Formula)

def cons (x : ZFSet.{u}) (env : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => x
  | n+1 => env n

@[simp] theorem cons_zero (x : ZFSet.{u}) (env : ℕ → ZFSet.{u}) : cons x env 0 = x := rfl
@[simp] theorem cons_succ (x : ZFSet.{u}) (env : ℕ → ZFSet.{u}) (n : ℕ) :
    cons x env (n+1) = env n := rfl

def Formula.Eval (env : ℕ → ZFSet.{u}) : Formula → Prop
  | .equal i j => env i = env j
  | .member i j => env i ∈ env j
  | .conj φ ψ => Eval env φ ∧ Eval env ψ
  | .neg φ => ¬ Eval env φ
  | .existsMem i φ => ∃ x ∈ env i, Eval (cons x env) φ

def Formula.Realize (M : ZFSet.{u}) (env : ℕ → ZFSet.{u}) : Formula → Prop
  | .equal i j => env i = env j
  | .member i j => env i ∈ env j
  | .conj φ ψ => Realize M env φ ∧ Realize M env ψ
  | .neg φ => ¬ Realize M env φ
  | .existsMem i φ => ∃ x ∈ M, x ∈ env i ∧ Realize M (cons x env) φ

namespace Formula

def disj (φ ψ : Formula) : Formula := .neg (.conj (.neg φ) (.neg ψ))
def allMem (i : ℕ) (φ : Formula) : Formula := .neg (.existsMem i (.neg φ))

@[simp] theorem eval_disj (φ ψ : Formula) (env : ℕ → ZFSet.{u}) :
    (disj φ ψ).Eval env ↔ φ.Eval env ∨ ψ.Eval env := by
  classical
  simp only [disj,Eval]
  constructor
  · intro h
    by_cases hφ : φ.Eval env
    · exact Or.inl hφ
    · exact Or.inr (Classical.byContradiction (fun hψ => h ⟨hφ,hψ⟩))
  · intro h hn
    exact h.elim hn.1 hn.2

@[simp] theorem eval_allMem (i : ℕ) (φ : Formula) (env : ℕ → ZFSet.{u}) :
    (allMem i φ).Eval env ↔ ∀ x ∈ env i, φ.Eval (cons x env) := by
  classical
  simp [allMem,Eval]

def singleton (s a : ℕ) : Formula :=
  .conj (.member a s) (allMem s (.equal 0 (a+1)))

def unorderedPair (s a b : ℕ) : Formula :=
  .conj (.member a s) (.conj (.member b s)
    (allMem s (disj (.equal 0 (a+1)) (.equal 0 (b+1)))))

@[simp] theorem eval_singleton (s a : ℕ) (env : ℕ → ZFSet.{u}) :
    (singleton s a).Eval env ↔ env s = ({env a} : ZFSet.{u}) := by
  simp only [singleton,Eval,eval_allMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨ha,hall⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_singleton]
    exact ⟨hall x,fun hx => hx ▸ ha⟩
  · intro h
    simp [h]

@[simp] theorem eval_unorderedPair (s a b : ℕ) (env : ℕ → ZFSet.{u}) :
    (unorderedPair s a b).Eval env ↔ env s = ({env a,env b} : ZFSet.{u}) := by
  simp only [unorderedPair,Eval,eval_allMem,eval_disj,cons_zero,cons_succ]
  constructor
  · rintro ⟨ha,hb,hall⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_pair]
    exact ⟨hall x,fun hx => hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb)⟩
  · intro h
    simp [h]

def orderedPair (s a b : ℕ) : Formula :=
  .conj (allMem s (disj (singleton 0 (a+1)) (unorderedPair 0 (a+1) (b+1))))
    (.conj (.existsMem s (singleton 0 (a+1)))
      (.existsMem s (unorderedPair 0 (a+1) (b+1))))

@[simp] theorem eval_orderedPair (s a b : ℕ) (env : ℕ → ZFSet.{u}) :
    (orderedPair s a b).Eval env ↔ env s = ZFSet.pair (env a) (env b) := by
  simp only [orderedPair,Eval,eval_allMem,eval_disj,eval_singleton,
    eval_unorderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨hall,⟨x,hx,hxa⟩,y,hy,hyab⟩
    apply ZFSet.ext
    intro z
    change z ∈ env s ↔ z ∈ ({({env a} : ZFSet.{u}),({env a,env b} : ZFSet.{u})} : ZFSet.{u})
    rw [ZFSet.mem_pair]
    exact ⟨hall z,fun hz => hz.elim (fun h => h ▸ hxa ▸ hx) (fun h => h ▸ hyab ▸ hy)⟩
  · intro h
    rw [h]
    simp [ZFSet.pair]

def pairMem (a b s : ℕ) : Formula := .existsMem s (orderedPair 0 (a+1) (b+1))

@[simp] theorem eval_pairMem (a b s : ℕ) (env : ℕ → ZFSet.{u}) :
    (pairMem a b s).Eval env ↔ ZFSet.pair (env a) (env b) ∈ env s := by
  simp [pairMem,Eval]
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace Formula
def imp (φ ψ : Formula) : Formula := disj (.neg φ) ψ
def iff (φ ψ : Formula) : Formula := .conj (imp φ ψ) (imp ψ φ)

@[simp] theorem eval_imp (φ ψ : Formula) (e : ℕ → ZFSet.{u}) :
    (imp φ ψ).Eval e ↔ (φ.Eval e → ψ.Eval e) := by
  classical
  simp only [imp, eval_disj, Eval]
  constructor
  · intro h hp; exact h.elim (fun hn => False.elim (hn hp)) id
  · intro h; by_cases hp : φ.Eval e
    · exact Or.inr (h hp)
    · exact Or.inl hp

@[simp] theorem eval_iff (φ ψ : Formula) (e : ℕ → ZFSet.{u}) :
    (iff φ ψ).Eval e ↔ (φ.Eval e ↔ ψ.Eval e) := by
  simp only [iff, Eval, eval_imp, iff_def]

def subset (a b : ℕ) : Formula := allMem a (.member 0 (b+1))
def transitive (a : ℕ) : Formula := allMem a (subset 0 (a+1))

@[simp] theorem eval_subset (a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (subset a b).Eval e ↔ e a ⊆ e b := by
  simp only [subset, eval_allMem, Eval, cons_zero, cons_succ]
  rfl

@[simp] theorem eval_transitive (a : ℕ) (e : ℕ → ZFSet.{u}) :
    (transitive a).Eval e ↔ Transitive (e a) := by
  simp only [transitive, eval_allMem, eval_subset, cons_zero, cons_succ]
  rfl

def functionGraph (f d v : ℕ) : Formula :=
  .conj (allMem f (.existsMem (d+1) (.existsMem (v+2) (orderedPair 2 1 0))))
    (allMem d (.existsMem (v+1)
      (.conj (pairMem 1 0 (f+2))
        (allMem (v+2) (imp (pairMem 2 0 (f+3)) (.equal 0 1))))))

@[simp] theorem eval_functionGraph (f d v : ℕ) (e : ℕ → ZFSet.{u}) :
    (functionGraph f d v).Eval e ↔
      (∀ z ∈ e f, ∃ x ∈ e d, ∃ y ∈ e v, z = ZFSet.pair x y) ∧
      (∀ x ∈ e d, ∃ y ∈ e v, ZFSet.pair x y ∈ e f ∧
        ∀ z ∈ e v, ZFSet.pair x z ∈ e f → z = y) := by
  simp only [functionGraph, Eval, eval_allMem, eval_orderedPair,
    eval_pairMem, eval_imp, cons_zero, cons_succ]

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

def natSet : ℕ → ZFSet.{u}
  | 0 => ∅
  | n+1 => insert (natSet n) (natSet n)

theorem natSet_eq_mk (n : ℕ) : natSet.{u} n = ZFSet.mk (PSet.ofNat n) := by
  induction n with
  | zero => rfl
  | succ n ih => change insert (natSet n) (natSet n) = _; rw [ih]; rfl

theorem mem_natSet (n : ℕ) (x : ZFSet.{u}) :
    x ∈ natSet n ↔ ∃ i < n, x = natSet i := by
  induction n with
  | zero => simp [natSet]
  | succ n ih =>
    rw [natSet,ZFSet.mem_insert_iff,ih]
    constructor
    · rintro (rfl|⟨i,hi,hx⟩)
      · exact ⟨n,Nat.lt_succ_self n,rfl⟩
      · exact ⟨i,Nat.lt_succ_of_lt hi,hx⟩
    · rintro ⟨i,hi,hx⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
      · exact Or.inr ⟨i,hi,hx⟩
      · exact Or.inl hx

theorem natSet_injective : Function.Injective natSet.{u} := by
  intro n m h
  rcases Nat.lt_trichotomy n m with hn|he|hm
  · exact False.elim (ZFSet.mem_irrefl (natSet m)
      (h ▸ (mem_natSet m _).mpr ⟨n,hn,rfl⟩))
  · exact he
  · exact False.elim (ZFSet.mem_irrefl (natSet n)
      (h.symm ▸ (mem_natSet n _).mpr ⟨m,hm,rfl⟩))

theorem mem_omega (x : ZFSet.{u}) : x ∈ ZFSet.omega ↔ ∃ n, x = natSet n := by
  induction x using Quotient.inductionOn with
  | h x =>
    change (∃ n : ULift ℕ, PSet.Equiv x (PSet.ofNat n.down)) ↔ _
    constructor
    · rintro ⟨⟨n⟩,hn⟩
      exact ⟨n,(Quotient.sound hn).trans (natSet_eq_mk n).symm⟩
    · rintro ⟨n,hn⟩
      exact ⟨⟨n⟩,Quotient.exact (hn.trans (natSet_eq_mk n))⟩

namespace Formula
def empty (x : ℕ) : Formula := allMem x (.neg (.equal 0 0))
def successor (s n : ℕ) : Formula :=
  .conj (.member n s) (.conj (subset n s)
    (allMem s (disj (.equal 0 (n+1)) (.member 0 (n+1)))))

@[simp] theorem eval_empty (x : ℕ) (e : ℕ → ZFSet.{u}) :
    (empty x).Eval e ↔ e x = ∅ := by
  simp only [empty,eval_allMem,Eval,cons_zero,not_true_eq_false]
  constructor
  · intro h; apply ZFSet.ext; intro z; simp only [ZFSet.notMem_empty,iff_false]; exact h z
  · intro h; simp [h]

@[simp] theorem eval_successor (s n : ℕ) (e : ℕ → ZFSet.{u}) :
    (successor s n).Eval e ↔ e s = insert (e n) (e n) := by
  simp only [successor,Eval,eval_subset,eval_allMem,eval_disj,cons_zero,cons_succ]
  constructor
  · rintro ⟨hn,hsub,hall⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨hall z,fun h => h.elim (fun h => h ▸ hn) (fun h => hsub h)⟩
  · intro h; rw [h]
    exact ⟨ZFSet.mem_insert _ _,fun _ hz => ZFSet.mem_insert_of_mem _ hz,
      fun _ hz => ZFSet.mem_insert_iff.mp hz⟩

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

def liftMap (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => v i+1

namespace Formula

def rename (v : ℕ → ℕ) : Formula → Formula
  | .equal i j => .equal (v i) (v j)
  | .member i j => .member (v i) (v j)
  | .conj φ ψ => .conj (rename v φ) (rename v ψ)
  | .neg φ => .neg (rename v φ)
  | .existsMem i φ => .existsMem (v i) (rename (liftMap v) φ)

end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetPresentationDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetPresentationDecoding
open BoundedSetTheory TransitiveNameModel
universe u

noncomputable def classSet (d E x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair x y ∈ E) d

@[simp] theorem mem_classSet (d E x y : ZFSet.{u}) :
    y ∈ classSet d E x ↔ y ∈ d ∧ ZFSet.pair x y ∈ E := ZFSet.mem_sep

def classFormula (c x d E : ℕ) : Formula :=
  .conj (.subset c d) (.allMem d (.iff (.member 0 (c+1)) (.pairMem (x+1) 0 (E+1))))

@[simp] theorem eval_classFormula (c x d E : ℕ) (e : ℕ → ZFSet.{u}) :
    (classFormula c x d E).Eval e ↔ e c = classSet (e d) (e E) (e x) := by
  simp only [classFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext
    intro y
    rw [mem_classSet]
    exact ⟨fun hy => ⟨hsub hy,(h y (hsub hy)).mp hy⟩,
      fun hy => (h y hy.1).mpr hy.2⟩
  · intro h
    rw [h]
    exact ⟨fun _ hy => (mem_classSet _ _ _ _).mp hy |>.1,
      fun y hy => by simp [hy]⟩

end TuringRigidity.SetPresentationDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

def realSet (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ n, x = natSet n ∧ A n = true) ZFSet.omega

@[simp] theorem nat_mem_realSet (A : Oracle) (n : ℕ) :
    natSet.{u} n ∈ realSet A ↔ A n = true := by
  simp only [realSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,m,hm,hA⟩
    exact natSet_injective hm ▸ hA
  · intro hA
    exact ⟨(mem_omega _).mpr ⟨n,rfl⟩,⟨n,rfl,hA⟩⟩

def oracleOf (x : ZFSet.{u}) : Oracle := by
  classical
  exact fun n => decide (natSet n ∈ x)

@[simp] theorem oracleOf_realSet (A : Oracle) : oracleOf (realSet.{u} A) = A := by
  funext n
  simp only [oracleOf,nat_mem_realSet]
  cases A n <;> rfl

def reals (M : ZFSet.{u}) : Set Oracle := {A | realSet A ∈ M}

end
end TuringRigidity.SetModelReals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

def finiteGraph (n : ℕ) (f : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin n => ZFSet.pair (natSet i.val) (f i.val))

@[simp] theorem mem_finiteGraph (n : ℕ) (f : ℕ → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ finiteGraph n f ↔ ∃ i < n, z = ZFSet.pair (natSet i) (f i) := by
  rw [finiteGraph,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨i.val,i.isLt,hi.symm⟩,fun ⟨i,hi,h⟩ => ⟨⟨i,hi⟩,h.symm⟩⟩

@[simp] theorem pair_mem_finiteGraph (n : ℕ) (f : ℕ → ZFSet.{u}) (i : ℕ) (y : ZFSet.{u}) :
    ZFSet.pair (natSet i) y ∈ finiteGraph n f ↔ i < n ∧ y = f i := by
  rw [mem_finiteGraph]
  constructor
  · rintro ⟨j,hj,he⟩
    obtain ⟨hn,hy⟩ := ZFSet.pair_inj.mp he
    have hi := natSet_injective hn
    exact ⟨hi ▸ hj,hi ▸ hy⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl⟩

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplicationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

def numberPair (q : ℕ × ℕ) : ZFSet.{u} := ZFSet.pair (natSet q.1) (natSet q.2)

def pairNumbers := ZFSet.prod ZFSet.omega.{u} ZFSet.omega

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpIdealPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.JumpIdealPresentation
open Encodable EncodedForcing OracleJump ArithmeticHierarchy IndexMatrix TableIndices
open PersistentRestrictions UniformArithmetic
noncomputable section

def omegaJump (X : Oracle) : Oracle := fun v => iterate X (Nat.unpair v).1 (Nat.unpair v).2

@[simp] theorem omegaJump_column (X : Oracle) (n : ℕ) :
    columns (omegaJump X) n = iterate X n := by
  funext k
  simp [columns,omegaJump]

def presentation (X : Oracle) : Oracle := fun v =>
  tableOracle (iterate X (Nat.unpair (Nat.unpair v).1).1)
    (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2

@[simp] theorem presentation_column (X : Oracle) (n e : ℕ) :
    columns (presentation X) (Nat.pair n e) = tableOracle (iterate X n) e := by
  funext k
  simp [columns,presentation]

end
end TuringRigidity.JumpIdealPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSequences
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

def sequenceSet (F : ℕ → Oracle) : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (natSet n) (realSet (F n)))

@[simp] theorem mem_sequenceSet (F : ℕ → Oracle) (z : ZFSet.{u}) :
    z ∈ sequenceSet F ↔ ∃ n, z = ZFSet.pair (natSet n) (realSet (F n)) := by
  rw [sequenceSet,ZFSet.mem_range]
  exact exists_congr (fun n => eq_comm)

@[simp] theorem pair_mem_sequenceSet (F : ℕ → Oracle) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ sequenceSet F ↔ x = realSet (F n) := by
  rw [mem_sequenceSet]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    exact natSet_injective hn ▸ hx
  · intro h
    exact ⟨n,by rw [h]⟩

end
end TuringRigidity.SetModelSequences

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelSequences
universe u
noncomputable section

def tripleFormula (i j k r d : ℕ) : Formula := .existsMem d
  (.conj (.orderedPair 0 (i+1) (j+1)) (.pairMem 0 (k+1) (r+1)))

@[simp] theorem eval_tripleFormula (i j k r d : ℕ) (e : ℕ → ZFSet.{u}) :
    (tripleFormula i j k r d).Eval e ↔
    ZFSet.pair (e i) (e j) ∈ e d ∧ ZFSet.pair (ZFSet.pair (e i) (e j)) (e k) ∈ e r := by
  simp only [tripleFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  constructor
  · rintro ⟨t,ht,rfl,h⟩
    exact ⟨ht,h⟩
  · rintro ⟨ht,h⟩
    exact ⟨_,ht,rfl,h⟩

def pairingSet : ZFSet.{u} := ZFSet.sep
  (fun z => ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (Nat.pair n m)))
  (ZFSet.prod pairNumbers ZFSet.omega)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace Formula
theorem eval_rename (φ : Formula) (v : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (φ.rename v).Eval e ↔ φ.Eval (fun i => e (v i)) := by
  induction φ generalizing v e with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ v e) (ihψ v e)
  | neg φ ih => exact not_congr (ih v e)
  | existsMem i φ ih =>
    simp only [rename,Eval]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    have he : (fun i => cons x e (liftMap v i)) = cons x (fun i => e (v i)) := by
      funext i; cases i <;> rfl
    exact (ih (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)
end Formula

namespace FiniteTuple

def prepend (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u} :=
  xs.foldr cons e

@[simp] theorem prepend_nil (e : ℕ → ZFSet.{u}) : prepend [] e = e := rfl
@[simp] theorem prepend_cons (x : ZFSet.{u}) (xs : List ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    prepend (x :: xs) e = cons x (prepend xs e) := rfl

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedFormulaRename
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

@[simp] theorem Formula.eval_rename_comp (p : Formula) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (p.rename r).Eval e ↔ p.Eval (e ∘ r) := Formula.eval_rename p r e
end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}}

def natLift (f : ℕ → ℕ) (x : ZFSet.{u}) : ZFSet.{u} :=
  natSet (f (Function.invFun natSet x))

@[simp] theorem natLift_nat (f : ℕ → ℕ) (n : ℕ) :
    natLift f (natSet.{u} n) = natSet (f n) := by
  simp only [natLift,Function.leftInverse_invFun natSet_injective n]

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelTreeRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic BoundedSetTheory TransitiveNameModel SetModelReals
open SetModelArithmetic SetModelFunctions SetModelSequences Encodable
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def Test.canonicalNode (t : Test) (O : Oracles) (v n : ℕ) : Prop :=
  encode (decodeNode n) = n ∧ t.accepts O v (decodeNode n)

def Test.edgePredicate (t : Test) (O : Oracles) (v n m : ℕ) : Prop :=
  t.canonicalNode O v n ∧ t.canonicalNode O v m ∧ ∃ a, decodeNode n = decodeNode m ++ [a]

def relationSet (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ realSet A, ZFSet.pair z x ∈ pairingSet) pairNumbers

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTreeDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic SetModelReals SetModelFunctions
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def unionRead (c : ℕ → ℕ) (i : ℕ) : ℕ := (decodeNode (c (i+1)))[i]?.getD 0

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PairGenericSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PairGenericSelection
open FiniteShuffle ShuffleRequirements Set

def column (b : Bool) (G : Oracle) : Oracle :=
  fun n => if b then G (2*n+1) else G (2*n)

end TuringRigidity.PairGenericSelection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericTruth
open FiniteShuffle ShuffleRequirements Set Filter Encodable

def triple (G : Oracle) : Oracle × Oracle × Oracle :=
  (PairGenericSelection.column false G,
    PairGenericSelection.column false (PairGenericSelection.column true G),
    PairGenericSelection.column true (PairGenericSelection.column true G))

end TuringRigidity.GenericTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericSourceTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericSourceTransfer
open FiniteShuffle ShuffleRequirements PairGenericSelection Set

@[simp] theorem triple_join (Y Z : Oracle) :
    GenericTruth.triple (join Y Z) = (Y,column false Z,column true Z) := by
  have hl : column false (join Y Z) = Y := by funext n; simp [column]
  have hr : column true (join Y Z) = Z := by funext n; simp [column]
  simp [GenericTruth.triple,hl,hr]

end TuringRigidity.GenericSourceTransfer

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_UnionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open BoundedSetTheory
universe u

namespace IterationFormula
open Formula

def unionOf (b a : ℕ) : Formula := .conj
  (allMem b (.existsMem (a+1) (.member 1 0)))
  (allMem a (allMem 0 (.member 0 (b+2))))

@[simp] theorem eval_unionOf (b a : ℕ) (e : ℕ → ZFSet.{u}) :
    (unionOf b a).Eval e ↔ e b = ZFSet.sUnion (e a) := by
  simp only [unionOf,Formula.Eval,eval_allMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hf,hb⟩
    apply ZFSet.ext; intro z; rw [ZFSet.mem_sUnion]
    exact ⟨hf z,fun ⟨y,hy,hz⟩ => hb y hy z hz⟩
  · intro h; rw [h]
    exact ⟨fun z hz => ZFSet.mem_sUnion.mp hz,
      fun y hy z hz => ZFSet.mem_sUnion.mpr ⟨y,hy,hz⟩⟩

end IterationFormula

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory
universe u

def Triple (k f a b q : ZFSet.{u}) : Prop :=
  ∃ v ∈ k, v = ZFSet.pair a b ∧ ZFSet.pair v q ∈ f

def Match (flip : Bool) (d c k o f a y q : ZFSet.{u}) : Prop :=
  ∃ r ∈ c, ZFSet.pair r q ∈ o ∧ ∃ b ∈ d, ∃ t ∈ c,
    ZFSet.pair b t ∈ y ∧ ZFSet.pair r t ∈ o ∧
      Triple k f (if flip then b else a) (if flip then a else b) r

def Side (flip : Bool) (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∀ a ∈ d, ∀ s ∈ c, ZFSet.pair a s ∈ x →
    ∀ q ∈ c, ZFSet.pair q p ∈ o → ZFSet.pair q s ∈ o → Match flip d c k o f a y q

def Step (d c k o f x y p : ZFSet.{u}) : Prop :=
  Side false d c k o f x y p ∧ Side true d c k o f y x p

def Vertex (d c k o f z : ZFSet.{u}) : Prop :=
  ∃ x ∈ d, ∃ y ∈ d, ∃ q ∈ c, ∃ v ∈ k,
    v = ZFSet.pair x y ∧ z = ZFSet.pair v q ∧ Step d c k o f x y q

namespace AtomicFormula
open Formula

def triple (k f a b q : ℕ) : Formula :=
  .existsMem k (.conj (orderedPair 0 (a+1) (b+1)) (pairMem 0 (q+1) (f+1)))

theorem eval_triple (k f a b q : ℕ) (e : ℕ → ZFSet.{u}) :
    (triple k f a b q).Eval e ↔ Triple (e k) (e f) (e a) (e b) (e q) := by
  simp only [triple,Formula.Eval,eval_orderedPair,eval_pairMem,cons_zero,cons_succ,Triple]

def matchF (flip : Bool) (d c k o f a y q : ℕ) : Formula :=
  .existsMem c (.conj (pairMem 0 (q+1) (o+1))
    (.existsMem (d+1) (.existsMem (c+2)
      (.conj (pairMem 1 0 (y+3)) (.conj (pairMem 2 0 (o+3))
        (triple (k+3) (f+3) (if flip then 1 else a+3) (if flip then a+3 else 1) 2))))))

theorem eval_matchF (flip : Bool) (d c k o f a y q : ℕ) (e : ℕ → ZFSet.{u}) :
    (matchF flip d c k o f a y q).Eval e ↔
      Match flip (e d) (e c) (e k) (e o) (e f) (e a) (e y) (e q) := by
  cases flip <;> simp only [matchF,Formula.Eval,eval_pairMem,eval_triple,
    cons_zero,cons_succ,Match,Bool.false_eq_true,ite_false,ite_true]

def side (flip : Bool) (d c k o f x y p : ℕ) : Formula :=
  allMem d (allMem (c+1) (imp (pairMem 1 0 (x+2))
    (allMem (c+2) (imp (.conj (pairMem 0 (p+3) (o+3)) (pairMem 0 1 (o+3)))
      (matchF flip (d+3) (c+3) (k+3) (o+3) (f+3) 2 (y+3) 0)))))

theorem eval_side (flip : Bool) (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (side flip d c k o f x y p).Eval e ↔
      Side flip (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [side,eval_allMem,eval_imp,Formula.Eval,eval_pairMem,eval_matchF,
    cons_zero,cons_succ,Side,and_imp]

def step (d c k o f x y p : ℕ) : Formula :=
  .conj (side false d c k o f x y p) (side true d c k o f y x p)

theorem eval_step (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (step d c k o f x y p).Eval e ↔
      Step (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [step,Formula.Eval,eval_side,Step]

def vertex (d c k o f z : ℕ) : Formula :=
  .existsMem d (.existsMem (d+1) (.existsMem (c+2) (.existsMem (k+3)
    (.conj (orderedPair 0 3 2) (.conj (orderedPair (z+4) 0 1)
      (step (d+4) (c+4) (k+4) (o+4) (f+4) 3 2 1))))))

theorem eval_vertex (d c k o f z : ℕ) (e : ℕ → ZFSet.{u}) :
    (vertex d c k o f z).Eval e ↔ Vertex (e d) (e c) (e k) (e o) (e f) (e z) := by
  simp only [vertex,Formula.Eval,eval_orderedPair,eval_step,cons_zero,cons_succ,Vertex]
end AtomicFormula

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory
universe u

def Graph (d c o f : ZFSet.{u}) : Prop :=
  f ⊆ ZFSet.prod (ZFSet.prod d d) c ∧
    ∀ x ∈ d, ∀ y ∈ d, ∀ q ∈ c,
      ZFSet.pair (ZFSet.pair x y) q ∈ f ↔ Step d c (ZFSet.prod d d) o f x y q

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicGraphCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem triple_pair {d f x y q : ZFSet.{u}} (hx : x ∈ d) (hy : y ∈ d) :
    Triple (ZFSet.prod d d) f x y q ↔ ZFSet.pair (ZFSet.pair x y) q ∈ f := by
  constructor
  · rintro ⟨v,_,rfl,h⟩; exact h
  · intro h
    exact ⟨_,ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,rfl,h⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicRequirements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames CountableForcing
universe u
variable {P : Type u} [Preorder P]

def Witness (a : Name P) : Name P → P → Prop
  | .mk _ b t, p => ∃ j, p ≤ t j ∧ EqForces a (b j) p

def NegMem (a b : Name P) (p : P) : Prop := ∀ q, q ≤ p → ¬ MemForces a b q

def MemTest (a b : Name P) : Set P := {p | Witness a b p ∨ NegMem a b p}

def Refute : Name P → Name P → P → Prop
  | .mk _ a s, .mk _ b t, p =>
    (∃ i, p ≤ s i ∧ NegMem (a i) (.mk _ b t) p) ∨
    (∃ j, p ≤ t j ∧ NegMem (b j) (.mk _ a s) p)

def EqTest (a b : Name P) : Set P := {p | EqForces a b p ∨ Refute a b p}

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicDecisionFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

def CodeWitness (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∃ b ∈ d, ∃ t ∈ c, ZFSet.pair b t ∈ y ∧ ZFSet.pair p t ∈ o ∧ Triple k f x b p

def CodeNeg (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∀ q ∈ c, ZFSet.pair q p ∈ o → ¬ CodeWitness d c k o f x y q

def CodeRefute (d c k o f x y p : ZFSet.{u}) : Prop :=
  ∃ a ∈ d, ∃ s ∈ c, ZFSet.pair a s ∈ x ∧ ZFSet.pair p s ∈ o ∧ CodeNeg d c k o f a y p

namespace AtomicFormula
open _root_.OAI.TuringRigidity.BoundedSetTheory.Formula

def witness (d c k o f x y p : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1)
    (.conj (pairMem 1 0 (y+2)) (.conj (pairMem (p+2) 0 (o+2))
      (triple (k+2) (f+2) (x+2) 1 (p+2)))))

theorem eval_witness (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (witness d c k o f x y p).Eval e ↔
      CodeWitness (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [witness,Formula.Eval,eval_pairMem,eval_triple,cons_zero,cons_succ,CodeWitness]

def negMem (d c k o f x y p : ℕ) : Formula :=
  allMem c (imp (pairMem 0 (p+1) (o+1))
    (.neg (witness (d+1) (c+1) (k+1) (o+1) (f+1) (x+1) (y+1) 0)))

theorem eval_negMem (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (negMem d c k o f x y p).Eval e ↔
      CodeNeg (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [negMem,eval_allMem,eval_imp,Formula.Eval,eval_pairMem,eval_witness,
    cons_zero,cons_succ,CodeNeg]

def refute (d c k o f x y p : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1)
    (.conj (pairMem 1 0 (x+2)) (.conj (pairMem (p+2) 0 (o+2))
      (negMem (d+2) (c+2) (k+2) (o+2) (f+2) 1 (y+2) (p+2)))))

theorem eval_refute (d c k o f x y p : ℕ) (e : ℕ → ZFSet.{u}) :
    (refute d c k o f x y p).Eval e ↔
      CodeRefute (e d) (e c) (e k) (e o) (e f) (e x) (e y) (e p) := by
  simp only [refute,Formula.Eval,eval_pairMem,eval_negMem,cons_zero,cons_succ,CodeRefute]

def memTest (d c k o f x y p : ℕ) : Formula :=
  disj (witness d c k o f x y p) (negMem d c k o f x y p)

def eqTest (d c k o f x y p : ℕ) : Formula :=
  disj (triple k f x y p) (disj (refute d c k o f x y p) (refute d c k o f y x p))
end AtomicFormula

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalAtomicTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

def GroundGeneric (M : ZFSet.{u}) (G : GenericFilter (Conditions c)) : Prop :=
  ∀ D ∈ M, Dense {q | label c q ∈ D} → ∃ q ∈ G.carrier, label c q ∈ D

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_AtomicCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

namespace AtomicFormula
open _root_.OAI.TuringRigidity.BoundedSetTheory.Formula

def product (d k : ℕ) : Formula :=
  .conj (allMem k (.existsMem (d+1) (.existsMem (d+2) (orderedPair 2 1 0))))
    (allMem d (allMem (d+1) (.existsMem (k+2) (orderedPair 0 2 1))))

theorem eval_product (d k : ℕ) (e : ℕ → ZFSet.{u}) :
    (product d k).Eval e ↔ e k = ZFSet.prod (e d) (e d) := by
  simp only [product,Formula.Eval,eval_allMem,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨h₁,h₂⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x,hx,y,hy,hz⟩ := h₁ z hz
      exact ZFSet.mem_prod.mpr ⟨x,hx,y,hy,hz⟩
    · intro hz
      obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
      obtain ⟨v,hv,rfl⟩ := h₂ x hx y hy
      exact hv
  · intro hk
    constructor
    · intro z hz
      rw [hk] at hz
      exact ZFSet.mem_prod.mp hz
    · intro x hx y hy
      exact ⟨_,hk ▸ ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,rfl⟩

def graph (d c k o f : ℕ) : Formula :=
  .conj (allMem f (.existsMem (k+1) (.existsMem (c+2) (orderedPair 2 1 0))))
    (allMem d (allMem (d+1) (allMem (c+2)
      (iff (triple (k+3) (f+3) 2 1 0) (step (d+3) (c+3) (k+3) (o+3) (f+3) 2 1 0)))))

theorem eval_graph (d c k o f : ℕ) (e : ℕ → ZFSet.{u})
    (hk : e k = ZFSet.prod (e d) (e d)) :
    (graph d c k o f).Eval e ↔ Graph (e d) (e c) (e o) (e f) := by
  simp only [graph,Formula.Eval,eval_allMem,eval_orderedPair,eval_iff,eval_triple,eval_step,
    cons_zero,cons_succ,hk,Graph]
  constructor
  · rintro ⟨h₁,h₂⟩
    refine ⟨fun z hz => ZFSet.mem_prod.mpr (h₁ z hz),?_⟩
    intro x hx y hy q hq
    exact (triple_pair hx hy).symm.trans (h₂ x hx y hy q hq)
  · rintro ⟨h₁,h₂⟩
    refine ⟨fun z hz => ZFSet.mem_prod.mp (h₁ hz),?_⟩
    intro x hx y hy q hq
    exact (triple_pair hx hy).trans (h₂ x hx y hy q hq)

def membership (d c k o f x y p : ℕ) : Formula :=
  allMem c (imp (pairMem 0 (p+1) (o+1))
    (matchF false (d+1) (c+1) (k+1) (o+1) (f+1) (x+1) (y+1) 0))

end AtomicFormula

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_NameSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

def SupportPredicate (d c o x z : ZFSet.{u}) : Prop :=
  ∃ a ∈ d, ∃ q ∈ c, z = ZFSet.pair a q ∧ ∃ s ∈ c,
    ZFSet.pair a s ∈ x ∧ ZFSet.pair q s ∈ o

namespace AtomicFormula
open _root_.OAI.TuringRigidity.BoundedSetTheory.Formula

def support (d c o x z : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1) (.conj (orderedPair (z+2) 1 0)
    (.existsMem (c+2) (.conj (pairMem 2 0 (x+3)) (pairMem 1 0 (o+3))))))

theorem eval_support (d c o x z : ℕ) (e : ℕ → ZFSet.{u}) :
    (support d c o x z).Eval e ↔ SupportPredicate (e d) (e c) (e o) (e x) (e z) := by
  simp only [support,Formula.Eval,eval_orderedPair,eval_pairMem,cons_zero,cons_succ,SupportPredicate]
end AtomicFormula

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IntersectionName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u

namespace AtomicFormula
open _root_.OAI.TuringRigidity.BoundedSetTheory.Formula

def select (d c k o f y z : ℕ) : Formula :=
  .existsMem d (.existsMem (c+1) (.conj (orderedPair (z+2) 1 0)
    (witness (d+2) (c+2) (k+2) (o+2) (f+2) 1 (y+2) 0)))

theorem eval_select (d c k o f y z : ℕ) (e : ℕ → ZFSet.{u}) :
    (select d c k o f y z).Eval e ↔
      ∃ x ∈ e d, ∃ q ∈ e c, e z = ZFSet.pair x q ∧
        CodeWitness (e d) (e c) (e k) (e o) (e f) x (e y) q := by
  simp only [select,Formula.Eval,eval_orderedPair,eval_witness,cons_zero,cons_succ]
end AtomicFormula

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel
universe u

@[instance_reducible] noncomputable def order (c : ZFSet.{u}) : PartialOrder (Conditions c) where
  le p q := label c q ⊆ label c p
  lt left right := label c right ⊆ label c left ∧ ¬ label c left ⊆ label c right
  le_refl _ := fun _ h => h
  le_trans _ _ _ hpq hqr := fun _ h => hpq (hqr h)
  le_antisymm p q hpq hqp := label_injective c (ZFSet.ext (fun z => ⟨fun h => hqp h,fun h => hpq h⟩))

attribute [local instance] order

@[instance_reducible] noncomputable def collapsePreorder
    (conditionSet : ZFSet.{u}) : Preorder (Conditions conditionSet) :=
  (order conditionSet).toPreorder

attribute [local instance] collapsePreorder

@[instance_reducible] noncomputable def top (c : ZFSet.{u}) (h0 : (∅ : ZFSet.{u}) ∈ c) : OrderTop (Conditions c) where
  top := equivShrink c ⟨∅,h0⟩
  le_top p := by
    have he : label c (equivShrink c ⟨∅,h0⟩) = ∅ := by simp [label]
    change label c (equivShrink c ⟨∅,h0⟩) ⊆ label c p
    rw [he]
    exact fun z hz => False.elim (ZFSet.notMem_empty z hz)

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetDegreeDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetDegreeDecoding
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals
open PersistentRestrictions
universe u
noncomputable section

def degreeSet (a : Degree) : ZFSet.{u} :=
  ZFSet.sep (fun x => degree (oracleOf x) = a) (ZFSet.powerset ZFSet.omega)

def idealSet (I : CountableIdeal) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ a ∈ I.carrier, x = degreeSet a)
    (ZFSet.powerset (ZFSet.powerset ZFSet.omega))

@[simp] theorem mem_idealSet (I : CountableIdeal) (x : ZFSet.{u}) :
    x ∈ idealSet I ↔ ∃ a ∈ I.carrier, x = degreeSet a := by
  rw [idealSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨a,ha,rfl⟩
    refine ⟨ZFSet.mem_powerset.mpr ?_,⟨a,ha,rfl⟩⟩
    intro y hy
    exact (ZFSet.mem_sep.mp hy).1

def automorphismSet {I : CountableIdeal} (ρ : I ≃o I) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ b : I, z = ZFSet.pair (degreeSet b.val) (degreeSet (ρ b).val))
    (ZFSet.prod (idealSet I) (idealSet I))

@[simp] theorem mem_automorphismSet {I : CountableIdeal} (ρ : I ≃o I) (z : ZFSet.{u}) :
    z ∈ automorphismSet ρ ↔ ∃ b : I, z = ZFSet.pair (degreeSet b.val) (degreeSet (ρ b).val) := by
  rw [automorphismSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨b,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨(mem_idealSet _ _).mpr ⟨b.val,b.property,rfl⟩,
      (mem_idealSet _ _).mpr ⟨(ρ b).val,(ρ b).property,rfl⟩⟩,⟨b,rfl⟩⟩

end
end TuringRigidity.SetDegreeDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelColumns
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelSequences
open EncodedForcing
universe u
noncomputable section

def columnRange (A : Oracle) : ZFSet.{u} := ZFSet.range (fun n : ℕ => realSet (columns A n))

@[simp] theorem mem_columnRange (A : Oracle) (x : ZFSet.{u}) :
    x ∈ columnRange A ↔ ∃ n, x = realSet (columns A n) := by
  rw [columnRange,ZFSet.mem_range]
  exact exists_congr (fun _ => eq_comm)

end
end TuringRigidity.SetModelColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelGraphImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelColumns
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelSequences
open EncodedForcing
universe u
noncomputable section

def graphImage (A G : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n m, G (Nat.pair n m) = true ∧
    z = ZFSet.pair (realSet (columns A n)) (realSet (columns A m)))
    (ZFSet.prod (columnRange A) (columnRange A))

@[simp] theorem mem_graphImage (A G : Oracle) (z : ZFSet.{u}) :
    z ∈ graphImage A G ↔ ∃ n m, G (Nat.pair n m) = true ∧
      z = ZFSet.pair (realSet (columns A n)) (realSet (columns A m)) := by
  rw [graphImage,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨n,m,hG,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨(mem_columnRange _ _).mpr ⟨n,rfl⟩,
      (mem_columnRange _ _).mpr ⟨m,rfl⟩⟩,⟨n,m,hG,rfl⟩⟩

end
end TuringRigidity.SetModelColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open SetDegreeDecoding SetModelSequences
open PersistentRestrictions EncodedForcing
universe u
noncomputable section

def FunctionGraph (f a b : ZFSet.{u}) : Prop :=
  (∀ z ∈ f, ∃ x ∈ a, ∃ y ∈ b, z = ZFSet.pair x y) ∧
  (∀ x ∈ a, ∃ y ∈ b, ZFSet.pair x y ∈ f ∧
    ∀ z ∈ b, ZFSet.pair x z ∈ f → z = y)

def ontoFormula (f a b : ℕ) : Formula :=
  .conj (.functionGraph f a b) (.allMem b (.existsMem (a+1) (.pairMem 0 1 (f+2))))

@[simp] theorem eval_ontoFormula (f a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (ontoFormula f a b).Eval e ↔ FunctionGraph (e f) (e a) (e b) ∧
      ∀ y ∈ e b, ∃ x ∈ e a, ZFSet.pair x y ∈ e f := by
  simp only [ontoFormula,Formula.Eval,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,cons_zero,cons_succ,FunctionGraph]

def InternallyCountable (M a : ZFSet.{u}) : Prop :=
  ∃ f ∈ M, (ontoFormula 0 1 2).Realize M (cons f (cons ZFSet.omega (fun _ => a)))

def choiceFormula (f a b : ℕ) : Formula :=
  .conj (.functionGraph f a b) (.allMem a (.existsMem 0 (.pairMem 1 0 (f+2))))

@[simp] theorem eval_choiceFormula (f a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (choiceFormula f a b).Eval e ↔ FunctionGraph (e f) (e a) (e b) ∧
      ∀ x ∈ e a, ∃ y ∈ x, ZFSet.pair x y ∈ e f := by
  simp only [choiceFormula,Formula.Eval,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,cons_zero,cons_succ,FunctionGraph]

end
end TuringRigidity.SetModelCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPresentedCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelArithmetic
open SetPresentationDecoding SetDegreeDecoding SetModelSequences SetModelColumns
open PersistentRestrictions EncodedForcing
universe u
noncomputable section
variable {M : ZFSet.{u}}

def degreeSequence (A : Oracle) : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (natSet n) (degreeSet (degree (columns A n))))

@[simp] theorem mem_degreeSequence (A : Oracle) (z : ZFSet.{u}) :
    z ∈ degreeSequence A ↔ ∃ n, z = ZFSet.pair (natSet n) (degreeSet (degree (columns A n))) := by
  rw [degreeSequence,ZFSet.mem_range]
  exact exists_congr (fun n => eq_comm)

@[simp] theorem pair_mem_degreeSequence (A : Oracle) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ degreeSequence A ↔ x = degreeSet (degree (columns A n)) := by
  rw [mem_degreeSequence]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    exact natSet_injective hn ▸ hx
  · intro h
    exact ⟨n,by rw [h]⟩

end
end TuringRigidity.SetModelCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIdealSatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

def idealFormula (i d l : ℕ) : Formula :=
  .conj (.subset i d) (.conj (.existsMem i (.equal 0 0))
    (.conj (.allMem i (.allMem (d+1) (.imp (.pairMem 0 1 (l+2)) (.member 0 (i+2)))))
      (.allMem i (.allMem (i+1) (.existsMem (i+2)
        (.conj (.pairMem 2 0 (l+3)) (.pairMem 1 0 (l+3))))))))

def IsIdeal (a d l : ZFSet.{u}) : Prop :=
  a ⊆ d ∧ (∃ x, x ∈ a) ∧
    (∀ x ∈ a, ∀ y ∈ d, ZFSet.pair y x ∈ l → y ∈ a) ∧
    (∀ x ∈ a, ∀ y ∈ a, ∃ z ∈ a, ZFSet.pair x z ∈ l ∧ ZFSet.pair y z ∈ l)

@[simp] theorem eval_idealFormula (i d l : ℕ) (e : ℕ → ZFSet.{u}) :
    (idealFormula i d l).Eval e ↔ IsIdeal (e i) (e d) (e l) := by
  simp only [idealFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ,IsIdeal,and_true]

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelActionSatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

def actionFormula (f i l : ℕ) : Formula :=
  .conj (ontoFormula f i i)
    (.allMem i (.allMem (i+1) (.allMem (i+2) (.allMem (i+3)
      (.imp (.conj (.pairMem 3 1 (f+4)) (.pairMem 2 0 (f+4)))
        (.iff (.pairMem 3 2 (l+4)) (.pairMem 1 0 (l+4))))))))

def IsAction (f i l : ZFSet.{u}) : Prop :=
  (FunctionGraph f i i ∧ ∀ y ∈ i, ∃ x ∈ i, ZFSet.pair x y ∈ f) ∧
    ∀ x ∈ i, ∀ y ∈ i, ∀ a ∈ i, ∀ b ∈ i,
      ZFSet.pair x a ∈ f ∧ ZFSet.pair y b ∈ f →
        (ZFSet.pair x y ∈ l ↔ ZFSet.pair a b ∈ l)

@[simp] theorem eval_actionFormula (f i l : ℕ) (e : ℕ → ZFSet.{u}) :
    (actionFormula f i l).Eval e ↔ IsAction (e f) (e i) (e l) := by
  simp only [actionFormula,Formula.Eval,eval_ontoFormula,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ,IsAction]

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPersistentSatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section

inductive InternalFormula where
  | bounded (p : Formula)
  | conj (p q : InternalFormula)
  | neg (p : InternalFormula)
  | existsSet (p : InternalFormula)

def InternalFormula.Realize (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) : InternalFormula → Prop
  | .bounded p => p.Realize M e
  | .conj p q => p.Realize M e ∧ q.Realize M e
  | .neg p => ¬ p.Realize M e
  | .existsSet p => ∃ x ∈ M, p.Realize M (cons x e)

def InternalFormula.allMem (i : ℕ) (p : InternalFormula) : InternalFormula :=
  .neg (.existsSet (.conj (.bounded (.member 0 (i+1))) (.neg p)))

@[simp] theorem InternalFormula.realize_allMem (i : ℕ) (p : InternalFormula)
    (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (InternalFormula.allMem i p).Realize M e ↔
      ∀ x ∈ M, x ∈ e i → p.Realize M (cons x e) := by
  classical
  simp [InternalFormula.allMem,InternalFormula.Realize,Formula.Realize]

def persistenceMatrix : Formula :=
  .conj (idealFormula 2 4 5) (.conj (ontoFormula 0 8 2)
    (.conj (actionFormula 1 2 5) (.conj (.subset 6 2)
      (.conj (.subset 7 1) (.member 3 2)))))

def persistenceFormula : InternalFormula :=
  .allMem 0 (.existsSet (.existsSet (.existsSet (.bounded persistenceMatrix))))

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTNativeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions
universe u
noncomputable section

def SetMoved (f i : ZFSet.{u}) : Prop := ∃ x ∈ i, ∃ y ∈ i, ZFSet.pair x y ∈ f ∧ x ≠ y

def NativeNonidentity (M D L i : ZFSet.{u}) : Prop :=
  ∃ f ∈ M, IsAction f i L ∧ SetMoved f i ∧
    persistenceFormula.Realize M (cons D (cons L (cons i (cons f (fun _ => ZFSet.omega)))))

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTGenericPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions CountableForcing
universe u
noncomputable section

def NativePersistent (M : ZFSet.{u}) (I : CountableIdeal) (ρ : I ≃o I) : Prop :=
  ∃ D ∈ M, ∃ L ∈ M,
    (∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A)) ∧
    (∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B) ∧
    persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega)))))

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_NativeGenericWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open BoundedSetTheory TransitiveNameModel SetDegreeDecoding PersistentRestrictions
open CountableForcing AtomicForcing
universe u

def SetGenericallyPersistent (M : ZFSet.{u}) (I : CountableIdeal) (ρ : I ≃o I) : Prop :=
  ∃ c o : ZFSet.{u}, ∃ ord : Preorder (Conditions c),
    letI := ord
    ∃ ot : OrderTop (Conditions c),
      letI := ot
      c ∈ M ∧ o ∈ M ∧
      (∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) ∧
      ∃ G : GenericFilter (Conditions c), GroundGeneric M G ∧
        SetModelCountability.InternallyCountable (genericExtensionSet M c G.carrier) (idealSet I) ∧
        NativePersistent (genericExtensionSet M c G.carrier) I ρ

end TuringRigidity.ArithmeticTree

end OAI
end


