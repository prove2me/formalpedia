-- Prove2me | Definitions.Def_OAIQ069A000
-- name    : OAIQ069A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:43:48.091306+00:00
-- url     : https://prove2.me/theorems/3539fb48-9694-4f16-aeb9-58a0595a0a22
-- title:
--   Definitions bundle OAIQ069A000 of the split of OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LargeIndependentSets.mainTheoremReal`, carved from OpenAI's openai/math development (OpenAI, *Hardness of finding large independent sets in three-colorable graphs (result family 106)*, OpenAI Math Release, September 24, 2026, result family 106, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 956 declarations of OpenAI's Lean: 469 definitions, 28 inductive types or structures, 14 instances and 445 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.IndependentSetsCut.CounterMachine.Command`, `OAI.IndependentSetsCut.CounterMachine.Command.Bounded`, `OAI.IndependentSetsCut.CounterMachine.Command.Evaluates`, `OAI.IndependentSetsCut.CounterMachine.Command.FinalLabel`, `OAI.IndependentSetsCut.CounterMachine.Command.Label`, `OAI.IndependentSetsCut.CounterMachine.Command.Within`, `OAI.IndependentSetsCut.CounterMachine.Command.backData`, `OAI.IndependentSetsCut.CounterMachine.Command.clear`, `OAI.IndependentSetsCut.CounterMachine.Command.code`, `OAI.IndependentSetsCut.CounterMachine.Command.copy`, `OAI.IndependentSetsCut.CounterMachine.Command.decData`, `OAI.IndependentSetsCut.CounterMachine.Command.discardData`, `OAI.IndependentSetsCut.CounterMachine.Command.entry`, `OAI.IndependentSetsCut.CounterMachine.Command.finalCode`, `OAI.IndependentSetsCut.CounterMachine.Command.finite`, `OAI.IndependentSetsCut.CounterMachine.Command.finiteMachine`, `OAI.IndependentSetsCut.CounterMachine.Command.incData`, `OAI.IndependentSetsCut.CounterMachine.Command.initial`, `OAI.IndependentSetsCut.CounterMachine.Command.inputBit`, `OAI.IndependentSetsCut.CounterMachine.Command.inputLength`, `OAI.IndependentSetsCut.CounterMachine.Command.lengthLoop`, `OAI.IndependentSetsCut.CounterMachine.Command.machine_run`, `OAI.IndependentSetsCut.CounterMachine.Command.move`, `OAI.IndependentSetsCut.CounterMachine.Command.mulAdd`, `OAI.IndependentSetsCut.CounterMachine.Command.put`, `OAI.IndependentSetsCut.CounterMachine.Command.readData`, `OAI.IndependentSetsCut.CounterMachine.Command.regCount`, `OAI.IndependentSetsCut.CounterMachine.Command.restrict`, `OAI.IndependentSetsCut.CounterMachine.Command.skipInput`, `OAI.IndependentSetsCut.CounterMachine.Command.subFrom`, `OAI.IndependentSetsCut.CounterMachine.Command.writeData`, `OAI.IndependentSetsCut.CounterMachine.Configuration`, `OAI.IndependentSetsCut.CounterMachine.Data`, `OAI.IndependentSetsCut.CounterMachine.Data.Clean`, `OAI.IndependentSetsCut.CounterMachine.Data.restrict`, `OAI.IndependentSetsCut.CounterMachine.Data.set`, `OAI.IndependentSetsCut.CounterMachine.Expr` and 457 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `IndependentSets_Encoding_BinaryCoordinates`, `IndependentSets_Encoding_GameEncoding`, `IndependentSets_Encoding_Target`, `IndependentSets_Expansion_Capped`, `IndependentSets_Expansion_CayleySpectral`, `IndependentSets_Expansion_DegreeReplacement`, `IndependentSets_Expansion_ExpanderFamily`, `IndependentSets_Expansion_ExpanderTables`, `IndependentSets_Expansion_Expanders`, `IndependentSets_Expansion_Finite`, `IndependentSets_Expansion_Finite2`, `IndependentSets_Expansion_PortTables`, `IndependentSets_Expansion_PoweringWalks`, `IndependentSets_Expansion_PreprocessingRegularTables`, `IndependentSets_Fourier_Contexts`, `IndependentSets_Fourier_Game`, `IndependentSets_Fourier_Walsh`, `IndependentSets_Machines_AmbientRelation`, `IndependentSets_Machines_BitValue`, `IndependentSets_Machines_Command`, `IndependentSets_Machines_Copy`, `IndependentSets_Machines_Correct`, `IndependentSets_Machines_ExprDrop`, `IndependentSets_Machines_ExprTables`, `IndependentSets_Machines_FinalCNFHeader`, `IndependentSets_Machines_FinalCNFMachine`, `IndependentSets_Machines_FinalCNFRow`, `IndependentSets_Machines_FinalCNFRowTrace`, `IndependentSets_Machines_FinalLabel`, `IndependentSets_Machines_FramedLen`, `IndependentSets_Machines_LengthLoop`, `IndependentSets_Machines_Machine`, `IndependentSets_Machines_MachineDrainMany`, `IndependentSets_Machines_MachineFixedBlockMap`, `IndependentSets_Machines_MachineLookupCore`, `IndependentSets_Machines_MachineLookupSpec`, `IndependentSets_Machines_MachineUnaryCounter`, `IndependentSets_Machines_PoweringMachineInitialize`, `IndependentSets_Machines_PoweringMachineLoop`, `IndependentSets_Machines_PoweringMachineTapes`, `IndependentSets_Machines_PoweringMachineWord`, `IndependentSets_Machines_Printer`, `IndependentSets_Machines_Represented`, `IndependentSets_Machines_Restrict`, `IndependentSets_Machines_TableIterationFiniteAlphabet`, `IndependentSets_Machines_ValuePolynomial`, `IndependentSets_PCP_AlphabetGraph`, `IndependentSets_PCP_AlphabetReduction`, `IndependentSets_PCP_AlphabetRetraction`, `IndependentSets_PCP_Ambient`, `IndependentSets_PCP_AssignmentTester`, `IndependentSets_PCP_ClauseVerifier`, `IndependentSets_PCP_CodeComposition`, `IndependentSets_PCP_ConstraintGraph`, `IndependentSets_PCP_Emitter`, `IndependentSets_PCP_Enumeration`, `IndependentSets_PCP_FinalBooleanVerifier`, `IndependentSets_PCP_FinalCNFPattern`, `IndependentSets_PCP_FinalCNFTableAdapter`, `IndependentSets_PCP_GenericGraphTables`, `IndependentSets_PCP_GraphTables`, `IndependentSets_PCP_InitialGraph`, `IndependentSets_PCP_LCTable`, `IndependentSets_PCP_Lookup`, `IndependentSets_PCP_Minimum`, `IndependentSets_PCP_Queries`, `IndependentSets_PCP_QueryIncidence`, `IndependentSets_PCP_RawInitialTables`, `IndependentSets_PCP_ReadRelation`, `IndependentSets_PCP_Semantics`, `IndependentSets_PCP_Semantics2`, `IndependentSets_PCP_VerifierCNF`, `IndependentSets_Reduction_StoredFloyd`, `IndependentSets_Repetition_Basic`, `IndependentSets_Repetition_Sampling`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ069A003`, `OAIQ069A004` and `OAIQ069A005`; the proof of `OAI.LargeIndependentSets.actual_aligned_fiber`.
-- source:
--   OpenAI, Hardness of finding large independent sets in three-colorable graphs (result family 106), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 106; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ069_INDEP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_BinaryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

end IndependentSetsGames.Integration.BinaryCoordinates

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

end IndependentSetsGames.Foundations.Target

namespace IndependentSetsGames.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

def decodeWordsAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append, List.append_assoc,
        decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length = n + 1 := by
  simp [encodeWord]

@[simp] theorem encodeWords_append (xs ys : List Nat) :
    encodeWords (xs ++ ys) = encodeWords xs ++ encodeWords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih, List.append_assoc]

@[simp] theorem encodeWords_length (ns : List Nat) :
    (encodeWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, ih]; omega

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

@[simp] theorem literalWords_length {n : Nat} (literal : Literal n) :
    (literalWords literal).length = 2 := by simp [literalWords]

@[simp] theorem clauseWords_length {n : Nat} (clause : Clause n) :
    (clauseWords clause).length = 6 := by simp [clauseWords]

end IndependentSetsGames.Foundations.Complexity

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Encoding_GameEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity

open Target

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

end IndependentSetsGames.Foundations.Complexity

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PoweringWalks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

end IndependentSetsGames.Foundations.PCP.PoweringWalks

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ConstraintGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

end ConstraintGraph

end IndependentSetsGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_DegreeReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace IndependentSetsGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

end IndependentSetsGames.Foundations.PCP.DegreeReplacement

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Walsh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Hastad

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

end IndependentSetsGames.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_CayleySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open IndependentSetsGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

end IndependentSetsGames.Foundations.PCP.CayleySpectral
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AssignmentTester
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AssignmentTester

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
@[simp] theorem cubeXor_right_twice (f g : Cube A) :
    cubeXor (cubeXor f g) g = f := by
  funext a
  change ((f a ^^ g a) ^^ g a) = f a
  cases f a <;> cases g a <;> rfl

def flipAt (i : A) (f : Cube A) : Cube A :=
  fun j => if j = i then !(f j) else f j

omit [Fintype A] in
@[simp] theorem flipAt_twice (i : A) (f : Cube A) : flipAt i (flipAt i f) = f := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

def cubeAnd (f g : Cube A) : Cube A := fun a => f a && g a

variable {K : Type*} [Fintype K] [Nonempty K]

def eventQueries (label : A → K → Bool) (kind : Fin 4) (k : K)
    (f g r₀ r₁ r₂ : Cube A) (slot : Fin 6) : K ⊕ Cube A :=
  if kind = 0 then
    if slot = 0 then .inr f else if slot = 1 then .inr g else .inr (cubeXor f g)
  else if kind = 1 then
    if slot = 0 then .inr r₀ else
    if slot = 1 then .inr (cubeXor r₀ (cubeAnd f g)) else
    if slot = 2 then .inr r₁ else
    if slot = 3 then .inr (cubeXor r₁ f) else
    if slot = 4 then .inr r₂ else .inr (cubeXor r₂ g)
  else if kind = 2 then
    if slot = 0 then .inr r₀ else .inr (cubeXor r₀ (fun _ => true))
  else
    if slot = 0 then .inl k else
    if slot = 1 then .inr r₀ else .inr (cubeXor r₀ (fun a => label a k))

def eventAccepts (kind : Fin 4) (b : Fin 6 → Bool) : Bool :=
  if kind = 0 then decide ((b 0 ^^ b 1) = b 2)
  else if kind = 1 then decide ((b 0 ^^ b 1) = ((b 2 ^^ b 3) && (b 4 ^^ b 5)))
  else if kind = 2 then (b 0 ^^ b 1)
  else decide (b 0 = (b 1 ^^ b 2))

end IndependentSetsGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Expanders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTransport

open PoweringWalks

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

end IndependentSetsGames.Foundations.PCP.GraphTransport

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

end IndependentSetsGames.Foundations.PCP.ZigzagGraphs

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ClauseVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP

open Target

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.«variables» := formula.clauses[index.val]

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot

end IndependentSetsGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GraphTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GraphTables

open IndependentSetsGames.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

def relationIndex : Label × Label ≃ Fin 4096 := finProdFinEquiv

def relationAt (table : RelationTable) (a b : Label) : Bool :=
  table[relationIndex (a, b)]

def relationOf (predicate : Label → Label → Bool) : RelationTable :=
  Vector.ofFn (fun i => predicate (relationIndex.symm i).1 (relationIndex.symm i).2)

@[simp] theorem relationAt_relationOf (predicate : Label → Label → Bool) (a b : Label) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance instDecidableValid {n m : Nat} (rows : Rows n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table where
  vertices : Nat
  darts : Nat
  rows : Rows vertices darts
  valid : Valid rows

def rowList (table : Table) : List (DartRow table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : Table) : (rowList table).length = table.darts := by
  simp [rowList]

def semantics (table : Table) : ConstraintGraph (Fin table.vertices) (Fin table.darts) Label where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : Table) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : Table) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : Table) (e : Fin table.darts) (a b : Label) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Rows n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Table :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) :
    ConstraintGraph (Fin n) (Fin m) Label where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem parseBit_bitWord (b : Bool) : parseBit (bitWord b) = some b := by
  cases b <;> rfl

@[simp] theorem parseBits_bitWords (bits : List Bool) :
    (bits.map bitWord).mapM parseBit = some bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

def relationWords (relation : RelationTable) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : RelationTable) :
    (relationWords relation).length = 4096 := by simp [relationWords]

def parseRelation (words : List Nat) : Option RelationTable := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = 4096 then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : RelationTable) :
    parseRelation (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

def parseRow (vertices darts : Nat) : List Nat → Option (DartRow vertices darts × List Nat)
  | tail :: reverseIndex :: words => do
      let tail ← parseLabel vertices tail
      let reverseIndex ← parseLabel darts reverseIndex
      let relation ← parseRelation (words.take 4096)
      return (⟨tail, reverseIndex, relation⟩, words.drop 4096)
  | _ => none

@[simp] theorem parseRow_encoded {n m : Nat} (row : DartRow n m) (rest : List Nat) :
    parseRow n m (rowWords row ++ rest) = some (row, rest) := by
  cases row with
  | mk tail reverseIndex relation =>
      have taken := List.take_left' (l₂ := rest) (relationWords_length relation)
      have dropped := List.drop_left' (l₂ := rest) (relationWords_length relation)
      simp [rowWords, parseRow, taken, dropped]

def parseRows (vertices darts : Nat) :
    Nat → List Nat → Option (List (DartRow vertices darts) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (row, words) ← parseRow vertices darts words
      let (rows, words) ← parseRows vertices darts count words
      return (row :: rows, words)

@[simp] theorem parseRows_encoded {n m : Nat} (rows : List (DartRow n m)) (rest : List Nat) :
    parseRows n m rows.length (rows.flatMap rowWords ++ rest) = some (rows, rest) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [parseRows, List.append_assoc, ih]

def tableWords (table : Table) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

def tableBits (table : Table) : List Bool := encodeWords (tableWords table)

def decodeTableWords : List Nat → Option Table
  | vertices :: darts :: words => do
      let (parsed, trailing) ← parseRows vertices darts darts words
      if trailing = [] then
        if length_ok : parsed.length = darts then
          let rows : Rows vertices darts := ⟨parsed.toArray, by simpa using length_ok⟩
          if valid : Valid rows then some ⟨vertices, darts, rows, valid⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeTableWords_encoded (table : Table) :
    decodeTableWords (tableWords table) = some table := by
  cases table with
  | mk vertices darts rows valid =>
      have parsed := parseRows_encoded rows.toList []
      simp only [Vector.length_toList, List.append_nil] at parsed
      simp [tableWords, rowList, decodeTableWords, parsed, valid, Vector.toArray_toList]

def decodeTableBits (bits : List Bool) : Option Table :=
  decodeWords bits >>= decodeTableWords

@[simp] theorem decodeTableBits_encoded (table : Table) :
    decodeTableBits (tableBits table) = some table := by
  simp [decodeTableBits, tableBits]

@[simp] theorem rowWords_length {n m : Nat} (row : DartRow n m) :
    (rowWords row).length = 4098 := by simp [rowWords]

theorem rowsWords_length {n m : Nat} (rows : List (DartRow n m)) :
    (rows.flatMap rowWords).length = 4098 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [ih, Nat.mul_add, Nat.add_comm]

@[simp] theorem tableWords_length (table : Table) :
    (tableWords table).length = 2 + 4098 * table.darts := by
  simp only [tableWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, rowList_length]

end IndependentSetsGames.Foundations.PCP.GraphTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PortTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PortTables

open PoweringWalks

abbrev Label := GraphTables.Label

end IndependentSetsGames.Foundations.PCP.PortTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_GenericGraphTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.GenericGraphTables

open IndependentSetsGames.Foundations.Complexity

abbrev Label (q : Nat) := Fin q
abbrev RelationTable (q : Nat) := Vector Bool (q * q)

variable {q : Nat}

def relationIndex (q : Nat) : (Label q) × (Label q) ≃ Fin (q * q) := finProdFinEquiv

def relationAt (table : (RelationTable q)) (a b : (Label q)) : Bool :=
  table[(relationIndex q) (a, b)]

def relationOf (predicate : (Label q) → (Label q) → Bool) : (RelationTable q) :=
  Vector.ofFn (fun i => predicate ((relationIndex q).symm i).1 ((relationIndex q).symm i).2)

@[simp] theorem relationAt_relationOf (predicate : (Label q) → (Label q) → Bool) (a b : (Label q)) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (q vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : (RelationTable q)

abbrev Rows (q vertices darts : Nat) := Vector (DartRow q vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows q n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows q n m) (e : Fin m) (a b : (Label q)) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows q n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

structure Table (q : Nat) where
  vertices : Nat
  darts : Nat
  rows : Rows q vertices darts
  valid : Valid rows

def rowList (table : (Table q)) : List (DartRow q table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : (Table q)) : (rowList table).length = table.darts := by
  simp [rowList]

def semantics (table : (Table q)) : ConstraintGraph (Fin table.vertices) (Fin table.darts) (Label q) where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : (Table q)) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : (Table q)) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : (Table q)) (e : Fin table.darts) (a b : (Label q)) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : Rows q n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : (Table q) :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (e : Fin m) (a b : (Label q)) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G with
  | mk reverse hinv tail accepts htranspose =>
    cases H with
    | mk reverse' hinv' tail' accepts' htranspose' =>
      dsimp only at hr ht hp
      have he : reverse = reverse' := Equiv.ext hr
      cases he
      cases ht
      cases hp
      rfl

@[simp] theorem semantics_ofGraph {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) : semantics (ofGraph G) = G := by
  apply constraintGraph_ext
  · exact semantics_ofGraph_reverse G
  · funext e
    exact semantics_ofGraph_tail G e
  · funext e a b
    exact semantics_ofGraph_accepts G e a b

@[simp] theorem semantics_ofGraph_rejectionCount {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) (Label q)) (labeling : Fin n → (Label q)) :
    (semantics (ofGraph G)).rejectionCount labeling = G.rejectionCount labeling := by
  rw [semantics_ofGraph]
  rfl

def bitWord (b : Bool) : Nat := if b then 1 else 0

def relationWords (relation : (RelationTable q)) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : (RelationTable q)) :
    (relationWords relation).length = (q * q) := by simp [relationWords]

def rowWords {n m : Nat} (row : DartRow q n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

def tableWords (table : (Table q)) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

def tableBits (table : (Table q)) : List Bool := encodeWords (tableWords table)

@[simp] theorem rowWords_length {n m : Nat} (row : DartRow q n m) :
    (rowWords row).length = (q * q + 2) := by
  simp only [rowWords, List.length_append, List.length_cons, List.length_nil,
    relationWords_length]
  omega

end IndependentSetsGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

end IndependentSetsGames.Foundations.PCP.CloudPadding

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Finite2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

def cloudDarts (t : Table) (v : Fin t.vertices) : List (Fin t.darts) :=
  (List.finRange t.darts).filter (fun e => decide (t.rows[e].tail = v))

@[simp] theorem mem_cloudDarts (t : Table) (v : Fin t.vertices) (e : Fin t.darts) :
    e ∈ cloudDarts t v ↔ t.rows[e].tail = v := by
  simp [cloudDarts]

theorem cloudDarts_nodup (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange t.darts)

def cloudSize (t : Table) (v : Fin t.vertices) : Nat := (cloudDarts t v).length

def cloudSelect (t : Table) (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    Cloud (semantics t) v :=
  ⟨(cloudDarts t v).get i,
    (mem_cloudDarts t v _).1 (List.get_mem (cloudDarts t v) i)⟩

def cloudRank (t : Table) (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    Fin (cloudSize t v) :=
  ⟨(cloudDarts t v).idxOf e.val,
    List.idxOf_lt_length_of_mem ((mem_cloudDarts t v e.val).2 e.property)⟩

@[simp] theorem cloudSelect_val (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) :
    (cloudSelect t v i).val = (cloudDarts t v).get i := rfl

@[simp] theorem cloudRank_val (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) :
    (cloudRank t v e).val = (cloudDarts t v).idxOf e.val := rfl

@[simp] theorem cloudSelect_cloudRank (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : cloudSelect t v (cloudRank t v e) = e := by
  apply Subtype.ext
  exact List.idxOf_get (cloudRank t v e).isLt

@[simp] theorem cloudRank_cloudSelect (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) : cloudRank t v (cloudSelect t v i) = i := by
  apply Fin.ext
  exact List.get_idxOf (cloudDarts_nodup t v) i

def cloudEquiv (t : Table) (v : Fin t.vertices) :
    Cloud (semantics t) v ≃ Fin (cloudSize t v) where
  toFun := cloudRank t v
  invFun := cloudSelect t v
  left_inv := cloudSelect_cloudRank t v
  right_inv := cloudRank_cloudSelect t v

def oldCloudIndex (t : Table) (e : Fin t.darts) :
    Fin (cloudSize t t.rows[e].tail) := cloudRank t t.rows[e].tail ⟨e, rfl⟩

@[simp] theorem cloudSelect_oldCloudIndex (t : Table) (e : Fin t.darts) :
    (cloudSelect t t.rows[e].tail (oldCloudIndex t e)).val = e :=
  congrArg Subtype.val (cloudSelect_cloudRank t t.rows[e].tail ⟨e, rfl⟩)

abbrev PaddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :=
  Cloud (paddedGraph (semantics t) (fun u => Fin (padding u))) v

def paddedOld (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : PaddedCloud t padding v :=
  ⟨Sum.inl e.val, e.property⟩

def paddedNew (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (i : Fin (padding v)) : PaddedCloud t padding v :=
  ⟨Sum.inr ⟨v, i⟩, rfl⟩

def paddedCloudEquiv (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) : PaddedCloud t padding v ≃ Fin (cloudSize t v + padding v) :=
  (CloudPadding.paddedCloudEquiv (semantics t) (fun u => Fin (padding u)) v).trans
    ((Equiv.sumCongr (cloudEquiv t v) (Equiv.refl (Fin (padding v)))).trans
      finSumFinEquiv)

def paddedCloudRank (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    PaddedCloud t padding v → Fin (cloudSize t v + padding v) :=
  paddedCloudEquiv t padding v

def paddedCloudSelect (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    Fin (cloudSize t v + padding v) → PaddedCloud t padding v :=
  (paddedCloudEquiv t padding v).symm

@[simp] theorem paddedCloudSelect_rank (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : PaddedCloud t padding v) :
    paddedCloudSelect t padding v (paddedCloudRank t padding v e) = e :=
  (paddedCloudEquiv t padding v).symm_apply_apply e

@[simp] theorem paddedCloudRank_select (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    paddedCloudRank t padding v (paddedCloudSelect t padding v i) = i :=
  (paddedCloudEquiv t padding v).apply_symm_apply i

@[simp] theorem paddedCloudRank_old (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    paddedCloudRank t padding v (paddedOld t padding v e) =
      Fin.castAdd (padding v) (cloudRank t v e) := rfl

@[simp] theorem paddedCloudRank_new (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudRank t padding v (paddedNew t padding v i) =
      Fin.natAdd (cloudSize t v) i := rfl

@[simp] theorem paddedCloudRank_old_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    (paddedCloudRank t padding v (paddedOld t padding v e)).val =
      (cloudRank t v e).val := rfl

@[simp] theorem paddedCloudRank_new_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    (paddedCloudRank t padding v (paddedNew t padding v i)).val =
      cloudSize t v + i.val := rfl

@[simp] theorem paddedCloudSelect_castAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    paddedCloudSelect t padding v (Fin.castAdd (padding v) i) =
      paddedOld t padding v (cloudSelect t v i) := by
  apply (paddedCloudEquiv t padding v).injective
  change (paddedCloudEquiv t padding v)
      ((paddedCloudEquiv t padding v).symm (Fin.castAdd (padding v) i)) = _
  rw [Equiv.apply_symm_apply]
  change Fin.castAdd (padding v) i =
    Fin.castAdd (padding v) (cloudRank t v (cloudSelect t v i))
  rw [cloudRank_cloudSelect]

@[simp] theorem paddedCloudSelect_natAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudSelect t padding v (Fin.natAdd (cloudSize t v) i) =
      paddedNew t padding v i :=
  (paddedCloudEquiv t padding v).symm_apply_apply (paddedNew t padding v i)

end IndependentSetsGames.Foundations.PCP.PreprocessingCloudIndex

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_ExpanderTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.ExpanderTables

open PoweringWalks

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

def reverseIndex {v d : Nat} (table : Table v d) (i : Fin (v * d)) : Fin (v * d) :=
  table.rows[i]

def lookup {v d : Nat} (table : Table v d) (x : Fin v × Fin d) : Fin v × Fin d :=
  (rowIndex v d).symm (reverseIndex table (rowIndex v d x))

theorem lookup_involutive {v d : Nat} (table : Table v d) :
    Function.Involutive (lookup table) := by
  intro x
  simp only [lookup, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex v d).symm (table.involutive (rowIndex v d x))).trans
    ((rowIndex v d).symm_apply_apply x)

end IndependentSetsGames.Foundations.PCP.ExpanderTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Minimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

variable {W D B : Type*}

def reindex (G : ConstraintGraph V E A) (vertices : V ≃ W) (darts : E ≃ D)
    (labels : A ≃ B) : ConstraintGraph W D B where
  reverse := darts.symm.trans (G.reverse.trans darts)
  reverse_involutive := by
    intro d
    change darts (G.reverse (darts.symm (darts (G.reverse (darts.symm d))))) = d
    rw [darts.symm_apply_apply, G.reverse_involutive, darts.apply_symm_apply]
  tail := fun d => vertices (G.tail (darts.symm d))
  accepts := fun d a b => G.accepts (darts.symm d) (labels.symm a) (labels.symm b)
  reverse_accepts := by
    intro d a b
    simpa only [Equiv.trans_apply, darts.symm_apply_apply] using
      G.reverse_accepts (darts.symm d) (labels.symm a) (labels.symm b)

end IndependentSetsGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_PreprocessingRegularTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def vertexCount (t : GraphTables.Table) (padding : Fin t.vertices → Nat) : Nat :=
  t.darts + ∑ v, padding v

end IndependentSetsGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_CodeComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open IndependentSetsGames.Foundations.Hastad

def codeword {A : Type*} (a : A) : Cube A → Bool := fun x => x a

def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

end IndependentSetsGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AlphabetReduction

open IndependentSetsGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

abbrev InputCoordinate (A : Type*) := Bool × Cube A

def pairEncoding (accepts : A → A → Bool) (p : LegalPair accepts) :
    InputCoordinate A → Bool :=
  pairWord (codeword p.1.1) (codeword p.1.2)

end IndependentSetsGames.Foundations.PCP.AlphabetReduction
end
namespace IndependentSetsGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

end IndependentSetsGames.Foundations.PCP.UniformRestriction

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_QueryIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.QueryIncidence

structure Verifier (E X : Type*) (q : Nat) where
  query : E → Fin q → X
  accepts : E → (Fin q → Bool) → Bool

abbrev Label (q : Nat) := Fin q → Bool
abbrev Vertex (E X : Type*) := E ⊕ X
abbrev Dart (E : Type*) (q : Nat) := (E × Fin q) × Bool

variable {E X : Type*} {q : Nat}

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

@[simp] theorem decode_encodeRight (positive : 0 < q) (bit : Bool) :
    decodeRight positive (encodeRight bit) = bit := rfl

def canonicalSlot [DecidableEq X] (T : Verifier E X q) (event : E) (i : Fin q) : Fin q :=
  Fin.find (fun j => T.query event j = T.query event i) ⟨i, rfl⟩

def RepeatedConsistent (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  ∀ i j, T.query event i = T.query event j → label i = label j

instance repeatedConsistentDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (RepeatedConsistent T event label) := by
  unfold RepeatedConsistent
  infer_instance

def LeftValid (T : Verifier E X q) (event : E) (label : Label q) : Prop :=
  T.accepts event label = true ∧ RepeatedConsistent T event label

instance leftValidDecidable [DecidableEq X]
    (T : Verifier E X q) (event : E) (label : Label q) :
    Decidable (LeftValid T event label) := by
  unfold LeftValid
  infer_instance

def incidenceAccept [DecidableEq X] (T : Verifier E X q) (positive : 0 < q)
    (event : E) (slot : Fin q) (left right : Label q) : Bool :=
  decide (LeftValid T event left) &&
    decide (left (canonicalSlot T event slot) = decodeRight positive right)

def reverse : Dart E q → Dart E q := fun d => (d.1, !d.2)

theorem reverse_involutive : Function.Involutive (reverse : Dart E q → Dart E q) := by
  rintro ⟨⟨event, slot⟩, orientation⟩
  cases orientation <;> rfl

def reverseEquiv : Dart E q ≃ Dart E q where
  toFun := reverse
  invFun := reverse
  left_inv := reverse_involutive
  right_inv := reverse_involutive

def tail (T : Verifier E X q) : Dart E q → Vertex E X
  | ((event, _), false) => .inl event
  | ((event, slot), true) => .inr (T.query event slot)

def predicate [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    Dart E q → Label q → Label q → Bool
  | ((event, slot), false), a, b => incidenceAccept T positive event slot a b
  | ((event, slot), true), a, b => incidenceAccept T positive event slot b a

def graph [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    ConstraintGraph (Vertex E X) (Dart E q) (Label q) where
  reverse := reverseEquiv
  reverse_involutive := reverse_involutive
  tail := tail T
  accepts := predicate T positive
  reverse_accepts := by
    rintro ⟨⟨event, slot⟩, orientation⟩ a b
    cases orientation <;> rfl

@[simp] theorem card_label (q : Nat) : Fintype.card (Label q) = 2 ^ q := by
  simp [Label]

@[simp] theorem card_vertex [Fintype E] [Fintype X] :
    Fintype.card (Vertex E X) = Fintype.card E + Fintype.card X := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart [Fintype E] :
    Fintype.card (Dart E q) = 2 * q * Fintype.card E := by
  simp [Dart, Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end IndependentSetsGames.Foundations.PCP.QueryIncidence

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AlphabetGraph

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators

abbrev Address (V E A : Type*) := (V × Cube A) ⊕ (E × Cube (A × A))

abbrev LocalEvent (A : Type*) := Fin 4 × AlphabetReduction.InputCoordinate A ×
  Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A) × Cube (A × A)

abbrev Event (E A : Type*) := E × LocalEvent A

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev legal (G : ConstraintGraph V E A) (e : E) (p : A × A) : Prop :=
  G.accepts e p.1 p.2 = true

instance legalDecidable (G : ConstraintGraph V E A) (e : E) :
    DecidablePred (legal G e) :=
  fun p => inferInstanceAs (Decidable (G.accepts e p.1 p.2 = true))

def restrictTape (G : ConstraintGraph V E A) (e : E) (f : Cube (A × A)) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) := UniformRestriction.restrict (legal G e) f

def extendTape (G : ConstraintGraph V E A) (e : E)
    (f : Cube (AlphabetReduction.LegalPair (G.accepts e))) : Cube (A × A) :=
  UniformRestriction.extend (legal G e) f

def globalizeQuery (G : ConstraintGraph V E A) (e : E) :
    AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e)) → Address V E A
  | .inl (side, tape) => .inl ((if side then G.head e else G.tail e), tape)
  | .inr tape => .inr (e, extendTape G e tape)

def verifier (G : ConstraintGraph V E A) : QueryIncidence.Verifier (Event E A) (Address V E A) 6 where
  query := fun (e, kind, k, f, g, r₀, r₁, r₂) slot =>
    globalizeQuery G e (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
      (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
      (restrictTape G e r₁) (restrictTape G e r₂) slot)
  accepts := fun (_, kind, _, _, _, _, _, _) b => AssignmentTester.eventAccepts kind b

def vertexBlock (assignment : Address V E A → Bool) (v : V) : Cube A → Bool :=
  fun tape => assignment (.inl (v, tape))

omit [Nonempty A] in
@[simp] theorem card_event [Fintype E] :
    Fintype.card (Event E A) = Fintype.card E * Fintype.card (LocalEvent A) :=
  Fintype.card_prod _ _

def honestAssignment (G : ConstraintGraph V E A) (labeling : V → A) : Address V E A → Bool
  | .inl (v, tape) => tape (labeling v)
  | .inr (e, tape) => tape (labeling (G.tail e), labeling (G.head e))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
@[simp] theorem honest_vertexBlock (G : ConstraintGraph V E A) (labeling : V → A) (v : V) :
    vertexBlock (honestAssignment G labeling) v = CodeComposition.codeword (labeling v) := rfl

def graph [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A) :
    ConstraintGraph (QueryIncidence.Vertex (Event E A) (Address V E A))
      (QueryIncidence.Dart (Event E A) 6) (QueryIncidence.Label 6) := QueryIncidence.graph (verifier G) (by omega)

end IndependentSetsGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Enumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Enumeration

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem boolEquiv_val (bit : Bool) : (boolEquiv bit).val = bitValue bit := by
  cases bit <;> rfl

def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

@[simp] theorem productEquiv_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) (y : B) :
    (productEquiv left right (x, y)).val = (left x).val * b + (right y).val := by
  change (right y).val + b * (left x).val = _
  simp [Nat.mul_comm, Nat.add_comm]

def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

@[simp] theorem sumEquiv_inl_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) :
    (sumEquiv left right (.inl x)).val = (left x).val := rfl

@[simp] theorem sumEquiv_inr_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (y : B) :
    (sumEquiv left right (.inr y)).val = a + (right y).val := rfl

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

def cubeEquiv (q : Nat) : Cube (Fin q) ≃ Fin (tapeCount q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) boolEquiv).trans finFunctionFinEquiv

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

def pairCubeEquiv (q : Nat) : Cube (Fin q × Fin q) ≃ Fin (pairTapeCount q) :=
  (Equiv.arrowCongr (pairIndex q) (Equiv.refl Bool)).trans (cubeEquiv (q * q))

def inputCoordinateEquiv (q : Nat) :
    AlphabetReduction.InputCoordinate (Fin q) ≃ Fin (2 * tapeCount q) :=
  productEquiv boolEquiv (cubeEquiv q)

def fivePairTapesEquiv (q : Nat) :
    (Cube (Fin q × Fin q) × Cube (Fin q × Fin q) × Cube (Fin q × Fin q) ×
      Cube (Fin q × Fin q) × Cube (Fin q × Fin q)) ≃ Fin (fiveTapeCount q) :=
  (productEquiv (pairCubeEquiv q)
    (productEquiv (pairCubeEquiv q)
      (productEquiv (pairCubeEquiv q)
        (productEquiv (pairCubeEquiv q) (pairCubeEquiv q))))).trans
    (finCongr (by simp [fiveTapeCount, pow_succ, Nat.mul_assoc]))

def localEventEquiv (q : Nat) : AlphabetGraph.LocalEvent (Fin q) ≃ Fin (localCount q) :=
  (productEquiv (Equiv.refl (Fin 4))
    (productEquiv (inputCoordinateEquiv q) (fivePairTapesEquiv q))).trans
    (finCongr (by simp [localCount, Nat.mul_assoc]))

def eventEquiv (m q : Nat) :
    AlphabetGraph.Event (Fin m) (Fin q) ≃ Fin (eventCount m q) :=
  productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)

def addressEquiv (n m q : Nat) :
    AlphabetGraph.Address (Fin n) (Fin m) (Fin q) ≃ Fin (addressCount n m q) :=
  sumEquiv (productEquiv (Equiv.refl (Fin n)) (cubeEquiv q))
    (productEquiv (Equiv.refl (Fin m)) (pairCubeEquiv q))

def vertexEquiv (n m q : Nat) :
    QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) ≃ Fin (vertexCount n m q) :=
  sumEquiv (eventEquiv m q) (addressEquiv n m q)

def dartEquiv (m q : Nat) :
    QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6 ≃ Fin (dartCount m q) :=
  (productEquiv (productEquiv (eventEquiv m q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [dartCount, Nat.mul_assoc]))

def labelEquiv : QueryIncidence.Label 6 ≃ Fin 64 := cubeEquiv 6

@[simp] theorem inputCoordinateEquiv_val (q : Nat) (side : Bool) (tape : Cube (Fin q)) :
    (inputCoordinateEquiv q (side, tape)).val =
      bitValue side * tapeCount q + (cubeEquiv q tape).val := by
  simp [inputCoordinateEquiv]

@[simp] theorem eventEquiv_val (m q : Nat) (edge : Fin m)
    (sample : AlphabetGraph.LocalEvent (Fin q)) :
    (eventEquiv m q (edge, sample)).val = edge.val * localCount q +
      (localEventEquiv q sample).val := by
  change (localEventEquiv q sample).val + localCount q * edge.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inl_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (addressEquiv n m q (.inl (vertex, tape))).val =
      vertex.val * tapeCount q + (cubeEquiv q tape).val := by
  change (cubeEquiv q tape).val + tapeCount q * vertex.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inr_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (addressEquiv n m q (.inr (edge, tape))).val =
      n * tapeCount q + (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val) := by
  change n * tapeCount q + ((pairCubeEquiv q tape).val + pairTapeCount q * edge.val) = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem vertexEquiv_event_val (n m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) :
    (vertexEquiv n m q (.inl event)).val = (eventEquiv m q event).val := rfl

@[simp] theorem vertexEquiv_vertexAddress_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (vertexEquiv n m q (.inr (.inl (vertex, tape)))).val =
      eventCount m q + (vertex.val * tapeCount q + (cubeEquiv q tape).val) := by
  change eventCount m q + (addressEquiv n m q (.inl (vertex, tape))).val = _
  rw [addressEquiv_inl_val]

@[simp] theorem vertexEquiv_edgeAddress_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (vertexEquiv n m q (.inr (.inr (edge, tape)))).val =
      eventCount m q + (n * tapeCount q +
        (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val)) := by
  change eventCount m q + (addressEquiv n m q (.inr (edge, tape))).val = _
  rw [addressEquiv_inr_val]

@[simp] theorem dartEquiv_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q ((event, slot), orientation)).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue orientation := by
  change (boolEquiv orientation).val + 2 * (slot.val + 6 * (eventEquiv m q event).val) = _
  rw [boolEquiv_val]
  omega

def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

@[simp] theorem ordered_length {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).length = count := by simp [ordered]

@[simp] theorem ordered_refl (n : Nat) : ordered (Equiv.refl (Fin n)) = List.finRange n := rfl

@[simp] theorem ordered_bool : ordered boolEquiv = [false, true] := rfl

def localEvents (q : Nat) : List (AlphabetGraph.LocalEvent (Fin q)) :=
  ordered (localEventEquiv q)

@[simp] theorem localEvents_length (q : Nat) : (localEvents q).length = localCount q :=
  ordered_length _

@[simp] theorem card_cube (q : Nat) : Fintype.card (Cube (Fin q)) = tapeCount q := by
  simpa using Fintype.card_congr (cubeEquiv q)

@[simp] theorem card_pairCube (q : Nat) :
    Fintype.card (Cube (Fin q × Fin q)) = pairTapeCount q := by
  simpa using Fintype.card_congr (pairCubeEquiv q)

@[simp] theorem card_localEvent (q : Nat) :
    Fintype.card (AlphabetGraph.LocalEvent (Fin q)) = localCount q := by
  simpa using Fintype.card_congr (localEventEquiv q)

@[simp] theorem card_event (m q : Nat) :
    Fintype.card (AlphabetGraph.Event (Fin m) (Fin q)) = eventCount m q := by
  simpa using Fintype.card_congr (eventEquiv m q)

@[simp] theorem card_address (n m q : Nat) :
    Fintype.card (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) = addressCount n m q := by
  simpa using Fintype.card_congr (addressEquiv n m q)

@[simp] theorem card_vertex (n m q : Nat) :
    Fintype.card (QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q))) = vertexCount n m q := by
  simpa using Fintype.card_congr (vertexEquiv n m q)

@[simp] theorem card_dart (m q : Nat) :
    Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6) =
      dartCount m q := by
  simpa using Fintype.card_congr (dartEquiv m q)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Queries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Queries

open IndependentSetsGames.Foundations.Hastad

abbrev RawQuery (q : Nat) :=
  (Bool × Cube (Fin q)) ⊕ Cube (Fin q × Fin q)

abbrev LocalEvent (q : Nat) := AlphabetGraph.LocalEvent (Fin q)

def mask {q : Nat} (P : Fin q → Fin q → Bool) (f : Cube (Fin q × Fin q)) :
    Cube (Fin q × Fin q) := fun p => if P p.1 p.2 then f p else false

def xorTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a ^^ g a

def andTape {A : Type*} (f g : Cube A) : Cube A := fun a => f a && g a

def inputPairTape {q : Nat} (k : Bool × Cube (Fin q)) : Cube (Fin q × Fin q) :=
  fun p => if k.1 then k.2 p.2 else k.2 p.1

def query {q : Nat} (P : Fin q → Fin q → Bool) (event : LocalEvent q)
    (slot : Fin 6) : RawQuery q :=
  match event with
  | (kind, k, f, g, r₀, r₁, r₂) =>
    if kind = 0 then
      if slot = 0 then .inr (mask P f) else
      if slot = 1 then .inr (mask P g) else .inr (mask P (xorTape f g))
    else if kind = 1 then
      if slot = 0 then .inr (mask P r₀) else
      if slot = 1 then .inr (mask P (xorTape r₀ (andTape f g))) else
      if slot = 2 then .inr (mask P r₁) else
      if slot = 3 then .inr (mask P (xorTape r₁ f)) else
      if slot = 4 then .inr (mask P r₂) else .inr (mask P (xorTape r₂ g))
    else if kind = 2 then
      if slot = 0 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (fun _ => true)))
    else
      if slot = 0 then .inl k else
      if slot = 1 then .inr (mask P r₀) else
        .inr (mask P (xorTape r₀ (inputPairTape k)))

def globalize {q : Nat} {V E : Type*} (tail head : V) (edge : E) :
    RawQuery q → AlphabetGraph.Address V E (Fin q)
  | .inl (side, tape) => .inl ((if side then head else tail), tape)
  | .inr tape => .inr (edge, tape)

@[simp] theorem mask_idempotent {q : Nat} (P : Fin q → Fin q → Bool)
    (f : Cube (Fin q × Fin q)) : mask P (mask P f) = mask P f := by
  funext p
  cases hp : P p.1 p.2 <;> simp [mask, hp]

def extendQuery {q : Nat} (P : Fin q → Fin q → Bool) :
    AlphabetReduction.InputCoordinate (Fin q) ⊕ Cube (AlphabetReduction.LegalPair P) →
      RawQuery q
  | .inl k => .inl k
  | .inr tape => .inr (UniformRestriction.extend (fun p : Fin q × Fin q => P p.1 p.2 = true) tape)

theorem query_eq_extend_eventQueries {q : Nat} (P : Fin q → Fin q → Bool)
    (kind : Fin 4) (k : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) (slot : Fin 6) :
    query P (kind, k, f, g, r₀, r₁, r₂) slot =
      extendQuery P (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding P) kind k
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) f)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) g)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₀)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₁)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₂) slot) := by
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [query, AssignmentTester.eventQueries, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> simp_all only [extendQuery]
  all_goals rfl

theorem globalize_extendQuery {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E)
    (x : AlphabetReduction.InputCoordinate (Fin q) ⊕
      Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    globalize (G.tail e) (G.head e) e (extendQuery (G.accepts e) x) =
      AlphabetGraph.globalizeQuery G e x := by
  cases x with
  | inl k => cases k; rfl
  | inr tape => rfl

theorem globalize_query {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E) (event : LocalEvent q) (slot : Fin 6) :
    globalize (G.tail e) (G.head e) e (query (G.accepts e) event slot) =
      (AlphabetGraph.verifier G).query (e, event) slot := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rw [query_eq_extend_eventQueries]
  exact globalize_extendQuery G e _

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Queries
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

def sameAddress (selfLoop : Bool) : RawQuery q → RawQuery q → Bool
  | .inl (side, f), .inl (side', g) => ((side == side') || selfLoop) && decide (f = g)
  | .inr f, .inr g => decide (f = g)
  | _, _ => false

@[simp] theorem sameAddress_refl (selfLoop : Bool) (x : RawQuery q) :
    sameAddress selfLoop x x = true := by
  rcases x with ⟨side, f⟩ | f <;> simp [sameAddress]

theorem globalize_eq_iff {V E : Type*} [DecidableEq V]
    (tail head : V) (edge : E) (selfLoop : Bool)
    (hloop : selfLoop = decide (tail = head)) (x y : RawQuery q) :
    globalize tail head edge x = globalize tail head edge y ↔
      sameAddress selfLoop x y = true := by
  rcases x with ⟨side, f⟩ | f <;> rcases y with ⟨side', g⟩ | g
  · cases side <;> cases side'
    · simp [globalize, sameAddress]
    · simp [globalize, sameAddress, hloop]
    · simp [globalize, sameAddress, hloop,
        show head = tail ↔ tail = head from eq_comm]
    · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]

def eqProfile (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i j : Fin 6) : Bool := sameAddress selfLoop (queries i) (queries j)

@[simp] theorem eqProfile_refl (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (i : Fin 6) : eqProfile selfLoop queries i i = true := sameAddress_refl _ _

def canonicalSlot (selfLoop : Bool) (queries : Fin 6 → RawQuery q) (i : Fin 6) : Fin 6 :=
  Fin.find (fun j => eqProfile selfLoop queries j i = true) ⟨i, eqProfile_refl _ _ _⟩

def RepeatedConsistent (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Prop :=
  ∀ i j, eqProfile selfLoop queries i j = true → label i = label j

instance repeatedConsistentDecidable (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (label : QueryIncidence.Label 6) : Decidable (RepeatedConsistent selfLoop queries label) := by
  unfold RepeatedConsistent
  infer_instance

def incidenceAccept (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) : Bool :=
  decide (accept left = true ∧ RepeatedConsistent selfLoop queries left) &&
    decide (left (canonicalSlot selfLoop queries slot) = right 0)

def predicate (selfLoop : Bool) (queries : Fin 6 → RawQuery q)
    (accept : QueryIncidence.Label 6 → Bool) (slot : Fin 6) (orientation : Bool)
    (a b : QueryIncidence.Label 6) : Bool :=
  if orientation then incidenceAccept selfLoop queries accept slot b a
  else incidenceAccept selfLoop queries accept slot a b

def relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable :=
  GraphTables.relationOf fun a b =>
    predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
      slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)

@[simp] theorem relationAt_relation (P : Fin q → Fin q → Bool) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt (relation P selfLoop event slot orientation) a b =
      predicate selfLoop (query P event) (AssignmentTester.eventAccepts event.1)
        slot orientation (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  exact GraphTables.relationAt_relationOf _ _ _

def oldPredicate (old : Vector Bool (q * q)) (a b : Fin q) : Bool :=
  old[(finProdFinEquiv (a, b) : Fin (q * q))]

def relationFromTable (old : Vector Bool (q * q)) (selfLoop : Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool) :
    GraphTables.RelationTable := relation (oldPredicate old) selfLoop event slot orientation

@[simp] theorem oldPredicate_relationAt (old : GraphTables.RelationTable)
    (a b : GraphTables.Label) : oldPredicate old a b = GraphTables.relationAt old a b := rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Semantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations
open Hastad
open Queries
variable {q : Nat}

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem eqProfile_query_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (i j : Fin 6) :
    eqProfile (decide (G.tail e = G.head e)) (query (G.accepts e) event) i j = true ↔
      (AlphabetGraph.verifier G).query (e, event) i =
        (AlphabetGraph.verifier G).query (e, event) j := by
  rw [← globalize_query G e event i, ← globalize_query G e event j]
  exact (globalize_eq_iff (G.tail e) (G.head e) e _ rfl _ _).symm

theorem canonicalSlot_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    canonicalSlot (decide (G.tail e = G.head e)) (query (G.accepts e) event) slot =
      QueryIncidence.canonicalSlot (AlphabetGraph.verifier G) (e, event) slot := by
  unfold canonicalSlot QueryIncidence.canonicalSlot
  apply Fin.find_congr'
  exact eqProfile_query_iff G e event _ slot

omit [DecidableEq E] in
theorem repeatedConsistent_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    RepeatedConsistent (decide (G.tail e = G.head e)) (query (G.accepts e) event) label ↔
      QueryIncidence.RepeatedConsistent (AlphabetGraph.verifier G) (e, event) label := by
  constructor
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mpr hij)
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mp hij)

omit [DecidableEq V] [DecidableEq E] in
theorem verifier_accepts (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    (AlphabetGraph.verifier G).accepts (e, event) label =
      AssignmentTester.eventAccepts event.1 label := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rfl

theorem incidenceAccept_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) :
    incidenceAccept (decide (G.tail e = G.head e)) (query (G.accepts e) event)
      (AssignmentTester.eventAccepts event.1) slot left right =
      QueryIncidence.incidenceAccept (AlphabetGraph.verifier G) (by decide) (e, event) slot
        left right := by
  simp only [incidenceAccept, QueryIncidence.incidenceAccept, QueryIncidence.LeftValid,
    verifier_accepts, repeatedConsistent_iff, canonicalSlot_eq,
    QueryIncidence.decodeRight, QueryIncidence.zeroSlot]
  rfl

theorem relationAt_relation_graph (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt
        (relation (G.accepts e) (decide (G.tail e = G.head e)) event slot orientation) a b =
      (AlphabetGraph.graph G).accepts (((e, event), slot), orientation)
        (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  rw [relationAt_relation]
  cases orientation <;>
    exact incidenceAccept_eq G e event slot _ _

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

def rowFromDart (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    GraphTables.DartRow (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  let edge := dart.1.1.1
  let event := dart.1.1.2
  let slot := dart.1.2
  let old := input.rows[edge]
  let head := input.rows[old.reverseIndex].tail
  { tail := Enumeration.vertexEquiv input.vertices input.darts q
      (if dart.2 then
        .inr (Queries.globalize old.tail head edge
          (Queries.query (GenericGraphTables.relationAt old.relation) event slot))
      else .inl (edge, event))
    reverseIndex := Enumeration.dartEquiv input.darts q (dart.1, !dart.2)
    relation := Relations.relationFromTable old.relation (decide (old.tail = head))
      event slot dart.2 }

def rows (input : GenericGraphTables.Table q) :
    GraphTables.Rows (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  Vector.ofFn (fun index =>
    rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index))

@[simp] theorem rows_at (input : GenericGraphTables.Table q)
    (index : Fin (Enumeration.dartCount input.darts q)) :
    (rows input)[index] =
      rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index) := by
  simp [rows]

theorem dartRow_ext {n m : Nat} {left right : GraphTables.DartRow n m}
    (ht : left.tail = right.tail) (hr : left.reverseIndex = right.reverseIndex)
    (hp : left.relation = right.relation) : left = right := by
  cases left
  cases right
  cases ht
  cases hr
  cases hp
  rfl

theorem relation_ext {left right : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt left a b = GraphTables.relationAt right a b) :
    left = right := by
  apply Vector.ext
  intro i hi
  let labels := GraphTables.relationIndex.symm (⟨i, hi⟩ : Fin 4096)
  have index : GraphTables.relationIndex labels = (⟨i, hi⟩ : Fin 4096) :=
    GraphTables.relationIndex.apply_symm_apply _
  have point := h labels.1 labels.2
  simpa only [GraphTables.relationAt, index, Fin.getElem_fin] using point

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Semantics2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Table
variable {q : Nat}

theorem rowFromDart_eq_graphRow (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    rowFromDart input dart =
      { tail := Enumeration.vertexEquiv input.vertices input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).tail dart)
        reverseIndex := Enumeration.dartEquiv input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).reverse dart)
        relation := GraphTables.relationOf (fun a b =>
          (AlphabetGraph.graph (GenericGraphTables.semantics input)).accepts dart
            (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)) } := by
  rcases dart with ⟨⟨⟨edge, event⟩, slot⟩, orientation⟩
  apply dartRow_ext
  · cases orientation with
    | false => rfl
    | true =>
      have query := Queries.globalize_query (GenericGraphTables.semantics input)
        edge event slot
      have predicate : (GenericGraphTables.semantics input).accepts edge =
          GenericGraphTables.relationAt input.rows[edge].relation := rfl
      rw [predicate] at query
      simpa only [rowFromDart, AlphabetGraph.graph, QueryIncidence.graph,
        QueryIncidence.tail, GenericGraphTables.semantics_tail,
        ConstraintGraph.head, GenericGraphTables.semantics_reverse,
        ite_true] using
        congrArg (fun address => Enumeration.vertexEquiv input.vertices input.darts q
          (.inr address)) query
  · rfl
  · apply relation_ext
    intro a b
    rw [GraphTables.relationAt_relationOf]
    exact Relations.relationAt_relation_graph (GenericGraphTables.semantics input)
      edge event slot orientation a b

theorem rows_eq_graphRows (input : GenericGraphTables.Table q) :
    rows input = GraphTables.graphRows
      (GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv) := by
  apply Vector.ext
  intro i hi
  simp only [rows, GraphTables.graphRows, Vector.getElem_ofFn]
  exact rowFromDart_eq_graphRow input
    ((Enumeration.dartEquiv input.darts q).symm ⟨i, hi⟩)

theorem rows_valid (input : GenericGraphTables.Table q) : GraphTables.Valid (rows input) := by
  rw [rows_eq_graphRows]
  exact GraphTables.graphRows_valid _

def build (input : GenericGraphTables.Table q) : GraphTables.Table where
  vertices := Enumeration.vertexCount input.vertices input.darts q
  darts := Enumeration.dartCount input.darts q
  rows := rows input
  valid := rows_valid input

@[simp] theorem build_vertices (input : GenericGraphTables.Table q) :
    (build input).vertices = Enumeration.vertexCount input.vertices input.darts q := rfl

@[simp] theorem build_darts (input : GenericGraphTables.Table q) :
    (build input).darts = Enumeration.dartCount input.darts q := rfl

@[simp] theorem rowList_length (input : GenericGraphTables.Table q) :
    (GraphTables.rowList (build input)).length = Enumeration.dartCount input.darts q := by
  exact GraphTables.rowList_length (build input)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Table

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_InitialGraph
attribute [-instance] _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.InitialGraph

open Target

abbrev Label := Bool × Bool × Bool
abbrev Vertex (F : Formula) := (Fin F.«variables» ⊕ Fin F.clauses.length) ⊕ Unit
abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

instance slotFintype : Fintype Slot where
  elems := {Slot.first, Slot.second, Slot.third}
  complete := by intro s; cases s <;> simp

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableVertex (F : Formula) (v : Fin F.«variables») : Vertex F := .inl (.inl v)
def clauseVertex (F : Formula) (i : Fin F.clauses.length) : Vertex F := .inl (.inr i)
def dummyVertex (F : Formula) : Vertex F := .inr ()

def reverse (F : Formula) : Dart F → Dart F
  | .inl (event, orientation) => .inl (event, !orientation)
  | .inr _ => .inr ()

theorem reverse_involutive (F : Formula) : Function.Involutive (reverse F) := by
  intro d
  cases d with
  | inl pair => rcases pair with ⟨e, b⟩; cases b <;> rfl
  | inr u => cases u; rfl

def reverseEquiv (F : Formula) : Dart F ≃ Dart F where
  toFun := reverse F
  invFun := reverse F
  left_inv := reverse_involutive F
  right_inv := reverse_involutive F

def tail (F : Formula) : Dart F → Vertex F
  | .inl (event, false) => clauseVertex F event.1
  | .inl (event, true) => variableVertex F (nameAt (clauseAt F event.1) event.2)
  | .inr _ => dummyVertex F

def toClauseAnswer (label : Label) : ClauseAnswer := ⟨label.1, label.2.1, label.2.2⟩
def fromClauseAnswer (answer : ClauseAnswer) : Label := (answer.first, answer.second, answer.third)

@[simp] theorem to_fromClauseAnswer (answer : ClauseAnswer) :
    toClauseAnswer (fromClauseAnswer answer) = answer := by
  cases answer; rfl

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

def incidenceAccept (F : Formula) (event : RandomEvent F)
    (clauseLabel variableAnswer : Label) : Bool :=
  variableValid variableAnswer &&
    (localSatisfies (clauseAt F event.1) (toClauseAnswer clauseLabel) &&
      decide (answerAt (toClauseAnswer clauseLabel) event.2 = variableAnswer.1))

def predicate (F : Formula) : Dart F → Label → Label → Bool
  | .inl (event, false), a, b => incidenceAccept F event a b
  | .inl (event, true), a, b => incidenceAccept F event b a
  | .inr _, _, _ => true

def raw (F : Formula) : ConstraintGraph (Vertex F) (Dart F) Label where
  reverse := reverseEquiv F
  reverse_involutive := reverse_involutive F
  tail := tail F
  accepts := predicate F
  reverse_accepts := by
    intro d a b
    cases d with
    | inl pair => rcases pair with ⟨event, orientation⟩; cases orientation <;> rfl
    | inr u => rfl

@[simp] theorem card_vertex (F : Formula) :
    Fintype.card (Vertex F) = F.«variables» + F.clauses.length + 1 := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

end IndependentSetsGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_AlphabetRetraction
attribute [-instance] _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

def pullback (G : ConstraintGraph V E A) (decode : B → A) : ConstraintGraph V E B where
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  tail := G.tail
  accepts := fun e b c => G.accepts e (decode b) (decode c)
  reverse_accepts := fun e b c => G.reverse_accepts e (decode b) (decode c)

@[simp] theorem edgeSatisfied_pullback (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) (e : E) :
    (pullback G decode).edgeSatisfied labeling e =
      G.edgeSatisfied (decode ∘ labeling) e := rfl

@[simp] theorem rejectionCount_pullback [Fintype E] (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) :
    (pullback G decode).rejectionCount labeling =
      G.rejectionCount (decode ∘ labeling) := rfl

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, c⟩
  rfl

end IndependentSetsGames.Foundations.PCP.AlphabetRetraction

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_RawInitialTables
attribute [-instance] _root_.OAI.IndependentSetsGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialTables

open Target GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

def slotOrder : Slot ≃ Fin 3 where
  toFun
    | .first => 0
    | .second => 1
    | .third => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .third
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (IndependentSetsGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := IndependentSetsGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := IndependentSetsGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (IndependentSetsGames.Integration.BinaryCoordinates.pack
      (IndependentSetsGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [IndependentSetsGames.Integration.BinaryCoordinates.pack_unpack]

def labelOrder : AlphabetRetraction.Label64 ≃ GraphTables.Label := binaryOrder 6

def vertexOrder (F : Formula) :
    InitialGraph.Vertex F ≃ Fin (F.«variables» + F.clauses.length + 1) :=
  ((finSumFinEquiv.sumCongr unitOrder).trans finSumFinEquiv)

def eventOrder (F : Formula) : RandomEvent F ≃ Fin (F.clauses.length * 3) :=
  ((Equiv.refl (Fin F.clauses.length)).prodCongr slotOrder).trans finProdFinEquiv

def dartOrder (F : Formula) : InitialGraph.Dart F ≃ Fin (6 * F.clauses.length + 1) :=
  (((((eventOrder F).prodCongr finTwoEquiv.symm).trans finProdFinEquiv).sumCongr
    unitOrder).trans finSumFinEquiv).trans (finCongr (by omega))

def raw64 (F : Formula) : ConstraintGraph (InitialGraph.Vertex F)
    (InitialGraph.Dart F) AlphabetRetraction.Label64 :=
  AlphabetRetraction.pullback (InitialGraph.raw F) AlphabetRetraction.decode64

def table (F : Formula) : GraphTables.Table :=
  GraphTables.ofEnumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder

@[simp] theorem table_vertices (F : Formula) :
    (table F).vertices = F.«variables» + F.clauses.length + 1 := rfl

@[simp] theorem table_darts (F : Formula) : (table F).darts = 6 * F.clauses.length + 1 := rfl

end IndependentSetsGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Contexts
attribute [-instance] _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceContexts

open Target PCP

def clauseAnswerEquiv : ClauseAnswer ≃ Bool × Bool × Bool where
  toFun a := (a.first, a.second, a.third)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

def clauseAnswerFinEquiv : ClauseAnswer ≃ Fin 8 :=
  clauseAnswerEquiv.trans
    ((Equiv.prodCongr finTwoEquiv.symm
      (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv))

instance clauseAnswerFintype : Fintype ClauseAnswer :=
  Fintype.ofEquiv (Bool × Bool × Bool) clauseAnswerEquiv.symm

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

@[simp] theorem card_clauseAnswer : Fintype.card ClauseAnswer = 8 := by
  rw [Fintype.card_congr clauseAnswerFinEquiv]
  rfl

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

abbrev J (u : ℕ) := Fin u → ClauseAnswer
abbrev ClauseContext (F : Formula) (u : ℕ) := Fin u → Fin F.clauses.length
abbrev VariableContext (F : Formula) (u : ℕ) := Fin u → Fin F.«variables»
@[simp] theorem card_J (u : ℕ) : Fintype.card (J u) = 8 ^ u := by simp [J]
@[simp] theorem card_ClauseContext (F : Formula) (u : ℕ) :
    Fintype.card (ClauseContext F u) = F.clauses.length ^ u := by simp [ClauseContext]
@[simp] theorem card_VariableContext (F : Formula) (u : ℕ) :
    Fintype.card (VariableContext F u) = F.«variables» ^ u := by simp [VariableContext]

def localConsistent {n : ℕ} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  decide (∀ s s' : Slot, nameAt clause s = nameAt clause s' →
    answerAt answer s = answerAt answer s')

@[simp] theorem localConsistent_eq_true_iff {n : ℕ}
    (clause : Clause n) (answer : ClauseAnswer) :
    localConsistent clause answer = true ↔
      ∀ s s' : Slot, nameAt clause s = nameAt clause s' →
        answerAt answer s = answerAt answer s' := by
  simp [localConsistent]

def canonicalSlot {n : ℕ} (clause : Clause n) (v : Fin n) : Slot :=
  if nameAt clause .first = v then .first
  else if nameAt clause .second = v then .second else .third

def baseAccepts (F : Formula) (v : Fin F.«variables») (c : Fin F.clauses.length)
    (i : Bool) (j : ClauseAnswer) : Bool :=
  decide (localSatisfies (clauseAt F c) j = true ∧
    localConsistent (clauseAt F c) j = true ∧
    answerAt j (canonicalSlot (clauseAt F c) v) = i)

@[simp] theorem baseAccepts_eq_true_iff (F : Formula) (v : Fin F.«variables»)
    (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    baseAccepts F v c i j = true ↔
      localSatisfies (clauseAt F c) j = true ∧
      localConsistent (clauseAt F c) j = true ∧
      answerAt j (canonicalSlot (clauseAt F c) v) = i := by
  simp [baseAccepts]

end IndependentSetsGames.Foundations.Hastad.SourceContexts

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators

noncomputable section

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

def pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ) : FiniteDistribution Γ := by
  classical
  exact
    { weight := fun y => ∑ x, if f x = y then μ.weight x else 0
      nonnegative := fun y => Finset.sum_nonneg fun x _ => by
        split
        · exact μ.nonnegative x
        · exact le_rfl
      normalized := by
        rw [Finset.sum_comm]
        simpa using μ.normalized }

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

end FiniteDistribution

abbrev Strategy (Q₁ Q₂ A₁ A₂ : Type*) := (Q₁ → A₁) × (Q₂ → A₂)

structure Game (Q₁ Q₂ A₁ A₂ : Type*) [Fintype Q₁] [Fintype Q₂]
    [Fintype A₁] [Fintype A₂] where
  questions : FiniteDistribution (Q₁ × Q₂)
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def tupleQuestionEquiv (n : Nat) :
    (Fin n → Q₁ × Q₂) ≃ (Fin n → Q₁) × (Fin n → Q₂) where
  toFun questions := (fun i => (questions i).1, fun i => (questions i).2)
  invFun questions := fun i => (questions.1 i, questions.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def repetition (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { questions := (G.questions.iid n).transport (tupleQuestionEquiv n)
      accepts := fun x y a b => decide (∀ i, G.accepts (x i) (y i) (a i) (b i) = true) }

@[simp] theorem repetition_question_weight (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition n).questions.weight questions =
      ∏ i, G.questions.weight (questions.1 i, questions.2 i) := rfl

@[simp] theorem repetition_accepts_iff (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (x : Fin n → Q₁) (y : Fin n → Q₂) (a : Fin n → A₁) (b : Fin n → A₂) :
    (G.repetition n).accepts x y a b = true ↔
      ∀ i, G.accepts (x i) (y i) (a i) (b i) = true := by
  classical
  simp [repetition]

def coordinateWin (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (coordinate : Fin n) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool :=
  G.accepts (questions.1 coordinate) (questions.2 coordinate)
    (strategy.1 questions.1 coordinate) (strategy.2 questions.2 coordinate)

def selectedWins (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (questions : (Fin n → Q₁) × (Fin n → Q₂)) : Bool := by
  classical
  exact decide (∀ i ∈ selected, G.coordinateWin strategy i questions = true)

@[simp] theorem selectedWins_empty (G : Game Q₁ Q₂ A₁ A₂) {n : Nat}
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins strategy ∅ questions = true := by
  simp [selectedWins]

end Game

end

end IndependentSetsGames.Foundations.Games

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Repetition_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Games.FiniteDistribution
open scoped BigOperators

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

end IndependentSetsGames.Foundations.Games.FiniteDistribution

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  {n : Nat}

def selectedSuccess (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) : ℝ :=
  (G.repetition n).questions.probability (G.selectedWins strategy selected)

@[simp] theorem selectedSuccess_empty (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    G.selectedSuccess strategy ∅ = 1 := by
  have h : G.selectedWins strategy ∅ = fun _ => true :=
    funext (G.selectedWins_empty strategy)
  rw [selectedSuccess, h, FiniteDistribution.probability_true]

end Game

end IndependentSetsGames.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Fourier_Game
attribute [-instance] _root_.OAI.IndependentSetsGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem event_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    Nonempty (RandomEvent F) :=
  ⟨(⟨0, List.length_pos_iff.mpr hne⟩, .first)⟩

def eventLaw (F : Formula) (hne : F.clauses ≠ []) :
    FiniteDistribution (RandomEvent F) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  exact FiniteDistribution.uniform _

def visibleQuestion (F : Formula) (e : RandomEvent F) :
    Fin F.«variables» × Fin F.clauses.length :=
  (nameAt (clauseAt F e.1) e.2, e.1)

def baseGame (F : Formula) (hne : F.clauses ≠ []) :
    Game (Fin F.«variables») (Fin F.clauses.length) Bool ClauseAnswer where
  questions := (eventLaw F hne).pushforward (visibleQuestion F)
  accepts := baseAccepts F

@[simp] theorem baseGame_accepts (F : Formula) (hne : F.clauses ≠ [])
    (v : Fin F.«variables») (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    (baseGame F hne).accepts v c i j = baseAccepts F v c i j := rfl

end IndependentSetsGames.Foundations.Hastad.SourceGame

end

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_VerifierCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.VerifierToCNF

open Target

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

abbrev Pattern (q : Nat) := Fin q → Bool

def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.«variables» + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.«variables») : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.«variables» (finProdFinEquiv (finProdFinEquiv (e, p), j))

def liftLiteral {q : Nat} (V : FiniteVerifier q) (l : Literal V.«variables») :
    Literal (outputVariables V) := ⟨oldIndex V l.variableIndex, l.positive⟩

def forbiddenLiteral {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (i : Fin q) : Literal V.«variables» :=
  ⟨V.query e i, !(patternAt q p i)⟩

def forbiddenClause {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Literal (outputVariables V)) :=
  List.ofFn (fun i => liftLiteral V (forbiddenLiteral V e p i))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, c], [] => [#v[a, b, c]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun c => c.eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, c] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.«variables» → Bool :=
  fun v => B (oldIndex V v)

def mismatchBits {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) : List Bool :=
  List.ofFn (fun i => (forbiddenLiteral V e p i).eval A)

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (v : Fin V.«variables») :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

theorem twelve_query_clause_count (V : FiniteVerifier 12) :
    (convert V (by decide)).clauses.length = V.events * 40960 := by
  simpa only [twelve_query_factor] using convert_clause_count V (by decide)

end IndependentSetsGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.FinalBooleanVerifier

open Target

abbrev Label := Fin 6 → Bool

variable {V E : Type*} {n m : Nat}

def bitIndex (vertices : V ≃ Fin n) (v : V) (j : Fin 6) : Fin (n * 6) :=
  finProdFinEquiv (vertices v, j)

def labelsOfBits (vertices : V ≃ Fin n) (assignment : Fin (n * 6) → Bool) : V → Label :=
  fun v j => assignment (bitIndex vertices v j)

def bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) : Fin (n * 6) → Bool :=
  fun k =>
    let pair : Fin n × Fin 6 := finProdFinEquiv.symm k
    labeling (vertices.symm pair.1) pair.2

@[simp] theorem labelsOfBits_bitsOfLabels (vertices : V ≃ Fin n) (labeling : V → Label) :
    labelsOfBits vertices (bitsOfLabels vertices labeling) = labeling := by
  funext v j
  simp only [labelsOfBits, bitsOfLabels, bitIndex, Equiv.symm_apply_apply]

abbrev verifier (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    VerifierToCNF.FiniteVerifier 12 where
  «variables» := n * 6
  events := m
  query := fun e i => Fin.addCases (motive := fun _ : Fin (6 + 6) => Fin (n * 6))
    (fun j : Fin 6 => bitIndex vertices (G.tail (edges.symm e)) j)
    (fun j : Fin 6 => bitIndex vertices (G.head (edges.symm e)) j) i
  accepts := fun e bits => G.accepts (edges.symm e)
    (fun j => bits (Fin.castAdd 6 j)) (fun j => bits (Fin.natAdd 6 j))

def cnf (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) : Formula :=
  VerifierToCNF.convert (verifier G vertices edges) (by decide)

theorem cnf_clause_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).clauses.length = m * 40960 :=
  VerifierToCNF.twelve_query_clause_count (verifier G vertices edges)

end IndependentSetsGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

abbrev labelEquiv : Label ≃ Fin 64 := AlphabetTable.Enumeration.labelEquiv

def labelIndex (label : Label) : Fin 64 := labelEquiv label

def tableGraph (table : GraphTables.Table) :
    ConstraintGraph (Fin table.vertices) (Fin table.darts) Label :=
  (GraphTables.semantics table).reindex (Equiv.refl _) (Equiv.refl _) labelEquiv.symm

@[simp] theorem tableGraph_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).tail e = table.rows[e].tail := rfl

@[simp] theorem tableGraph_reverse (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem tableGraph_accepts (table : GraphTables.Table) (e : Fin table.darts)
    (a b : Label) :
    (tableGraph table).accepts e a b =
      GraphTables.relationAt table.rows[e].relation (labelIndex a) (labelIndex b) := rfl

end IndependentSetsGames.Foundations.Complexity.FinalCNFPattern

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.StdSimplexCompat
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Expansion_Capped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.ShortestPaths

structure Capped (B : ℕ) where
  val : ℕ
  bound : val ≤ B+1
  deriving DecidableEq

namespace Capped

@[ext] lemma ext {B : ℕ} {a b : Capped B} (h : a.val=b.val) : a=b := by
  cases a; cases b; simp_all

def clip (B : ℕ) (c : ℕ∞) : Capped B :=
  ⟨if c=⊤ then B+1 else min c.toNat (B+1),by split <;> simp⟩

@[simp] lemma clip_top (B : ℕ) : (clip B ⊤).val = B+1 := by simp [clip]
@[simp] lemma clip_nat (B n : ℕ) : (clip B (n:ℕ∞)).val = min n (B+1) := by simp [clip]

end Capped
end LargeIndependentSets.ShortestPaths

namespace LargeIndependentSets.ShortestPaths.Capped

abbrev Matrix (B n : ℕ) := Vector (Vector (Capped B) n) n

def Matrix.get {B n : ℕ} (a : Matrix B n) (i j : Fin n) : Capped B := a[i.val][j.val]

end LargeIndependentSets.ShortestPaths.Capped

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineFixedBlockMap
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

section Chains

variable {K Λ σ : Type} {N : Nat}

def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

theorem fill_apply (slots : List (Fin N)) (bits buffer : Buffer N) (i : Fin N) :
    fill slots bits buffer i = if i ∈ slots then bits i else buffer i := by
  induction slots generalizing buffer with
  | nil => simp [fill]
  | cons j slots ih =>
      change fill slots bits (Function.update buffer j (bits j)) i = _
      rw [ih]
      by_cases hm : i ∈ slots
      · simp [hm]
      · by_cases he : i = j <;> simp [hm, he]

@[simp] theorem fill_all (bits buffer : Buffer N) :
    fill (List.ofFn id) bits buffer = bits := by
  funext i
  simp [fill_apply, List.mem_ofFn]

end Chains

end IndependentSetsGames.Foundations.Complexity.MachineFixedBlockMap

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_FinalCNFMachine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

abbrev Buffer (N : Nat) := MachineFixedBlockMap.Buffer N

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Machine
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Hastad.SourceMachine

open Turing
open IndependentSetsGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

end IndependentSetsGames.Foundations.Hastad.SourceMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineUnaryCounter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

end IndependentSetsGames.Foundations.Complexity.MachineUnaryCounter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineLookupCore
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def tapes (index source destination : K) (base : K → List Bool)
    (counter input output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base index counter) source input)
    destination output

@[simp] theorem tapes_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output index = counter := by
  simp [tapes, his, hid]

@[simp] theorem tapes_source (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) :
    tapes index source destination base counter input output source = input := by
  simp [tapes, hsd]

@[simp] theorem tapes_destination (index source destination : K)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output destination = output := by
  simp [tapes]

end IndependentSetsGames.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Lookup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open IndependentSetsGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

def rowBits {q n m : Nat} (row : DartRow q n m) : List Bool := encodeWords (rowWords row)

def rowsBits {q n m : Nat} (rows : List (DartRow q n m)) : List Bool :=
  encodeWords (rows.flatMap rowWords)

@[simp] theorem rowsBits_nil {q n m : Nat} : rowsBits ([] : List (DartRow q n m)) = [] := rfl

@[simp] theorem rowsBits_cons {q n m : Nat} (row : DartRow q n m)
    (rows : List (DartRow q n m)) : rowsBits (row :: rows) = rowBits row ++ rowsBits rows := by
  simp only [rowsBits, List.flatMap_cons, encodeWords_append, rowBits]

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_ReadRelation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open IndependentSetsGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

def relationEquiv (q : Nat) : RelationTable q ≃ (Fin (q * q) → Bool) where
  toFun relation i := relation[i.val]
  invFun := Vector.ofFn
  left_inv relation := Vector.ofFn_getElem
  right_inv bits := by funext i; simp

@[instance_reducible] def relationFintype (q : Nat) : Fintype (RelationTable q) :=
  Fintype.ofEquiv (Fin (q * q) → Bool) (relationEquiv q).symm

end IndependentSetsGames.Foundations.PCP.AlphabetTable.ReadRelation

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Ambient
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup
open Turing
open IndependentSetsGames.Foundations.Complexity
open GenericGraphTables
variable {K Λ σ : Type} [DecidableEq K]

def headIndex {q : Nat} (table : Table q) (e : Fin table.darts) : Fin table.darts :=
  table.rows[e].reverseIndex

def headValue {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  table.rows[headIndex table e].tail.val

theorem headValue_eq_semantics {q : Nat} (table : Table q) (e : Fin table.darts) :
    headValue table e = ((semantics table).head e).val := rfl

abbrev HeadTapes (K : Type) := Fin 6 → K

def headLookupTapes {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) : K → List Bool :=
  MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
    (encodeWord 0 ++ base (tape 3))
    (encodeWord table.rows[headIndex table e].reverseIndex.val ++
      (encodeWords (relationWords table.rows[headIndex table e].relation) ++
        (rowsBits ((rowList table).drop ((headIndex table e).val + 1)) ++ base (tape 2))))
    (encodeWord (headValue table e))

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_Emitter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open IndependentSetsGames.Foundations.Complexity

inductive Command (h : Nat) (σ : Type) (bound : Nat)
  | literal (word : List Bool)
  | bit (value : σ → Bool)
  | bounded (value : σ → Fin bound)
  | scaled (source : Fin h) (coefficient : Nat)
  | scaledIf (source : Fin h) (coefficient : Nat) (active : σ → Bool)

def commandBits {h bound : Nat} {σ : Type} (values : Fin h → Nat) (ambient : σ) :
    Command h σ bound → List Bool
  | .literal word => word
  | .bit value => encodeWord (if value ambient then 1 else 0)
  | .bounded value => List.replicate (value ambient).val true
  | .scaled source coefficient => List.replicate (coefficient * values source) true
  | .scaledIf source coefficient active =>
      List.replicate ((if active ambient then coefficient else 0) * values source) true

def commandSteps {h bound : Nat} {σ : Type} (values : Fin h → Nat) :
    Command h σ bound → Nat
  | .literal _ | .bit _ => 1
  | .bounded _ => 2
  | .scaled source _ => 3 * (values source + 1) + 2
  | .scaledIf source _ _ => 3 * (values source + 1) + 3

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

def affineCommands (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    List (Command h σ bound) :=
  terms.map (fun term => .scaled term.1 term.2) ++ [.bounded offset, .literal [false]]

@[simp] theorem affineCommands_length (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    (affineCommands terms offset).length = terms.length + 2 := by
  simp [affineCommands]

def Command.mapAmbient {τ : Type} (view : σ → τ) :
    Command h τ bound → Command h σ bound
  | .literal word => .literal word
  | .bit value => .bit (value ∘ view)
  | .bounded value => .bounded (value ∘ view)
  | .scaled source coefficient => .scaled source coefficient
  | .scaledIf source coefficient active => .scaledIf source coefficient (active ∘ view)

@[simp] theorem commandBits_mapAmbient {τ : Type} (view : σ → τ)
    (command : Command h τ bound) (values : Fin h → Nat) (ambient : σ) :
    commandBits values ambient (command.mapAmbient view) =
      commandBits values (view ambient) command := by
  cases command <;> rfl

@[simp] theorem commandSteps_mapAmbient {τ : Type} (view : σ → τ)
    (command : Command h τ bound) (values : Fin h → Nat) :
    commandSteps values (command.mapAmbient view) = commandSteps values command := by
  cases command <;> rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Emitter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_AmbientRelation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine
open Turing
open PCP

namespace Program

open PCP.AlphabetTable

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

abbrev Ambient := Unit × Buffer 4096
abbrev Plan := List (Emitter.Command 5 Ambient 36864)

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

end Program

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_FinalCNFHeader
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

def headerFrame (input archive vertices darts rowIndex tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .archive => archive
  | .vertices => vertices
  | .darts => darts
  | .rowIndex => rowIndex
  | .tail => tail
  | .head => head
  | .accumulator => accumulator
  | _ => []

def headerResultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  headerFrame rowsBits (encodeWords [n, m] ++ rowsBits)
    (encodeWord n) (encodeWord m) (encodeWord 0) [] []
    (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse

@[simp] theorem headerResultTapes_input (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .input = rowsBits := rfl

@[simp] theorem headerResultTapes_archive (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .archive = encodeWords [n, m] ++ rowsBits := rfl

@[simp] theorem headerResultTapes_accumulator (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .accumulator =
      (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse := rfl

@[simp] theorem headerResultTapes_rowIndex (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .rowIndex = encodeWord 0 := rfl

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_FinalCNFRowTrace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

def endpointTapes (base : Tape → List Bool) (tail reverse : Nat) (rest : List Bool) :=
  Hastad.SourceMachine.fieldTapes Tape.input Tape.reverseIndex
    (Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
      (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail))
    rest (encodeWord reverse ++ base .reverseIndex)

def finishTapes (base : Tape → List Bool) (row : Nat) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update base Tape.tail []) Tape.head [])
      Tape.reverseIndex []) Tape.rowIndex (encodeWord (row + 1))

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_FinalCNFTableAdapter
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFTableAdapter

open PCP

def genericRow {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.DartRow 64 n m :=
  ⟨row.tail, row.reverseIndex, row.relation⟩

@[simp] theorem genericRow_tail {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).tail = row.tail := rfl

@[simp] theorem genericRow_reverseIndex {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).reverseIndex = row.reverseIndex := rfl

@[simp] theorem genericRow_relation {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).relation = row.relation := rfl

def genericRows {n m : Nat} (rows : GraphTables.Rows n m) :
    GenericGraphTables.Rows 64 n m := rows.map genericRow

@[simp] theorem genericRows_get {n m : Nat} (rows : GraphTables.Rows n m) (e : Fin m) :
    (genericRows rows)[e] = genericRow rows[e] := by
  simp [genericRows]

@[simp] theorem genericRows_reverseAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) :
    GenericGraphTables.reverseAt (genericRows rows) e = GraphTables.reverseAt rows e := by
  change (genericRows rows)[e].reverseIndex = rows[e].reverseIndex
  rw [genericRows_get]
  rfl

@[simp] theorem genericRows_acceptsAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) (a b : Fin 64) :
    GenericGraphTables.acceptsAt (genericRows rows) e a b =
      GraphTables.acceptsAt rows e a b := by
  simp only [GenericGraphTables.acceptsAt, genericRows_get, genericRow_relation]
  rfl

theorem genericRows_valid {n m : Nat} (rows : GraphTables.Rows n m)
    (valid : GraphTables.Valid rows) : GenericGraphTables.Valid (genericRows rows) := by
  constructor
  · intro e
    simpa only [genericRows_reverseAt] using valid.1 e
  · intro e a b
    simpa only [genericRows_reverseAt, genericRows_acceptsAt] using valid.2 e a b

def genericTable (table : GraphTables.Table) : GenericGraphTables.Table 64 where
  vertices := table.vertices
  darts := table.darts
  rows := genericRows table.rows
  valid := genericRows_valid table.rows table.valid

@[simp] theorem genericTable_vertices (table : GraphTables.Table) :
    (genericTable table).vertices = table.vertices := rfl

@[simp] theorem genericTable_darts (table : GraphTables.Table) :
    (genericTable table).darts = table.darts := rfl

@[simp] theorem genericTable_row (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e] = genericRow table.rows[e] := genericRows_get _ _

@[simp] theorem genericTable_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].tail = table.rows[e].tail := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_reverseIndex (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].reverseIndex = table.rows[e].reverseIndex := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_relation (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].relation = table.rows[e].relation := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericRow_words {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.rowWords (genericRow row) = GraphTables.rowWords row := rfl

theorem genericTable_rowList (table : GraphTables.Table) :
    GenericGraphTables.rowList (genericTable table) =
      (GraphTables.rowList table).map genericRow := by
  simp only [GenericGraphTables.rowList, GraphTables.rowList, genericTable,
    genericRows, Vector.toList_map]

@[simp] theorem genericTable_tableWords (table : GraphTables.Table) :
    GenericGraphTables.tableWords (genericTable table) = GraphTables.tableWords table := by
  simp only [GenericGraphTables.tableWords, GraphTables.tableWords,
    genericTable_vertices, genericTable_darts, genericTable_rowList, List.flatMap_map,
    genericRow_words]

@[simp] theorem genericTable_tableBits (table : GraphTables.Table) :
    GenericGraphTables.tableBits (genericTable table) = GraphTables.tableBits table := by
  simp only [GenericGraphTables.tableBits, GraphTables.tableBits, genericTable_tableWords]

@[simp] theorem genericTable_semantics_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).tail e =
      (GraphTables.semantics table).tail e := genericTable_tail table e

@[simp] theorem genericTable_semantics_reverse (table : GraphTables.Table)
    (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).reverse e =
      (GraphTables.semantics table).reverse e := genericTable_reverseIndex table e

@[simp] theorem genericTable_semantics_head (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).head e =
      (GraphTables.semantics table).head e := by
  exact (genericTable_semantics_tail table _).trans
    (congrArg (GraphTables.semantics table).tail (genericTable_semantics_reverse table e))

@[simp] theorem genericTable_semantics_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (a b : Fin 64) :
    (GenericGraphTables.semantics (genericTable table)).accepts e a b =
      (GraphTables.semantics table).accepts e a b := genericRows_acceptsAt _ _ _ _

@[simp] theorem genericTable_headIndex (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headIndex (genericTable table) e = table.rows[e].reverseIndex :=
  genericTable_reverseIndex table e

@[simp] theorem genericTable_headValue (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headValue (genericTable table) e =
      ((GraphTables.semantics table).head e).val := by
  exact (AlphabetTable.Lookup.headValue_eq_semantics (genericTable table) e).trans
    (congrArg Fin.val (genericTable_semantics_head table e))

end IndependentSetsGames.Foundations.Complexity.FinalCNFTableAdapter

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_FinalCNFRow
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

@[simp] theorem headRoles_zero : headRoles 0 = Tape.archive := rfl
@[simp] theorem headRoles_one : headRoles 1 = Tape.reverseIndex := rfl
@[simp] theorem headRoles_two : headRoles 2 = Tape.scanWork := rfl
@[simp] theorem headRoles_three : headRoles 3 = Tape.indexWork := rfl
@[simp] theorem headRoles_four : headRoles 4 = Tape.head := rfl
@[simp] theorem headRoles_five : headRoles 5 = Tape.scratch := rfl

def rowOperands (table : GraphTables.Table) (e : Fin table.darts) : Fin 5 → Nat :=
  values table.vertices table.darts table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val e.val

def rowRelation (table : GraphTables.Table) (e : Fin table.darts) : Ambient :=
  ((), fun i => table.rows[e].relation[i])

def rowRest (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) : List Bool :=
  encodeWords (GraphTables.relationWords table.rows[e].relation) ++ rest

def preparedTapes (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headRoles
    (endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
      (rowRest table e rest)) (genericTable table) e

def emittedTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Function.update (Function.update (preparedTapes base table e rest) Tape.input rest)
    Tape.accumulator ((plan.flatMap (Emitter.commandBits (rowOperands table e)
      (rowRelation table e))).reverse ++ base .accumulator)

def rowResultTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  finishTapes (emittedTapes plan base table e rest) e.val

@[simp] theorem rowResult_input (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .input = rest := by
  simp [rowResultTapes, finishTapes, emittedTapes]

@[simp] theorem rowResult_tail (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .tail = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_head (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .head = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_reverse (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .reverseIndex = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_index (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .rowIndex = encodeWord (e.val + 1) := by
  simp [rowResultTapes, finishTapes]

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineLookupSpec
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineLookupSpec

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

end IndependentSetsGames.Foundations.Complexity.MachineLookupSpec

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineWord
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineWord

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Tape (t : Nat) := Fin 6 ⊕ Fin (t + 1)

def first (t : Nat) : Fin (t + 1) := ⟨0, by omega⟩

end IndependentSetsGames.Foundations.Complexity.PoweringMachineWord

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineTapes
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineTapes

abbrev Tape (max : Nat) := Fin 11 ⊕ Fin max

def table (max : Nat) : Tape max := .inl 0
def start (max : Nat) : Tape max := .inl 1
def query (max : Nat) : Tape max := .inl 2
def scan (max : Nat) : Tape max := .inl 3
def reverse (max : Nat) : Tape max := .inl 4
def scratch (max : Nat) : Tape max := .inl 5
def leftEndpoint (max : Nat) : Tape max := .inl 6
def rightEndpoint (max : Nat) : Tape max := .inl 7
def leftCopy (max : Nat) : Tape max := .inl 8
def rightCopy (max : Nat) : Tape max := .inl 9
def rowOutput (max : Nat) : Tape max := .inl 10

def endpoint (max : Nat) (target : Bool) : Tape max :=
  if target then rightEndpoint max else leftEndpoint max

@[simp] theorem endpoint_false (max : Nat) : endpoint max false = leftEndpoint max := rfl
@[simp] theorem endpoint_true (max : Nat) : endpoint max true = rightEndpoint max := rfl

def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

def trajectoryPlacement {t max : Nat} (h : t ≤ max) : Fin (t + 1) → Tape max :=
  Fin.cases (start max) (fun i => .inr (Fin.castLE h i))

def wordPlacement {t max : Nat} (h : t ≤ max) (target : Bool) :
    PoweringMachineWord.Tape t → Tape max
  | .inl i => .inl (wordSharedRole target i)
  | .inr i => trajectoryPlacement h i

@[simp] theorem wordPlacement_inl_zero {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 0) = table max := rfl
@[simp] theorem wordPlacement_inl_one {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 1) = query max := rfl
@[simp] theorem wordPlacement_inl_two {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 2) = scan max := rfl
@[simp] theorem wordPlacement_inl_three {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 3) = reverse max := rfl
@[simp] theorem wordPlacement_inl_four {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 4) = scratch max := rfl
@[simp] theorem wordPlacement_inl_five {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 5) = endpoint max target := by cases target <;> rfl
@[simp] theorem wordPlacement_first {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inr (PoweringMachineWord.first t)) = start max := rfl
@[simp] theorem wordPlacement_succ {t max : Nat} (h : t ≤ max) (target : Bool) (i : Fin t) :
    wordPlacement h target (.inr i.succ) = .inr (Fin.castLE h i) := rfl

def relationPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 2 else
    if i = 3 then 3 else if i = 4 then 10 else 5)

@[simp] theorem relationPlacement_zero (max : Nat) : relationPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem relationPlacement_one (max : Nat) : relationPlacement max 1 = table max := rfl
@[simp] theorem relationPlacement_two (max : Nat) : relationPlacement max 2 = query max := rfl
@[simp] theorem relationPlacement_three (max : Nat) : relationPlacement max 3 = scan max := rfl
@[simp] theorem relationPlacement_four (max : Nat) : relationPlacement max 4 = rowOutput max := rfl
@[simp] theorem relationPlacement_five (max : Nat) : relationPlacement max 5 = scratch max := rfl

def equalityPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else
    if i = 3 then 9 else if i = 4 then 5 else 10)

@[simp] theorem equalityPlacement_zero (max : Nat) : equalityPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem equalityPlacement_one (max : Nat) : equalityPlacement max 1 = rightEndpoint max := rfl
@[simp] theorem equalityPlacement_two (max : Nat) : equalityPlacement max 2 = leftCopy max := rfl
@[simp] theorem equalityPlacement_three (max : Nat) : equalityPlacement max 3 = rightCopy max := rfl
@[simp] theorem equalityPlacement_four (max : Nat) : equalityPlacement max 4 = scratch max := rfl
@[simp] theorem equalityPlacement_five (max : Nat) : equalityPlacement max 5 = rowOutput max := rfl

end IndependentSetsGames.Foundations.Complexity.PoweringMachineTapes

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineLoop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

def scanTapes (B remaining processed : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord remaining ++ suffix
  | .counter => encodeWord processed
  | .vertices => encodeWord processed
  | .darts => encodeWord (B * processed)

def finalTapes (B n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => suffix
  | .counter => encodeWord n
  | .vertices => encodeWord n
  | .darts => encodeWord (B * n)

end IndependentSetsGames.Foundations.Complexity.PoweringMachineLoop

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_PoweringMachineInitialize
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop

abbrev ExtraTape (max : Nat) := PoweringMachineTapes.Tape max ⊕ Unit
abbrev GlobalTape (max : Nat) := HeaderTape ⊕ ExtraTape max

def commonPlacement (max : Nat) (tape : PoweringMachineTapes.Tape max) : GlobalTape max :=
  if tape = PoweringMachineTapes.start max then .inl .counter else .inr (.inl tape)

@[simp] theorem commonPlacement_start (max : Nat) :
    commonPlacement max (PoweringMachineTapes.start max) = .inl .counter := by
  simp [commonPlacement]

@[simp] theorem commonPlacement_table (max : Nat) :
    commonPlacement max (PoweringMachineTapes.table max) =
      .inr (.inl (PoweringMachineTapes.table max)) := by
  simp [commonPlacement, PoweringMachineTapes.table, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_scratch (max : Nat) :
    commonPlacement max (PoweringMachineTapes.scratch max) =
      .inr (.inl (PoweringMachineTapes.scratch max)) := by
  simp [commonPlacement, PoweringMachineTapes.scratch, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_rowOutput (max : Nat) :
    commonPlacement max (PoweringMachineTapes.rowOutput max) =
      .inr (.inl (PoweringMachineTapes.rowOutput max)) := by
  simp [commonPlacement, PoweringMachineTapes.rowOutput, PoweringMachineTapes.start]

def mergeTapes {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) : GlobalTape max → List Bool
  | .inl k => header k
  | .inr e => extra e

@[simp] theorem final_counter (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra
      (commonPlacement max (PoweringMachineTapes.start max)) = encodeWord vertices := by
  simp [mergeTapes, finalTapes]

@[simp] theorem final_vertices (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .vertices) = encodeWord vertices := rfl

@[simp] theorem final_darts (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .darts) = encodeWord (B * vertices) := rfl

end IndependentSetsGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_MachineDrainMany
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineDrainMany

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev LocalLabel (_ : K) := Unit

end IndependentSetsGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_TableIterationFiniteAlphabet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine
open Turing

inductive Tape (R : Type) where
  | input | backup | output | reg (r : R)
  deriving DecidableEq, Fintype

inductive Instruction (R L : Type) where
  | inc (r : R) (next : L)
  | dec (r : R) (positive zero : L)
  | test (r : R) (zero positive : L)
  | read (one zero empty : L)
  | back (nonempty empty : L)
  | write (b : Bool) (next : L)
  | discard (next : L)
  | jump (next : L)
  | halt

structure Data (R : Type) where
  reg : R → ℕ
  input : List Bool
  backup : List Bool
  output : List Bool

structure Configuration (R L : Type) extends Data R where
  label : Option L

variable {R L : Type} [DecidableEq R]

def Instruction.execute (i : Instruction R L) (d : Data R) : Configuration R L :=
  match i with
  | .inc r next => ⟨{ d with reg := Function.update d.reg r (d.reg r + 1) }, some next⟩
  | .dec r positive zero =>
    ⟨{ d with reg := Function.update d.reg r (d.reg r - 1) },
      some (if d.reg r = 0 then zero else positive)⟩
  | .test r zero positive => ⟨d, some (if d.reg r = 0 then zero else positive)⟩
  | .read one zero empty =>
    ⟨{ d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }, some (match d.input with
      | [] => empty | true :: _ => one | false :: _ => zero)⟩
  | .back nonempty empty =>
    ⟨{ d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail },
      some (if d.backup = [] then empty else nonempty)⟩
  | .write b next => ⟨{ d with output := b :: d.output }, some next⟩
  | .discard next => ⟨{d with input := d.input.tail}, some next⟩
  | .jump next => ⟨d, some next⟩
  | .halt => ⟨d, none⟩

def step (p : L → Instruction R L) (c : Configuration R L) : Option (Configuration R L) :=
  c.label.map (fun l => (p l).execute c.toData)

def tapes (d : Data R) : Tape R → List Bool
  | .input => d.input
  | .backup => d.backup
  | .output => d.output
  | .reg r => List.replicate (d.reg r) true

def embed (c : Configuration R L) : TM2.Cfg (fun _ : Tape R => Bool) L (Option Bool) :=
  ⟨c.label, none, tapes c.toData⟩

def goto (l : L) : TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))

def Instruction.code : Instruction R L → TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool)
  | .inc r next => .push (.reg r) (fun _ => true) (goto next)
  | .dec r positive zero => .pop (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .test r zero positive => .peek (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .read one zero empty => .pop .input (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .backup (fun b => b.getD false)
          (.branch (fun b => b.getD false) (goto one) (goto zero))) (goto empty))
  | .back nonempty empty => .pop .backup (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .input (fun b => b.getD false) (goto nonempty)) (goto empty))
  | .write b next => .push .output (fun _ => b) (goto next)
  | .discard next => .pop .input (fun _ _ => none) (goto next)
  | .jump next => goto next
  | .halt => .halt

 theorem tapes_inc (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r + 1) } =
      Function.update (tapes d) (.reg r) (true :: tapes d (.reg r)) := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h, List.replicate_succ]

 theorem tapes_dec (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r - 1) } =
      Function.update (tapes d) (.reg r) (tapes d (.reg r)).tail := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h]

 theorem tapes_read (d : Data R) :
    tapes { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup } =
      Function.update (Function.update (tapes d) .input d.input.tail) .backup
        (d.input.take 1 ++ d.backup) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_back (d : Data R) :
    tapes { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail } =
      Function.update (Function.update (tapes d) .backup d.backup.tail) .input
        (d.backup.take 1 ++ d.input) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_write (d : Data R) (b : Bool) :
    tapes { d with output := b :: d.output } =
      Function.update (tapes d) .output (b :: d.output) := by
  funext k; cases k <;> simp [tapes]

 theorem instruction_simulation (i : Instruction R L) (d : Data R) :
    TM2.stepAux i.code none (tapes d) = embed (i.execute d) := by
  cases i with
  | inc r next => simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_inc]
  | dec r pos zero =>
    cases h : d.reg r with
    | zero =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      simpa [h, tapes] using (tapes_dec d r).symm
    | succ n =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed,
        tapes, h, List.replicate_succ]
      simpa [h, tapes] using (tapes_dec d r).symm
  | test r zero pos =>
    cases h : d.reg r <;>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h, List.replicate_succ]
  | read one zero empty =>
    cases h : d.input with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_read d).symm
  | back nonempty empty =>
    cases h : d.backup with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_back d).symm
  | write b next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_write, tapes]
  | discard next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed]
    funext k; cases k <;> simp [tapes]
  | jump next => rfl
  | halt => rfl

 theorem step_simulation (p : L → Instruction R L) (c : Configuration R L) :
    TM2.step (fun l => (p l).code) (embed c) = (step p c).map embed := by
  cases c with
  | mk d l =>
    cases l with
    | none => rfl
    | some l => simpa [TM2.step, step, embed] using congrArg some (instruction_simulation (p l) d)

def machine [Fintype R] [Fintype L] (p : L → Instruction R L) (main : L) : FinTM2 where
  K := Tape R
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := L
  main := main
  σ := Option Bool
  initialState := none
  m l := (p l).code

end IndependentSetsCut.CounterMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Command
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine
variable {R L : Type} [DecidableEq R]

inductive Command (R : Type) where
  | skip
  | inc (r : R)
  | dec (r : R)
  | write (b : Bool)
  | discard
  | rewind
  | seq (first second : Command R)
  | test (r : R) (zero positive : Command R)
  | read (one zero empty : Command R)
  | loop (r : R) (body : Command R)

namespace Command

def Label : Command R → Type
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => Unit
  | .seq a b => Label a ⊕ Label b
  | .test _ a b => Unit ⊕ Label a ⊕ Label b
  | .read a b c => Unit ⊕ Label a ⊕ Label b ⊕ Label c
  | .loop _ b => Unit ⊕ Label b

noncomputable instance labelFintype (c : Command R) : Fintype (Label c) := by
  induction c with
  | skip | inc | dec | write | discard | rewind => exact inferInstanceAs (Fintype Unit)
  | seq a b ia ib => exact inferInstanceAs (Fintype (Label a ⊕ Label b))
  | test r a b ia ib => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b))
  | read a b c ia ib ic => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b ⊕ Label c))
  | loop r b ib => exact inferInstanceAs (Fintype (Unit ⊕ Label b))

def entry : (c : Command R) → Label c
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => ()
  | .seq a _ => .inl a.entry
  | .test _ _ _ | .read _ _ _ | .loop _ _ => .inl ()

def code : (c : Command R) → (Label c → L) → L → Label c → Instruction R L
  | .skip, _, exit, _ => .jump exit
  | .inc r, _, exit, _ => .inc r exit
  | .dec r, _, exit, _ => .dec r exit exit
  | .write b, _, exit, _ => .write b exit
  | .discard, _, exit, _ => .discard exit
  | .rewind, labels, exit, _ => .back (labels ()) exit
  | .seq a b, labels, _exit, .inl l =>
      a.code (fun l => labels (.inl l)) (labels (.inr b.entry)) l
  | .seq _a b, labels, exit, .inr l => b.code (fun l => labels (.inr l)) exit l
  | .test r a b, labels, _, .inl _ =>
      .test r (labels (.inr (.inl a.entry))) (labels (.inr (.inr b.entry)))
  | .test _ a _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .test _ _ b, labels, exit, .inr (.inr l) =>
      b.code (fun l => labels (.inr (.inr l))) exit l
  | .read a b c, labels, _, .inl _ =>
      .read (labels (.inr (.inl a.entry))) (labels (.inr (.inr (.inl b.entry))))
        (labels (.inr (.inr (.inr c.entry))))
  | .read a _ _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .read _ b _, labels, exit, .inr (.inr (.inl l)) =>
      b.code (fun l => labels (.inr (.inr (.inl l)))) exit l
  | .read _ _ c, labels, exit, .inr (.inr (.inr l)) =>
      c.code (fun l => labels (.inr (.inr (.inr l)))) exit l
  | .loop r b, labels, exit, .inl _ => .dec r (labels (.inr b.entry)) exit
  | .loop _ b, labels, _, .inr l => b.code (fun l => labels (.inr l)) (labels (.inl ())) l

def incData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r + 1) }
def decData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r - 1) }
def readData (d : Data R) : Data R :=
  { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }
def backData (d : Data R) : Data R :=
  { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail }
def discardData (d : Data R) : Data R := {d with input := d.input.tail}
def writeData (d : Data R) (b : Bool) : Data R := { d with output := b :: d.output }

inductive Evaluates : Command R → Data R → Data R → ℕ → Prop
  | skip (d) : Evaluates .skip d d 1
  | inc (d r) : Evaluates (.inc r) d (incData d r) 1
  | dec (d r) : Evaluates (.dec r) d (decData d r) 1
  | write (d b) : Evaluates (.write b) d (writeData d b) 1
  | discard (d) : Evaluates .discard d (discardData d) 1
  | rewind_empty {d} : d.backup = [] → Evaluates .rewind d d 1
  | rewind_cons {d e n b rest} : d.backup = b :: rest →
      Evaluates .rewind (backData d) e n → Evaluates .rewind d e (1 + n)
  | seq {a b d e f n m} : Evaluates a d e n → Evaluates b e f m →
      Evaluates (.seq a b) d f (n + m)
  | test_zero {r a b d e n} : d.reg r = 0 → Evaluates a d e n →
      Evaluates (.test r a b) d e (1 + n)
  | test_pos {r a b d e n} : d.reg r ≠ 0 → Evaluates b d e n →
      Evaluates (.test r a b) d e (1 + n)
  | read_one {a b c d e n rest} : d.input = true :: rest →
      Evaluates a (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_zero {a b c d e n rest} : d.input = false :: rest →
      Evaluates b (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_empty {a b c d e n} : d.input = [] →
      Evaluates c (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | loop_zero {r b d} : d.reg r = 0 → Evaluates (.loop r b) d d 1
  | loop_pos {r b d e f n m} : d.reg r ≠ 0 →
      Evaluates b (decData d r) e n → Evaluates (.loop r b) e f m →
      Evaluates (.loop r b) d f (1 + n + m)

end Command

def advance (p : L → Instruction R L) : Option (Configuration R L) → Option (Configuration R L) :=
  fun c => c.bind (step p)

def atCfg (l : L) (d : Data R) : Option (Configuration R L) := some ⟨d, some l⟩

def Runs (p : L → Instruction R L) (n : ℕ) (l : L) (d : Data R) (l' : L) (d' : Data R) : Prop :=
  (advance p)^[n] (atCfg l d) = atCfg l' d'

 theorem runs_one (p : L → Instruction R L) (l : L) (d : Data R) (l' : L) (d' : Data R)
    (h : (p l).execute d = ⟨d', some l'⟩) : Runs p 1 l d l' d' := by
  simpa [Runs, advance, atCfg, step] using congrArg some h

 theorem Runs.trans {p : L → Instruction R L} {n m : ℕ} {l l' l'' : L} {d e f : Data R}
    (h : Runs p n l d l' e) (h' : Runs p m l' e l'' f) : Runs p (n + m) l d l'' f := by
  unfold Runs at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h, h']

namespace Command
 theorem trace {c : Command R} {d d' : Data R} {n : ℕ} (h : Evaluates c d d' n)
    (p : L → Instruction R L) (labels : c.Label → L) (exit : L)
    (atLabels : ∀ l, p (labels l) = c.code labels exit l) :
    Runs p n (labels c.entry) d exit d' := by
  induction h generalizing L with
  | skip d =>
    apply runs_one
    rw [atLabels]; rfl
  | inc d r =>
    apply runs_one
    rw [atLabels]; rfl
  | dec d r =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, decData]
  | write d b =>
    apply runs_one
    rw [atLabels]; rfl
  | discard d =>
    apply runs_one
    rw [atLabels]; rfl
  | @rewind_empty d hd =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, hd]
    cases d; simp_all
  | @rewind_cons d e n b rest hd he ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, backData, hd]
  | @seq a b d e f n m h h' ih ih' =>
    exact Runs.trans
      (ih p (fun l => labels (.inl l)) (labels (.inr b.entry)) (fun l => atLabels (.inl l)))
      (ih' p (fun l => labels (.inr l)) exit (fun l => atLabels (.inr l)))
  | @test_zero r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @test_pos r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @read_one a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_zero a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inl l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_empty a b c d e n hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inr l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @loop_zero r b d hr =>
    apply runs_one
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
    rw [← hr, Function.update_eq_self]
  | @loop_pos r b d e f n m hr h h' ih ih' =>
    refine Runs.trans (Runs.trans (runs_one p _ _ _ _ ?_)
      (ih p (fun l => labels (.inr l)) (labels (.inl ())) (fun l => atLabels (.inr l))))
        (ih' p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, decData, hr]
end Command
end IndependentSetsCut.CounterMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_FinalLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine

section
open Turing
variable {R L : Type} [DecidableEq R]

 theorem advance_simulation (p : L → Instruction R L) (a : Option (Configuration R L)) :
    (a.map embed).bind (TM2.step (fun l => (p l).code)) = (advance p a).map embed := by
  cases a with
  | none => rfl
  | some c => exact step_simulation p c

 theorem iterate_simulation (p : L → Instruction R L) (n : ℕ)
    (a : Option (Configuration R L)) :
    (fun a => a.bind (TM2.step (fun l => (p l).code)))^[n] (a.map embed) =
      ((advance p)^[n] a).map embed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, advance_simulation, Function.iterate_succ_apply']

namespace Command

abbrev FinalLabel (c : Command R) := c.Label ⊕ Unit

def finalCode (c : Command R) : c.FinalLabel → Instruction R c.FinalLabel
  | .inl l => c.code Sum.inl (.inr ()) l
  | .inr _ => .halt

def initial (input : List Bool) : Data R :=
  ⟨fun _ => 0, input, [], []⟩

noncomputable def finiteMachine [Fintype R] (c : Command R) : FinTM2 :=
  machine c.finalCode (.inl c.entry)

 theorem finiteMachine_initial [Fintype R] (c : Command R) (input : List Bool) :
    initList c.finiteMachine input = embed ⟨initial input, some (.inl c.entry)⟩ := by
  unfold initList
  congr 1
  funext k
  cases k <;> simp [finiteMachine, machine, tapes, initial]
  rfl

 noncomputable def machine_run [Fintype R] {c : Command R} {input : List Bool} {out : Data R} {n : ℕ}
    (h : Evaluates c (initial input) out n) :
    StateTransition.EvalsToInTime c.finiteMachine.step (initList c.finiteMachine input)
      (some (embed ⟨out, none⟩)) (n + 1) := by
  have hr := trace h c.finalCode Sum.inl (.inr ()) (fun _ => rfl)
  have hi := iterate_simulation c.finalCode n (atCfg (.inl c.entry) (initial input))
  have hit : (fun a : Option (Configuration R c.FinalLabel) => advance c.finalCode a)^[n + 1]
      (atCfg (.inl c.entry) (initial input)) = some ⟨out, none⟩ := by
    rw [Function.iterate_succ_apply', hr]
    rfl
  refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
  rw [finiteMachine_initial]
  change (fun a => a.bind (TM2.step (fun l => (c.finalCode l).code)))^[n + 1]
      ((atCfg (.inl c.entry) (initial input)).map embed) = _
  rw [iterate_simulation, hit]
  rfl

end Command
end

open scoped BigOperators
variable {R : Type} [DecidableEq R]

namespace Data

def set (d : Data R) (r : R) (v : ℕ) : Data R :=
  { d with reg := Function.update d.reg r v }

@[simp] theorem set_self (d : Data R) (r : R) : d.set r (d.reg r) = d := by
  simp [set]

@[simp] theorem set_set (d : Data R) (r : R) (v w : ℕ) :
    (d.set r v).set r w = d.set r w := by simp [set]

@[simp] theorem set_reg_same (d : Data R) (r : R) (v : ℕ) :
    (d.set r v).reg r = v := by simp [set]

@[simp] theorem set_reg_ne (d : Data R) (r s : R) (v : ℕ) (h : s ≠ r) :
    (d.set r v).reg s = d.reg s := by simp [set, h]

 theorem set_comm (d : Data R) (r s : R) (v w : ℕ) (h : r ≠ s) :
    (d.set r v).set s w = (d.set s w).set r v := by
  simp only [set]
  congr 1
  exact Function.update_comm h v w d.reg

end Data

namespace Command

def clear (r : R) : Command R := .loop r .skip

def move (r s : R) : Command R := .loop r (.inc s)

 theorem clear_evaluates (d : Data R) (r : R) :
    Evaluates (clear r) d (d.set r 0) (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hs : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [clear, hs] using (Evaluates.loop_zero (b := .skip) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    have hd : (decData d r).reg r = n := by simp [decData, hn]
    have he := ih (decData d r) hd
    have hf : (decData d r).set r 0 = d.set r 0 := by simp [decData, Data.set]
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [clear, hf, ht] using
      (Evaluates.loop_pos hr (Evaluates.skip (decData d r)) he)

 theorem move_evaluates (d : Data R) (r s : R) (hrs : r ≠ s) :
    Evaluates (move r s) d ((d.set r 0).set s (d.reg s + d.reg r))
      (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hz : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [move, hz] using (Evaluates.loop_zero (b := .inc s) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    let e := incData (decData d r) s
    have er : e.reg r = n := by simp [e, incData, decData, hrs, hn]
    have es : e.reg s = d.reg s + 1 := by simp [e, incData, decData, Ne.symm hrs]
    have he := ih e er
    have hf : (e.set r 0).set s (e.reg s + n) =
        (d.set r 0).set s (d.reg s + (n + 1)) := by
      simp only [es]
      have hc : e.set r 0 = (d.set r 0).set s (d.reg s + 1) := by
        dsimp [e, incData, decData, Data.set]
        congr 1
        ext t
        by_cases ht : t = r <;> by_cases hs : t = s <;> simp_all
      rw [hc, Data.set_set]
      congr 1
      omega
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [move, hf, ht] using (Evaluates.loop_pos hr (Evaluates.inc (decData d r) s) he)

def Within (c : Command R) (d e : Data R) (B : ℕ) : Prop :=
  ∃ n ≤ B, Evaluates c d e n

 theorem Within.seq {a b : Command R} {d e f : Data R} {B C : ℕ}
    (h : Within a d e B) (h' : Within b e f C) : Within (.seq a b) d f (B + C) := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨m, hm, hf⟩ := h'
  exact ⟨n + m, Nat.add_le_add hn hm, Evaluates.seq he hf⟩

 theorem Within.mono {c : Command R} {d e : Data R} {B C : ℕ}
    (h : Within c d e B) (hBC : B ≤ C) : Within c d e C := by
  obtain ⟨n, hn, he⟩ := h
  exact ⟨n, hn.trans hBC, he⟩

end Command
end IndependentSetsCut.CounterMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Copy
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine

section
open scoped BigOperators
variable {R : Type} [DecidableEq R]

omit [DecidableEq R] in
@[ext] theorem Data.ext {d e : Data R} (hr : d.reg = e.reg)
    (hi : d.input = e.input) (hb : d.backup = e.backup) (ho : d.output = e.output) : d = e := by
  cases d; cases e; simp_all

namespace Command

theorem Within.loop (r : R) (b : Command R) (state : ℕ → Data R) (n B : ℕ)
    (hr : ∀ i ≤ n, (state i).reg r = i)
    (hb : ∀ i < n, Within b (decData (state (i+1)) r) (state i) B) :
    Within (.loop r b) (state n) (state 0) (n * (B + 1) + 1) := by
  induction n with
  | zero => exact ⟨1, by omega, Evaluates.loop_zero (hr 0 le_rfl)⟩
  | succ n ih =>
    obtain ⟨a, ha, ea⟩ := hb n (by omega)
    obtain ⟨b', hb', eb⟩ := ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))
    refine ⟨1 + a + b', ?_, Evaluates.loop_pos (by rw [hr (n+1) le_rfl]; omega) ea eb⟩
    nlinarith

 theorem Within.inc (d : Data R) (r : R) : Within (.inc r) d (incData d r) 1 :=
  ⟨1, le_rfl, Evaluates.inc d r⟩
 theorem Within.dec (d : Data R) (r : R) : Within (.dec r) d (decData d r) 1 :=
  ⟨1, le_rfl, Evaluates.dec d r⟩
 theorem Within.skip (d : Data R) : Within (.skip : Command R) d d 1 :=
  ⟨1, le_rfl, Evaluates.skip d⟩
 theorem Within.clear (d : Data R) (r : R) :
    Within (clear r) d (d.set r 0) (2*d.reg r+1) :=
  ⟨_, le_rfl, clear_evaluates d r⟩
 theorem Within.move (d : Data R) (r s : R) (h : r ≠ s) :
    Within (move r s) d ((d.set r 0).set s (d.reg s+d.reg r)) (2*d.reg r+1) :=
  ⟨_, le_rfl, move_evaluates d r s h⟩

def copy (r s t : R) : Command R :=
  .seq (.loop r (.seq (.inc s) (.inc t))) (move t r)

 theorem copy_evaluates (d : Data R) (r s t : R)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (copy r s t) d (d.set s (d.reg s + d.reg r)) (5*d.reg r+2) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => ((d.set r i).set s (d.reg s+n-i)).set t (n-i)
  have hn : state n = d := by
    ext u <;> simp [state, Data.set, n]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;> simp_all
  have hloop : Within (.loop r (.seq (.inc s) (.inc t))) (state n) (state 0) (n*3+1) := by
    apply Within.loop r _ state n 2
    · intro i hi; simp [state, Data.set, hrs, hrt]
    · intro i hi
      have he := (Within.inc (decData (state (i+1)) r) s).seq
        (Within.inc (incData (decData (state (i+1)) r) s) t)
      have hout : incData (incData (decData (state (i+1)) r) s) t = state i := by
        ext u <;> simp only [incData, decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
          simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst] <;> omega
      simpa only [hout] using he
  rw [hn] at hloop
  have hm := Within.move (state 0) t r (Ne.symm hrt)
  have hout : ((state 0).set t 0).set r ((state 0).reg r + (state 0).reg t) =
      d.set s (d.reg s + d.reg r) := by
    ext u <;> simp only [state, Data.set]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
      simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst, ht, n]
  have ht' : (state 0).reg t = n := by simp [state, Data.set]
  have h := hloop.seq hm
  rw [hout, ht'] at h
  convert h using 1 <;> dsimp [copy, n] ; omega

def mulAdd (count source target backup : R) : Command R :=
  .loop count (copy source target backup)

 theorem mulAdd_evaluates (d : Data R) (c r s t : R)
    (hcr : c ≠ r) (hcs : c ≠ s) (hct : c ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (mulAdd c r s t) d ((d.set c 0).set s (d.reg s+d.reg c*d.reg r))
      (d.reg c*(5*d.reg r+3)+1) := by
  let n := d.reg c
  let state : ℕ → Data R := fun i => (d.set c i).set s (d.reg s+(n-i)*d.reg r)
  have hn : state n = d := by
    simp [state, n]
  have hloop : Within (.loop c (copy r s t)) (state n) (state 0)
      (n*(5*d.reg r+3)+1) := by
    apply Within.loop c _ state n (5*d.reg r+2)
    · intro i hi; simp [state, Data.set, hcs]
    · intro i hi
      have hr' : (decData (state (i+1)) c).reg r = d.reg r := by
        simp [state, decData, Data.set, Ne.symm hcr, hrs]
      have ht' : (decData (state (i+1)) c).reg t = 0 := by
        simp [state, decData, Data.set, Ne.symm hct, Ne.symm hst, ht]
      have h := copy_evaluates (decData (state (i+1)) c) r s t hrs hrt hst ht'
      rw [hr'] at h
      have hout : (decData (state (i+1)) c).set s
          ((decData (state (i+1)) c).reg s + d.reg r) = state i := by
        have hh : (n-(i+1))*d.reg r+d.reg r = (n-i)*d.reg r := by
          have : n-i = n-(i+1)+1 := by omega
          rw [this, Nat.add_mul, Nat.one_mul]
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = c <;> by_cases hs : u = s <;>
          simp [hu, hs, hcs, Ne.symm hcs, Nat.add_assoc] ; omega
      simpa only [hout] using h
  simpa [mulAdd, hn, state, n] using hloop

end Command
end

variable {R : Type} [DecidableEq R]
namespace Command

def put (r : R) : ℕ → Command R
  | 0 => .skip
  | n+1 => .seq (.inc r) (put r n)

 theorem put_evaluates (d : Data R) (r : R) (n : ℕ) :
    Within (put r n) d (d.set r (d.reg r+n)) (n+1) := by
  induction n generalizing d with
  | zero => simpa [put] using Within.skip d
  | succ n ih =>
    have h := (Within.inc d r).seq (ih (incData d r))
    have he : (incData d r).set r ((incData d r).reg r+n) = d.set r (d.reg r+(n+1)) := by
      simp [incData, Data.set, Nat.add_assoc, Nat.add_comm]
    rw [he] at h
    simpa only [put, show 1+(n+1) = n+1+1 by omega] using h

 def subFrom (r s : R) : Command R := .loop r (.dec s)

 theorem subFrom_evaluates (d : Data R) (r s : R) (h : r ≠ s) :
    Within (subFrom r s) d ((d.set r 0).set s (d.reg s-d.reg r)) (2*d.reg r+1) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => (d.set r i).set s (d.reg s-(n-i))
  have hn : state n = d := by simp [state, n]
  have hl : Within (.loop r (.dec s)) (state n) (state 0) (n*2+1) := by
    apply Within.loop r _ state n 1
    · intro i hi; simp [state, Data.set, h]
    · intro i hi
      have he : decData (decData (state (i+1)) r) s = state i := by
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;>
          simp [hu, hs, h, Ne.symm h] ; omega
      simpa only [he] using Within.dec (decData (state (i+1)) r) s
  simpa [subFrom, state, n, hn, Nat.mul_comm] using hl

 theorem rewind_evaluates (d : Data R) :
    Within (.rewind : Command R) d {d with input := d.backup.reverse++d.input, backup := []}
      (d.backup.length+1) := by
  generalize he : d.backup = xs
  induction xs generalizing d with
  | nil =>
    have hd : {d with input := [].reverse++d.input, backup := []} = d := by
      cases d; simp_all
    exact ⟨1, by simp, by rw [hd]; exact Evaluates.rewind_empty he⟩
  | cons b rest ih =>
    have hb : (backData d).backup = rest := by simp [backData, he]
    obtain ⟨n, hn, h⟩ := ih (backData d) hb
    have hout : {backData d with input := rest.reverse++(backData d).input, backup := []} =
        {d with input := (b::rest).reverse++d.input, backup := []} := by
      simp [backData, he, List.reverse_cons, List.append_assoc]
    rw [hout] at h
    exact ⟨1+n, by simp; omega, Evaluates.rewind_cons he h⟩

def skipInput (r : R) : Command R := .loop r (.read .skip .skip .skip)

 theorem skipInput_evaluates (d : Data R) (r : R) :
    Within (skipInput r) d
      {(d.set r 0) with input := d.input.drop (d.reg r), backup := (d.input.take (d.reg r)).reverse++d.backup}
      (3*d.reg r+1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have he : {d.set r 0 with input := d.input.drop 0, backup := (d.input.take 0).reverse++d.backup} = d := by
      simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append]
      rw [← hn, Data.set_self]
    rw [he]
    exact ⟨1, by omega, Evaluates.loop_zero hn⟩
  | succ n ih =>
    let e := readData (decData d r)
    have he : e.reg r = n := by simp [e, readData, decData, hn]
    obtain ⟨a, ha, hr⟩ := ih e he
    have hb : Evaluates (.read .skip .skip .skip) (decData d r) e 2 := by
      cases hinput : d.input with
      | nil => exact Evaluates.read_empty (d := decData d r) hinput (Evaluates.skip _)
      | cons b rest =>
        cases b
        · exact Evaluates.read_zero (d := decData d r) hinput (Evaluates.skip _)
        · exact Evaluates.read_one (d := decData d r) hinput (Evaluates.skip _)
    have hout : {e.set r 0 with input := e.input.drop n, backup := (e.input.take n).reverse++e.backup} =
        {d.set r 0 with input := d.input.drop (n+1), backup := (d.input.take (n+1)).reverse++d.backup} := by
      cases hi : d.input with
      | nil => simp [e, readData, decData, Data.set, hi]
      | cons b rest => simp [e, readData, decData, Data.set, hi, List.reverse_cons, List.append_assoc]
    rw [hout] at hr
    refine ⟨1+2+a, by omega, Evaluates.loop_pos (by omega) hb hr⟩

def inputBit (index result : R) : Command R :=
  .seq (skipInput index) (.seq (.read (.inc result) .skip .skip) .rewind)

 theorem inputBit_evaluates (d : Data R) (i r : R) (hir : i ≠ r)
    (hb : d.backup = []) (hr : d.reg r = 0) :
    Within (inputBit i r) d ((d.set i 0).set r (if d.input[d.reg i]?.getD false then 1 else 0))
      (3*d.reg i+d.input.length+4) := by
  let e : Data R := {d.set i 0 with input := d.input.drop (d.reg i), backup := (d.input.take (d.reg i)).reverse++d.backup}
  have he := skipInput_evaluates d i
  let bit := (d.input[d.reg i]?).getD false
  let f : Data R := (readData e).set r (if bit then 1 else 0)
  have hread : Within (.read (.inc r) .skip .skip) e f 2 := by
    have er : e.reg r = 0 := by simp [e, Data.set, Ne.symm hir, hr]
    have bit_head : (e.input.head?).getD false = bit := by
      simp [e, bit, List.head?_drop]
    cases hi : e.input with
    | nil =>
      have hbit : bit = false := by simpa [hi] using bit_head.symm
      have hf : f = readData e := by simp [f, hbit, readData, ← er]
      exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_empty hi (Evaluates.skip _)⟩
    | cons b rest =>
      cases b
      · have hbit : bit = false := by simpa [hi] using bit_head.symm
        have hf : f = readData e := by simp [f, hbit, readData, ← er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_zero hi (Evaluates.skip _)⟩
      · have hbit : bit = true := by simpa [hi] using bit_head.symm
        have hf : f = incData (readData e) r := by simp [f, hbit, incData, Data.set, readData, er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_one hi (Evaluates.inc _ _)⟩
  have hrew := rewind_evaluates f
  have restored : {f with input := f.backup.reverse++f.input, backup := []} =
      (d.set i 0).set r (if bit then 1 else 0) := by
    have heq : e.backup.reverse ++ e.input = d.input := by
      simp [e, hb]
    have heq' : (readData e).backup.reverse ++ (readData e).input = d.input := by
      rw [readData]
      simp only [List.reverse_append, List.reverse_take]
      cases hi : e.input <;> simpa [hi, List.append_assoc] using heq
    apply Data.ext
    · rfl
    · exact heq'
    · exact hb.symm
    · rfl
  have size : f.backup.length ≤ d.input.length := by
    dsimp [f, Data.set, readData, e]
    simp only [List.length_append, List.length_take, List.length_reverse, hb, List.length_nil,
      add_zero, List.length_drop]
    omega
  have hh := he.seq (hread.seq hrew)
  rw [restored] at hh
  exact hh.mono (by omega)

end Command
end IndependentSetsCut.CounterMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_LengthLoop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine

section
variable {R : Type} [DecidableEq R]
namespace Command

def lengthLoop (guard result : R) : Command R :=
  .loop guard (.read (.seq (.inc guard) (.inc result)) (.seq (.inc guard) (.inc result)) .skip)

 theorem lengthLoop_evaluates (d : Data R) (g r : R) (hgr : g ≠ r) (hg : d.reg g = 1) :
    Within (lengthLoop g r) d
      {((d.set g 0).set r (d.reg r+d.input.length)) with
        input := [], backup := d.input.reverse++d.backup}
      (4*d.input.length+4) := by
  generalize hx : d.input = xs
  induction xs generalizing d with
  | nil =>
    have he : readData (decData d g) = d.set g 0 := by
      simp [readData, decData, Data.set, hx, hg]
    have hread : Evaluates (.read (.seq (.inc g) (.inc r)) (.seq (.inc g) (.inc r)) .skip)
        (decData d g) (d.set g 0) 2 := by
      rw [← he]
      exact Evaluates.read_empty (d := decData d g) hx (Evaluates.skip _)
    have hloop : Evaluates (lengthLoop g r) d (d.set g 0) 4 :=
      Evaluates.loop_pos (by omega) hread (Evaluates.loop_zero (by simp))
    have hf : {((d.set g 0).set r (d.reg r + ([] : List Bool).length)) with input := [], backup := [].reverse++d.backup} = d.set g 0 := by
      apply Data.ext
      · simp [Data.set, Ne.symm hgr]
      · exact hx.symm
      · simp [Data.set]
      · rfl
    exact ⟨4, by simp, by rw [hf]; exact hloop⟩
  | cons b xs ih =>
    let e := incData (incData (readData (decData d g)) g) r
    have eg : e.reg g = 1 := by simp [e, incData, decData, readData, hgr, hg]
    have ei : e.input = xs := by simp [e, incData, decData, readData, hx]
    obtain ⟨n, hn, he⟩ := ih e eg ei
    have hread : Evaluates (.read (.seq (.inc g) (.inc r)) (.seq (.inc g) (.inc r)) .skip)
        (decData d g) e 3 := by
      have hi := Evaluates.seq (Evaluates.inc (readData (decData d g)) g)
        (Evaluates.inc (incData (readData (decData d g)) g) r)
      cases b
      · exact Evaluates.read_zero (d := decData d g) hx hi
      · exact Evaluates.read_one (d := decData d g) hx hi
    have heq : {((e.set g 0).set r (e.reg r+xs.length)) with input := [], backup := xs.reverse++e.backup} =
        {((d.set g 0).set r (d.reg r+(b::xs).length)) with input := [], backup := (b::xs).reverse++d.backup} := by
      apply Data.ext
      · ext u
        by_cases hu : u = g <;> by_cases hr : u = r <;>
          simp [e, incData, decData, readData, Data.set, hu, hr,
            hgr, Ne.symm hgr, hg, Nat.add_assoc, Nat.add_comm]
      · rfl
      · simp [e, incData, decData, readData, hx, List.reverse_cons, List.append_assoc]
      · rfl
    rw [heq] at he
    exact ⟨1+3+n, by simp; omega, Evaluates.loop_pos (by omega) hread he⟩

 def inputLength (g r : R) : Command R := .seq (.inc g) (.seq (lengthLoop g r) .rewind)

 theorem inputLength_evaluates (d : Data R) (g r : R) (hgr : g ≠ r)
    (hg : d.reg g = 0) (hr : d.reg r = 0) (hb : d.backup = []) :
    Within (inputLength g r) d (d.set r d.input.length) (5*d.input.length+6) := by
  have he := lengthLoop_evaluates (incData d g) g r hgr (by simp [incData, hg])
  obtain ⟨n,hn,h⟩ := he
  let e : Data R := {((incData d g).set g 0).set r ((incData d g).reg r+d.input.length)
    with input := [], backup := d.input.reverse++d.backup}
  have he' : Within (lengthLoop g r) (incData d g) e (4*d.input.length+4) := ⟨n,hn,h⟩
  have hw := rewind_evaluates e
  have hout : {e with input := e.backup.reverse++e.input, backup := []} = d.set r d.input.length := by
    apply Data.ext
    · ext u
      by_cases hu : u = g <;> by_cases hu' : u = r <;>
        simp [e, incData, Data.set, hu, hu', hgr, Ne.symm hgr, hg, hr]
    · simp [e, hb, Data.set]
    · exact hb.symm
    · rfl
  have size : e.backup.length = d.input.length := by simp [e, hb]
  have hfull := (Within.inc d g).seq (he'.seq hw)
  rw [hout, size] at hfull
  exact hfull.mono (by omega)

end Command
end

open scoped BigOperators
open Finset

inductive Expr where
  | const (n : ℕ)
  | arg (i : ℕ)
  | length
  | bit (index : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | zero (a : Expr)
  | sum (bound body : Expr)

namespace Expr

def bind (v : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | n+1 => v n

 def eval (input : List Bool) (args : ℕ → ℕ) : Expr → ℕ
  | .const n => n
  | .arg i => args i
  | .length => input.length
  | .bit e => if (input[eval input args e]?).getD false then 1 else 0
  | .add a b => eval input args a + eval input args b
  | .sub a b => eval input args a - eval input args b
  | .mul a b => eval input args a * eval input args b
  | .zero a => if eval input args a = 0 then 1 else 0
  | .sum b f => ∑ i ∈ range (eval input args b), eval input (bind args i) f

 def valueBudget : Expr → ℕ → ℕ
  | .const n, _ => n
  | .arg _, M => M
  | .length, M => M
  | .bit _, _ => 1
  | .add a b, M => valueBudget a M + valueBudget b M
  | .sub a _, M => valueBudget a M
  | .mul a b, M => valueBudget a M * valueBudget b M
  | .zero _, _ => 1
  | .sum b f, M => valueBudget b M * valueBudget f (M+valueBudget b M)

 theorem eval_le (e : Expr) (input : List Bool) (args : ℕ → ℕ) (M : ℕ)
    (hi : input.length ≤ M) (ha : ∀ i, args i ≤ M) :
    e.eval input args ≤ e.valueBudget M := by
  induction e generalizing args M with
  | const n => exact le_rfl
  | arg i => exact ha i
  | length => exact hi
  | bit e ih => simp only [eval, valueBudget]; split_ifs <;> omega
  | zero e ih => simp only [eval, valueBudget]; split_ifs <;> omega
  | add a b ia ib => exact Nat.add_le_add (ia _ _ hi ha) (ib _ _ hi ha)
  | sub a b ia ib => exact (Nat.sub_le _ _).trans (ia _ _ hi ha)
  | mul a b ia ib => exact Nat.mul_le_mul (ia _ _ hi ha) (ib _ _ hi ha)
  | sum b f ib iF =>
    have hb := ib args M hi ha
    calc
      _ ≤ ∑ _ ∈ range (eval input args b), f.valueBudget (M+b.valueBudget M) := by
        apply sum_le_sum; intro i hi'
        apply iF
        · omega
        · intro j
          cases j with
          | zero => dsimp [bind]; have := mem_range.mp hi'; omega
          | succ j => exact (ha j).trans (by omega)
      _ = eval input args b * f.valueBudget (M+b.valueBudget M) := by simp
      _ ≤ b.valueBudget M * f.valueBudget (M+b.valueBudget M) := Nat.mul_le_mul_right _ hb

 def timeBudget : Expr → ℕ → ℕ
  | .const n, _ => n+1
  | .arg _, M => 5*M+2
  | .length, M => 5*M+6
  | .bit e, M => timeBudget e M+3*valueBudget e M+M+7
  | .add a b, M | .sub a b, M => timeBudget a M+timeBudget b M+2*valueBudget b M+1
  | .mul a b, M => timeBudget a M+timeBudget b M+
      valueBudget b M*(5*valueBudget a M+3)+1+2*valueBudget a M+1+
      2*(valueBudget a M*valueBudget b M)+1
  | .zero a, M => timeBudget a M+2*valueBudget a M+2
  | .sum b f, M => timeBudget b M+valueBudget b M*
      (timeBudget f (M+valueBudget b M)+2*valueBudget f (M+valueBudget b M)+3)+2*valueBudget b M+2

 def compile (vars : ℕ → ℕ) (k : ℕ) : Expr → Command ℕ
  | .const n => Command.put k n
  | .arg i => Command.copy (vars i) k (k+1)
  | .length => Command.inputLength (k+1) k
  | .bit e => .seq (compile vars k e)
      (.seq (Command.inputBit k (k+1)) (Command.move (k+1) k))
  | .add a b => .seq (compile vars k a) (.seq (compile vars (k+1) b) (Command.move (k+1) k))
  | .sub a b => .seq (compile vars k a) (.seq (compile vars (k+1) b) (Command.subFrom (k+1) k))
  | .mul a b => .seq (compile vars k a) (.seq (compile vars (k+1) b)
      (.seq (Command.mulAdd (k+1) k (k+2) (k+3))
        (.seq (Command.clear k) (Command.move (k+2) k))))
  | .zero a => .seq (compile vars k a) (.test k (.inc k) (Command.clear k))
  | .sum b f => .seq (compile vars (k+1) b)
      (.seq (.loop (k+1) (.seq (compile (bind vars (k+2)) (k+3) f)
        (.seq (Command.move (k+3) k) (.inc (k+2))))) (Command.clear (k+2)))

end Expr
namespace Data

def Clean (d : Data ℕ) (k : ℕ) : Prop := ∀ r, k ≤ r → d.reg r = 0

 theorem Clean.mono {d : Data ℕ} {k l : ℕ} (hc : d.Clean k) (h : k ≤ l) : d.Clean l :=
  fun r hr => hc r (h.trans hr)

 theorem Clean.set_succ {d : Data ℕ} {k : ℕ} (hc : d.Clean k) (v : ℕ) :
    (d.set k v).Clean (k+1) := by
  intro r hr
  rw [set_reg_ne _ _ _ _ (by omega)]
  exact hc r (by omega)

 theorem set_args (d : Data ℕ) (vars : ℕ → ℕ) (k v : ℕ) (h : ∀ i, vars i < k) :
    (fun i => (d.set k v).reg (vars i)) = (fun i => d.reg (vars i)) := by
  funext i
  exact set_reg_ne _ _ _ _ (by have := h i; omega)

 theorem set_clean_zero {d : Data ℕ} {k r : ℕ} (hc : d.Clean k) (h : k ≤ r) :
    d.set r 0 = d := by rw [← hc r h, set_self]

end Data
end IndependentSetsCut.CounterMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Correct
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators
open Finset Command

def Correct (e : Expr) : Prop := ∀ (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ),
    (∀ i, vars i < k) → d.Clean k → d.backup = [] → d.input.length ≤ M →
    (∀ i, d.reg (vars i) ≤ M) →
    Within (e.compile vars k) d (d.set k (e.eval d.input (fun i => d.reg (vars i)))) (e.timeBudget M)

 theorem correct_const (n : ℕ) : Correct (.const n) := by
  intro vars k d M hv hc hb hi ha
  simpa [compile, eval, timeBudget, hc k le_rfl] using put_evaluates d k n

 theorem correct_arg (i : ℕ) : Correct (.arg i) := by
  intro vars k d M hv hc hb hi ha
  have he := copy_evaluates d (vars i) k (k+1) (by have := hv i; omega)
    (by have := hv i; omega) (by omega) (hc _ (by omega))
  simp only [hc k le_rfl, zero_add] at he
  exact he.mono (by dsimp [timeBudget]; have := ha i; omega)

 theorem correct_length : Correct .length := by
  intro vars k d M hv hc hb hi ha
  exact (inputLength_evaluates d (k+1) k (by omega) (hc _ (by omega)) (hc _ le_rfl) hb).mono
    (by dsimp [timeBudget]; omega)

 theorem binary_start {a b : Expr} (hca : Correct a) (hcb : Correct b)
    (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ)
    (hv : ∀ i, vars i < k) (hc : d.Clean k) (hb : d.backup = []) (hi : d.input.length ≤ M)
    (ha : ∀ i, d.reg (vars i) ≤ M) :
    Within (.seq (a.compile vars k) (b.compile vars (k+1))) d
      ((d.set k (a.eval d.input (fun i => d.reg (vars i)))).set (k+1)
        (b.eval d.input (fun i => d.reg (vars i))))
      (a.timeBudget M+b.timeBudget M) := by
  have h1 := hca vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h2 := hcb vars (k+1) (d.set k A) M (fun i => by have := hv i; omega)
    (hc.set_succ A) hb hi (fun i => by
      rw [Data.set_reg_ne d k (vars i) A (Nat.ne_of_lt (hv i))]
      exact ha i)
  rw [Data.set_args d vars k A hv] at h2
  exact h1.seq h2

 theorem correct_add {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.add a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := Within.move e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k+e.reg (k+1)) = d.set k (A+B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (move (k+1) k) e (d.set k (A+B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_sub {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.sub a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := subFrom_evaluates e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k-e.reg (k+1)) = d.set k (A-B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (subFrom (k+1) k) e (d.set k (A-B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_zero {a : Expr} (hca : Correct a) : Correct (.zero a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 : Within (.test k (.inc k) (clear k)) (d.set k A)
      (d.set k (if A=0 then 1 else 0)) (2*A+2) := by
    by_cases hA : A=0
    · refine ⟨2, by omega, Evaluates.test_zero (r := k) (n := 1) (d := d.set k A) (by simp [hA]) ?_⟩
      simpa [hA, incData, Data.set] using Evaluates.inc (d.set k A) k
    · refine ⟨1+(2*A+1), by omega, Evaluates.test_pos (r := k) (d := d.set k A) (by simpa using hA) ?_⟩
      simpa [hA] using clear_evaluates (d.set k A) k
  have h := h1.seq h2
  exact h.mono (by dsimp [timeBudget]; have := a.eval_le d.input _ M hi ha; dsimp [A] at *; omega)

 theorem correct_bit {a : Expr} (hca : Correct a) : Correct (.bit a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := if (d.input[A]?).getD false then 1 else 0
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 := inputBit_evaluates (d.set k A) k (k+1) (by omega) hb
    (by rw [Data.set_reg_ne _ _ _ _ (by omega)]; exact hc _ (by omega))
  have hout2 : ((d.set k A).set k 0).set (k+1) B = d.set (k+1) B := by
    rw [Data.set_set, Data.set_clean_zero hc le_rfl]
  simp only [Data.set_reg_same] at h2
  change Within (inputBit k (k+1)) (d.set k A)
    (((d.set k A).set k 0).set (k+1) B) (3*A+d.input.length+4) at h2
  rw [hout2] at h2
  have h3 := Within.move (d.set (k+1) B) (k+1) k (by omega)
  have hout3 : ((d.set (k+1) B).set (k+1) 0).set k
      ((d.set (k+1) B).reg k+(d.set (k+1) B).reg (k+1)) = d.set k B := by
    simp only [Data.set_set]
    rw [Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  have h3' : Within (move (k+1) k) (d.set (k+1) B) (d.set k B) (2*B+1) := by
    rw [hout3] at h3
    simpa only [Data.set_reg_same] using h3
  have h := h1.seq (h2.seq h3')
  have hB : B ≤ 1 := by dsimp [B]; split_ifs <;> omega
  exact h.mono (by have hA := a.eval_le d.input _ M hi ha; dsimp [timeBudget, A] at *; omega)

end IndependentSetsCut.CounterMachine.Expr

namespace IndependentSetsCut.CounterMachine.Command
variable {R : Type} [DecidableEq R]
 theorem Within.assoc {a b c : Command R} {d e : Data R} {B : ℕ}
    (h : Within (.seq (.seq a b) c) d e B) : Within (.seq a (.seq b c)) d e B := by
  obtain ⟨n, hn, he⟩ := h
  cases he with
  | seq hab hc =>
    cases hab with
    | seq ha hb =>
      exact ⟨_, by omega, Evaluates.seq ha (Evaluates.seq hb hc)⟩
end IndependentSetsCut.CounterMachine.Command
namespace IndependentSetsCut.CounterMachine.Expr
open Command

 theorem correct_mul {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.mul a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hz1 := hc (k+1) (by omega)
  have hz2 := hc (k+2) (by omega)
  have hz3 := hc (k+3) (by omega)
  have hm := mulAdd_evaluates e (k+1) k (k+2) (k+3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simp [e, hz3, Data.set])
  have hout : (e.set (k+1) 0).set (k+2) (e.reg (k+2)+e.reg (k+1)*e.reg k) =
      (d.set k A).set (k+2) (A*B) := by
    apply Data.ext
    · ext u
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [e, Data.set, h0, h1, h2, hz1, hz2, Nat.mul_comm]
    all_goals rfl
  rw [hout] at hm
  have hm' : Within (mulAdd (k+1) k (k+2) (k+3)) e ((d.set k A).set (k+2) (A*B))
      (B*(5*A+3)+1) := by simpa [e, Data.set] using hm
  let f := (d.set k A).set (k+2) (A*B)
  have hf := Within.clear f k
  have houtf : f.set k 0 = d.set (k+2) (A*B) := by
    change (((d.set k A).set (k+2) (A*B)).set k 0) = _
    rw [Data.set_comm _ k (k+2) _ _ (by omega)]
    rw [Data.set_set]
    rw [Data.set_comm _ (k+2) k _ _ (by omega), Data.set_clean_zero hc le_rfl]
  rw [houtf] at hf
  have hf' : Within (clear k) f (d.set (k+2) (A*B)) (2*A+1) := by
    simpa [f, Data.set] using hf
  have hg := Within.move (d.set (k+2) (A*B)) (k+2) k (by omega)
  have houtg : ((d.set (k+2) (A*B)).set (k+2) 0).set k
      ((d.set (k+2) (A*B)).reg k+(d.set (k+2) (A*B)).reg (k+2)) = d.set k (A*B) := by
    rw [Data.set_set, Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  rw [houtg] at hg
  have hg' : Within (move (k+2) k) (d.set (k+2) (A*B)) (d.set k (A*B)) (2*(A*B)+1) := by
    simpa only [Data.set_reg_same] using hg
  have hh := (hs.seq (hm'.seq (hf'.seq hg'))).assoc
  apply hh.mono
  have hA := a.eval_le d.input _ M hi ha
  have hB := b.eval_le d.input _ M hi ha
  change a.timeBudget M+b.timeBudget M+(B*(5*A+3)+1+(2*A+1+(2*(A*B)+1))) ≤ _
  change A ≤ a.valueBudget M at hA
  change B ≤ b.valueBudget M at hB
  dsimp only [timeBudget]
  calc
    _ ≤ a.timeBudget M+b.timeBudget M+
        (b.valueBudget M*(5*a.valueBudget M+3)+1+
          (2*a.valueBudget M+1+(2*(a.valueBudget M*b.valueBudget M)+1))) := by gcongr
    _ = _ := by omega

end IndependentSetsCut.CounterMachine.Expr

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_ValuePolynomial
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr

section
open Polynomial

 noncomputable def valuePolynomial : Expr → Polynomial ℕ
  | .const n => C n
  | .arg _ | .length => X
  | .bit _ | .zero _ => 1
  | .add a b => valuePolynomial a+valuePolynomial b
  | .sub a _ => valuePolynomial a
  | .mul a b => valuePolynomial a*valuePolynomial b
  | .sum b f => valuePolynomial b*(valuePolynomial f).comp (X+valuePolynomial b)

 theorem valuePolynomial_eval (e : Expr) (M : ℕ) :
    e.valuePolynomial.eval M = e.valueBudget M := by
  induction e generalizing M <;>
    simp_all [valuePolynomial, valueBudget, Polynomial.eval_comp]

 noncomputable def timePolynomial : Expr → Polynomial ℕ
  | .const n => C (n+1)
  | .arg _ => 5*X+2
  | .length => 5*X+6
  | .bit e => timePolynomial e+3*valuePolynomial e+X+7
  | .add a b | .sub a b => timePolynomial a+timePolynomial b+2*valuePolynomial b+1
  | .mul a b => timePolynomial a+timePolynomial b+
      valuePolynomial b*(5*valuePolynomial a+3)+1+2*valuePolynomial a+1+
      2*(valuePolynomial a*valuePolynomial b)+1
  | .zero a => timePolynomial a+2*valuePolynomial a+2
  | .sum b f => timePolynomial b+valuePolynomial b*
      ((timePolynomial f).comp (X+valuePolynomial b)+
        2*(valuePolynomial f).comp (X+valuePolynomial b)+3)+2*valuePolynomial b+2

 theorem timePolynomial_eval (e : Expr) (M : ℕ) :
    e.timePolynomial.eval M = e.timeBudget M := by
  induction e generalizing M <;>
    simp_all [timePolynomial, timeBudget, valuePolynomial_eval, Polynomial.eval_comp]

end

open scoped BigOperators
open Finset Command

 theorem correct_sum {b f : Expr} (hcb : Correct b) (hcf : Correct f) : Correct (.sum b f) := by
  intro vars k d M hv hc hb hi ha
  let args := fun i => d.reg (vars i)
  let B := b.eval d.input args
  let F := fun i => f.eval d.input (bind args i)
  let V := b.valueBudget M
  let W := f.valueBudget (M+V)
  let T := f.timeBudget (M+V)
  have hB : B ≤ V := b.eval_le d.input args M hi ha
  have hF : ∀ i < B, F i ≤ W := by
    intro i hi'
    apply f.eval_le
    · omega
    · intro j; cases j with
      | zero => dsimp [bind]; omega
      | succ j => exact (ha j).trans (by omega)
  let state : ℕ → Data ℕ := fun i =>
    ((d.set k (∑ j ∈ range (B-i), F j)).set (k+1) i).set (k+2) (B-i)
  have hz : ∀ r, k ≤ r → d.reg r = 0 := hc
  have hbnd := hcb vars (k+1) d M (fun i => by have := hv i; omega)
    (hc.mono (by omega)) hb hi ha
  have hstart : state B = d.set (k+1) B := by
    simp only [state, Nat.sub_self, range_zero, sum_empty]
    rw [Data.set_clean_zero hc le_rfl]
    exact Data.set_clean_zero ((hc.mono (by omega)).set_succ B) le_rfl
  have hloop : Within (.loop (k+1) (.seq (compile (bind vars (k+2)) (k+3) f)
      (.seq (move (k+3) k) (.inc (k+2))))) (state B) (state 0) (B*(T+2*W+3)+1) := by
    apply (Within.loop (k+1) _ state B (T+2*W+2))
    · intro i hi'
      simp [state, Data.set]
    · intro i hi'
      let j := B-(i+1)
      let e := decData (state (i+1)) (k+1)
      have hj : j < B := by dsimp [j]; omega
      have hindex : B-i = j+1 := by dsimp [j]; omega
      have heclean : e.Clean (k+3) := by
        intro r hr
        have h0 : r ≠ k := by omega
        have h1 : r ≠ k+1 := by omega
        have h2 : r ≠ k+2 := by omega
        simp [e, decData, state, Data.set, h0, h1, h2, hc r (by omega)]
      have henv : (fun u => e.reg (bind vars (k+2) u)) = bind args j := by
        funext u
        cases u with
        | zero => simp [e, decData, state, Data.set, bind, j]
        | succ u =>
          have h0 : vars u ≠ k := by have := hv u; omega
          have h1 : vars u ≠ k+1 := by have := hv u; omega
          have h2 : vars u ≠ k+2 := by have := hv u; omega
          simp [e, decData, state, Data.set, bind, args, h0, h1, h2]
      have heargs : ∀ u, e.reg (bind vars (k+2) u) ≤ M+V := by
        intro u
        change (fun u => e.reg (bind vars (k+2) u)) u ≤ M+V
        rw [henv]
        cases u with
        | zero => dsimp [bind]; omega
        | succ u => exact (ha u).trans (by omega)
      have hf := hcf (bind vars (k+2)) (k+3) e (M+V)
        (fun u => by cases u with
          | zero => dsimp [bind]; omega
          | succ u => dsimp [bind]; have := hv u; omega) heclean hb (by exact hi.trans (by omega)) heargs
      rw [henv] at hf
      change Within _ e (e.set (k+3) (F j)) T at hf
      have hm := Within.move (e.set (k+3) (F j)) (k+3) k (by omega)
      let out := (((e.set (k+3) (F j)).set (k+3) 0).set k
        ((e.set (k+3) (F j)).reg k+(e.set (k+3) (F j)).reg (k+3)))
      have hh := hf.seq (hm.seq (Within.inc out (k+2)))
      have hsum : (∑ u ∈ range (B-i), F u) = (∑ u ∈ range j, F u)+F j := by
        rw [hindex, sum_range_succ]
      have hout : incData out (k+2) = state i := by
        apply Data.ext
        · ext u
          have hz3 := hc (k+3) (by omega)
          by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;>
            by_cases h2 : u = k+2 <;> by_cases h3 : u = k+3 <;>
            simp [out, e, state, Data.set, incData, decData,
              h0, h1, h2, h3, j, hsum, hz3] <;> omega
        all_goals rfl
      rw [hout] at hh
      apply hh.mono
      simp only [Data.set_reg_same]
      have := hF j hj
      omega
  rw [hstart] at hloop
  have hclear := Within.clear (state 0) (k+2)
  have hout : (state 0).set (k+2) 0 = d.set k (∑ j ∈ range B, F j) := by
    dsimp only [state]
    rw [Data.set_set]
    apply Data.ext
    · ext u
      have hz1 := hc (k+1) (by omega)
      have hz2 := hc (k+2) (by omega)
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [Data.set, h0, h1, h2, hz1, hz2]
    all_goals rfl
  rw [hout] at hclear
  have hclear' : Within (clear (k+2)) (state 0) (d.set k (∑ j ∈ range B, F j)) (2*B+1) := by
    simpa [state, Data.set] using hclear
  have hh := hbnd.seq (hloop.seq hclear')
  apply hh.mono

  change _ ≤ b.timeBudget M+V*(T+2*W+3)+2*V+2
  have ht := Nat.mul_le_mul_right (T+2*W+3) hB
  omega

 theorem correct (e : Expr) : Correct e := by
  induction e with
  | const n => exact correct_const n
  | arg i => exact correct_arg i
  | length => exact correct_length
  | bit a ih => exact correct_bit ih
  | add a b ia ib => exact correct_add ia ib
  | sub a b ia ib => exact correct_sub ia ib
  | mul a b ia ib => exact correct_mul ia ib
  | zero a ih => exact correct_zero ih
  | sum b f ib iF => exact correct_sum ib iF

end IndependentSetsCut.CounterMachine.Expr

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Restrict
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine

 def Data.restrict (N : ℕ) (d : Data ℕ) : Data (Fin N) :=
  ⟨fun r => d.reg r.val, d.input, d.backup, d.output⟩

namespace Command

 def Bounded (N : ℕ) : Command ℕ → Prop
  | .skip | .write _ | .discard | .rewind => True
  | .inc r | .dec r => r < N
  | .seq a b => Bounded N a ∧ Bounded N b
  | .test r a b => r < N ∧ Bounded N a ∧ Bounded N b
  | .read a b c => Bounded N a ∧ Bounded N b ∧ Bounded N c
  | .loop r b => r < N ∧ Bounded N b

 def regCount : Command ℕ → ℕ
  | .skip | .write _ | .discard | .rewind => 0
  | .inc r | .dec r => r+1
  | .seq a b => max a.regCount b.regCount
  | .test r a b => max (r+1) (max a.regCount b.regCount)
  | .read a b c => max a.regCount (max b.regCount c.regCount)
  | .loop r b => max (r+1) b.regCount

 theorem bounded_of_count (c : Command ℕ) (N : ℕ) (h : c.regCount ≤ N) : c.Bounded N := by
  induction c <;> simp_all [Bounded, regCount]

 def restrict (N : ℕ) : (c : Command ℕ) → Bounded N c → Command (Fin N)
  | .skip, _ => .skip
  | .inc r, h => .inc ⟨r,h⟩
  | .dec r, h => .dec ⟨r,h⟩
  | .write b, _ => .write b
  | .discard, _ => .discard
  | .rewind, _ => .rewind
  | .seq a b, h => .seq (restrict N a h.1) (restrict N b h.2)
  | .test r a b, h => .test ⟨r,h.1⟩ (restrict N a h.2.1) (restrict N b h.2.2)
  | .read a b c, h => .read (restrict N a h.1) (restrict N b h.2.1) (restrict N c h.2.2)
  | .loop r b, h => .loop ⟨r,h.1⟩ (restrict N b h.2)

 theorem restrict_inc (N : ℕ) (d : Data ℕ) (r : ℕ) (h : r<N) :
    (incData d r).restrict N = incData (d.restrict N) ⟨r,h⟩ := by
  apply Data.ext
  · ext u
    simp only [Data.restrict, incData]
    by_cases hu : u.val = r
    · have he : u = ⟨r,h⟩ := Fin.ext hu
      simp [he]
    · have he : u ≠ ⟨r,h⟩ := fun he => hu (congrArg Fin.val he)
      simp [hu, he]
  all_goals rfl

 theorem restrict_dec (N : ℕ) (d : Data ℕ) (r : ℕ) (h : r<N) :
    (decData d r).restrict N = decData (d.restrict N) ⟨r,h⟩ := by
  apply Data.ext
  · ext u
    simp only [Data.restrict, decData]
    by_cases hu : u.val = r
    · have he : u = ⟨r,h⟩ := Fin.ext hu
      simp [he]
    · have he : u ≠ ⟨r,h⟩ := fun he => hu (congrArg Fin.val he)
      simp [hu, he]
  all_goals rfl

 theorem Evaluates.restrict {c : Command ℕ} {d e : Data ℕ} {n : ℕ}
    (he : Evaluates c d e n) (N : ℕ) (h : Bounded N c) :
    Evaluates (c.restrict N h) (d.restrict N) (e.restrict N) n := by
  induction he with
  | skip d => exact Evaluates.skip _
  | inc d r => simpa only [Command.restrict, restrict_inc N d r h] using Evaluates.inc (d.restrict N) ⟨r,h⟩
  | dec d r => simpa only [Command.restrict, restrict_dec N d r h] using Evaluates.dec (d.restrict N) ⟨r,h⟩
  | write d b => exact Evaluates.write _ _
  | discard d => exact Evaluates.discard _
  | rewind_empty hh => exact Evaluates.rewind_empty hh
  | rewind_cons hh he ih => exact Evaluates.rewind_cons hh (ih trivial)
  | seq h1 h2 i1 i2 => exact (i1 h.1).seq (i2 h.2)
  | test_zero hr he ih => exact Evaluates.test_zero hr (ih h.2.1)
  | test_pos hr he ih => exact Evaluates.test_pos hr (ih h.2.2)
  | read_one hr he ih => exact Evaluates.read_one hr (ih h.1)
  | read_zero hr he ih => exact Evaluates.read_zero hr (ih h.2.1)
  | read_empty hr he ih => exact Evaluates.read_empty hr (ih h.2.2)
  | loop_zero hr => exact Evaluates.loop_zero hr
  | @loop_pos r b d e f n m hr h1 h2 i1 i2 =>
    exact Evaluates.loop_pos hr (by simpa only [restrict_dec N d r h.1] using i1 h.2) (i2 h)

 def finite (c : Command ℕ) : Command (Fin c.regCount) :=
  c.restrict c.regCount (c.bounded_of_count _ le_rfl)

 theorem finite_evaluates {c : Command ℕ} {d e : Data ℕ} {n : ℕ}
    (h : Evaluates c d e n) : Evaluates c.finite (d.restrict c.regCount) (e.restrict c.regCount) n :=
  h.restrict _ _

end Command

open scoped BigOperators
open Command

def table (len bit : Expr) (input : List Bool) : List Bool :=
  List.ofFn (fun i : Fin (len.eval input (fun _ => 0)) =>
    decide (bit.eval input (fun _ => i.val) ≠ 0))

 def emit (r : ℕ) : Command ℕ := .test r (.write false) (.seq (clear r) (.write true))

 theorem emit_evaluates (d : Data ℕ) (r : ℕ) :
    Within (emit r) d (writeData (d.set r 0) (decide (d.reg r ≠ 0))) (2*d.reg r+3) := by
  by_cases hr : d.reg r = 0
  · refine ⟨2, by omega, ?_⟩
    have h := Evaluates.test_zero (r := r) (b := .seq (clear r) (.write true)) hr
      (Evaluates.write d false)
    have hd : d.set r 0 = d := by rw [← hr, Data.set_self]
    simpa [emit, hr, hd] using h
  · have h := Evaluates.test_pos (a := .write false) hr
      ((clear_evaluates d r).seq (Evaluates.write (d.set r 0) true))
    exact ⟨1+(2*d.reg r+1+1), by omega, by simpa [emit, hr] using h⟩

 def print (len bit : Expr) : Command ℕ :=
  .seq (len.compile (fun _ => 0) 1)
    (.loop 1 (.seq (bit.compile (fun _ => 1) 2) (emit 2)))

 theorem print_evaluates (len bit : Expr) (input : List Bool) :
    Within (print len bit) (initial input)
      {initial input with output := table len bit input}
      (len.timeBudget input.length+len.valueBudget input.length*
        (bit.timeBudget (input.length+len.valueBudget input.length)+
          2*bit.valueBudget (input.length+len.valueBudget input.length)+4)+1) := by
  let d : Data ℕ := initial input
  let L := len.eval input (fun _ => 0)
  let V := len.valueBudget input.length
  let M := input.length+V
  let T := bit.timeBudget M
  let W := bit.valueBudget M
  let out := table len bit input
  have hL : L ≤ V := len.eval_le input _ _ le_rfl (by simp)
  have holen : out.length = L := by simp [out, table, L]
  let state : ℕ → Data ℕ := fun i => {d.set 1 i with output := out.drop i}
  have hlen := len.correct (fun _ => 0) 1 d input.length (by omega)
    (by intro r hr; rfl) rfl le_rfl (by simp [d, initial])
  have hstart : state L = d.set 1 L := by
    simp [state, ← holen, d, initial, Data.set]
  have hloop : Within (.loop 1 (.seq (bit.compile (fun _ => 1) 2) (emit 2)))
      (state L) (state 0) (L*(T+2*W+4)+1) := by
    apply Within.loop 1 _ state L (T+2*W+3)
    · intro i hi; simp [state]
    · intro i hi
      let e := decData (state (i+1)) 1
      have heReg : e.reg = Function.update (fun _ => 0) 1 i := by
        simp [e, state, decData, Data.set, d, initial]
      have heClean : e.Clean 2 := by
        intro r hr
        rw [heReg]
        simp [show r ≠ 1 by omega]
      have heAt : e.reg 1 = i := by simp [heReg]
      have heArg : (fun u : ℕ => e.reg ((fun _ => 1) u)) = (fun _ => i) := by
        funext u; simp [heReg]
      have hc := bit.correct (fun _ => 1) 2 e M (by omega) heClean rfl
        (by change input.length ≤ M; dsimp [M]; omega)
        (by intro u; rw [heAt]; dsimp [M]; omega)
      rw [heArg] at hc
      let B := bit.eval input (fun _ => i)
      change Within _ e (e.set 2 B) T at hc
      have hemit := emit_evaluates (e.set 2 B) 2
      have hd : (e.set 2 B).set 2 0 = e := by
        rw [Data.set_set, Data.set_clean_zero heClean le_rfl]
      simp only [hd, Data.set_reg_same] at hemit
      have hh := hc.seq hemit
      have hdrop : decide (B ≠ 0) :: out.drop (i+1) = out.drop i := by
        have hi' : i < out.length := by omega
        rw [← List.getElem_cons_drop hi']
        congr 1
        simp [out, table, B]
      have hout : writeData e (decide (B ≠ 0)) = state i := by
        apply Data.ext
        · simp [writeData, heReg, state, d, initial, Data.set]
        · rfl
        · rfl
        · exact hdrop
      rw [hout] at hh
      apply hh.mono
      have hB : B ≤ W := bit.eval_le input _ M (by dsimp [M]; omega) (by intro u; dsimp [M]; omega)
      omega
  rw [hstart] at hloop
  have zend : state 0 = {initial input with output := table len bit input} := by
    simp [state, d, Data.set, initial, out]
  rw [zend] at hloop
  exact (hlen.seq hloop).mono (by

    change _ ≤ len.timeBudget input.length+V*(T+2*W+4)+1
    have := Nat.mul_le_mul_right (T+2*W+4) hL
    omega)

def eraseInput : Command ℕ := .seq (inputLength 1 0) (.loop 0 .discard)

 theorem eraseInput_evaluates (d : Data ℕ) (hz : d.Clean 0) (hb : d.backup = []) :
    Within eraseInput d {d with input := []} (7*d.input.length+7) := by
  have hl := inputLength_evaluates d 1 0 (by omega) (hz 1 (by omega)) (hz 0 le_rfl) hb
  let state : ℕ → Data ℕ := fun i => {d.set 0 i with input := d.input.drop (d.input.length-i)}
  have hs : state d.input.length = d.set 0 d.input.length := by simp [state, Data.set]
  have hf : state 0 = {d with input := []} := by
    simp [state, Data.set_clean_zero hz le_rfl]
  have hloop : Within (.loop 0 .discard) (state d.input.length) (state 0) (2*d.input.length+1) := by
    have h := Within.loop 0 (.discard : Command ℕ) state d.input.length 1
    have heq : 2*d.input.length+1 = d.input.length*(1+1)+1 := by omega
    rw [heq]
    apply h
    · intro i hi; simp [state]
    · intro i hi
      have he : discardData (decData (state (i+1)) 0) = state i := by
        apply Data.ext
        · simp [state, discardData, decData, Data.set]
        · simp only [discardData, decData, state, Data.set]
          rw [List.tail_drop]
          congr 1
          omega
        all_goals rfl
      exact ⟨1,le_rfl, by rw [← he]; exact Evaluates.discard _⟩
  rw [hs, hf] at hloop
  exact (hl.seq hloop).mono (by omega)

end IndependentSetsCut.CounterMachine

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Printer
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine
open Turing Polynomial Command

def printer (len bit : Expr) : Command ℕ := .seq (print len bit) eraseInput

noncomputable def printerTime (len bit : Expr) : Polynomial ℕ :=
  len.timePolynomial+len.valuePolynomial*
    (bit.timePolynomial.comp (X+len.valuePolynomial)+
      2*bit.valuePolynomial.comp (X+len.valuePolynomial)+4)+1+7*X+8

 theorem printer_evaluates (len bit : Expr) (input : List Bool) :
    Within (printer len bit) (initial input)
      ⟨fun _ => 0, [], [], table len bit input⟩ ((printerTime len bit).eval input.length-1) := by
  have hp := print_evaluates len bit input
  have he := eraseInput_evaluates {initial input with output := table len bit input}
    (by intro r hr; rfl) rfl
  have h := hp.seq he
  apply h.mono
  simp only [printerTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, Expr.timePolynomial_eval, Expr.valuePolynomial_eval]

  simp only [initial] at *
  omega

 theorem halted_eq {R : Type} [DecidableEq R] [Fintype R] (c : Command R) (out : List Bool) :
    embed (⟨⟨fun _ => 0, [], [], out⟩, none⟩ : Configuration R c.FinalLabel) =
      haltList c.finiteMachine out := by
  unfold embed haltList
  congr 1
  funext k
  cases k <;> simp [tapes, finiteMachine, machine]
  rfl

noncomputable def tableComputer (len bit : Expr) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (table len bit) where
  tm := (printer len bit).finite.finiteMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := printerTime len bit
  outputsFun input := by
    let h := printer_evaluates len bit input
    let n := Classical.choose h
    have hn := Classical.choose_spec h
    have he := Command.finite_evaluates hn.2
    change Evaluates _ (initial input) ⟨fun _ => 0, [], [], table len bit input⟩ n at he
    have run := machine_run he
    have hout := halted_eq (printer len bit).finite (table len bit input)
    have run' : StateTransition.EvalsToInTime (printer len bit).finite.finiteMachine.step
        (initList (printer len bit).finite.finiteMachine input)
        (some (haltList (printer len bit).finite.finiteMachine (table len bit input))) (n+1) := by
      convert run using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      unfold haltList embed
      congr 1
      funext k
      cases k <;> simp [tapes, finiteMachine, machine]
      rfl
    let run := run'
    refine ⟨⟨run.steps, ?_⟩, ?_⟩
    · change (flip Option.bind (printer len bit).finite.finiteMachine.step)^[run.steps]
        (some (initList (printer len bit).finite.finiteMachine (input.map (id : Bool → Bool)))) =
        some (haltList (printer len bit).finite.finiteMachine ((table len bit input).map (id : Bool → Bool)))
      erw [List.map_id, List.map_id]
      exact run.evals_in_steps
    · have hs := run.steps_le_m
      have hb := hn.1
      have hp : 0 < (printerTime len bit).eval input.length := by
        simp only [printerTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, Expr.timePolynomial_eval, Expr.valuePolynomial_eval]
        omega
      change run.steps ≤ (printerTime len bit).eval input.length
      omega

end IndependentSetsCut.CounterMachine

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators
open Finset

def rename (ρ : ℕ → ℕ) : Expr → Expr
  | .const n => .const n
  | .arg i => .arg (ρ i)
  | .length => .length
  | .bit e => .bit (rename ρ e)
  | .add a b => .add (rename ρ a) (rename ρ b)
  | .sub a b => .sub (rename ρ a) (rename ρ b)
  | .mul a b => .mul (rename ρ a) (rename ρ b)
  | .zero a => .zero (rename ρ a)
  | .sum b f => .sum (rename ρ b) (rename (bind (fun i => ρ i+1) 0) f)

@[simp] theorem rename_eval (e : Expr) (ρ : ℕ → ℕ) (input : List Bool) (args : ℕ → ℕ) :
    (e.rename ρ).eval input args = e.eval input (fun i => args (ρ i)) := by
  induction e generalizing ρ args <;> simp only [rename, eval] at *
  all_goals try simp_all
  case sum b f ib iF =>
    apply sum_congr rfl
    intro i hi
    congr 1
    funext j
    cases j <;> rfl

def bindExpr (σ : ℕ → Expr) (e : Expr) : ℕ → Expr
  | 0 => e
  | i+1 => σ i

def subst (σ : ℕ → Expr) : Expr → Expr
  | .const n => .const n
  | .arg i => σ i
  | .length => .length
  | .bit e => .bit (subst σ e)
  | .add a b => .add (subst σ a) (subst σ b)
  | .sub a b => .sub (subst σ a) (subst σ b)
  | .mul a b => .mul (subst σ a) (subst σ b)
  | .zero a => .zero (subst σ a)
  | .sum b f => .sum (subst σ b) (subst (bindExpr (fun i => (σ i).rename Nat.succ) (.arg 0)) f)

@[simp] theorem subst_eval (e : Expr) (σ : ℕ → Expr) (input : List Bool) (args : ℕ → ℕ) :
    (e.subst σ).eval input args = e.eval input (fun i => (σ i).eval input args) := by
  induction e generalizing σ args <;> simp only [subst, eval] at *
  all_goals try simp_all
  case sum b f ib iF =>
    apply sum_congr rfl
    intro i hi
    congr 1
    funext j
    cases j with
    | zero => rfl
    | succ j => simp [bindExpr, bind]

def positive (a : Expr) : Expr := .zero (.zero a)
def equal (a b : Expr) : Expr := .zero (.add (.sub a b) (.sub b a))
def le (a b : Expr) : Expr := .zero (.sub a b)
def lt (a b : Expr) : Expr := le (.add a (.const 1)) b

@[simp] theorem positive_eval (a : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (positive a).eval input args = if a.eval input args ≠ 0 then 1 else 0 := by
  simp [positive, eval]

@[simp] theorem equal_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (equal a b).eval input args = if a.eval input args = b.eval input args then 1 else 0 := by
  by_cases h : a.eval input args = b.eval input args
  · simp only [equal, eval, h, Nat.sub_self, Nat.zero_add, ↓reduceIte]
  · have hn : a.eval input args-b.eval input args+(b.eval input args-a.eval input args) ≠ 0 := by omega
    simp only [equal, eval, h, hn, ↓reduceIte]

@[simp] theorem le_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (le a b).eval input args = if a.eval input args ≤ b.eval input args then 1 else 0 := by
  simp [le, eval, Nat.sub_eq_zero_iff_le]

@[simp] theorem lt_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (lt a b).eval input args = if a.eval input args < b.eval input args then 1 else 0 := by
  simp [lt, eval]

def cond (c a b : Expr) : Expr := .add (.mul (positive c) a) (.mul (.zero c) b)
@[simp] theorem cond_eval (c a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (cond c a b).eval input args = if c.eval input args ≠ 0 then a.eval input args else b.eval input args := by
  simp only [cond, eval, positive_eval]; split_ifs <;> simp_all

def quotient (a b : Expr) : Expr :=
  .mul (positive b) (.sum a (le (.mul (.add (.arg 0) (.const 1)) (b.rename Nat.succ)) (a.rename Nat.succ)))

 theorem quotient_sum (a b : ℕ) (hb : 0 < b) :
    (∑ i ∈ range a, if (i+1)*b ≤ a then (1:ℕ) else 0) = a/b := by
  have hcond (i : ℕ) : (i+1)*b ≤ a ↔ i < a/b := by
    rw [← Nat.le_div_iff_mul_le hb, Nat.add_one_le_iff]
  simp_rw [hcond]
  rw [sum_boole]
  have hs : {i ∈ range a | i < a/b} = range (a/b) := by
    ext i; simp only [mem_filter, mem_range]
    exact and_iff_right_of_imp (fun hi => hi.trans_le (Nat.div_le_self _ _))
  simp only [hs, card_range, Nat.cast_id]

@[simp] theorem quotient_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (quotient a b).eval input args = a.eval input args / b.eval input args := by
  simp only [quotient, eval, positive_eval, le_eval, rename_eval, bind]
  by_cases hb : b.eval input args = 0
  · simp [hb]
  · simp only [hb, ne_eq, not_false_eq_true, ↓reduceIte, one_mul]
    simpa using quotient_sum (a.eval input args) (b.eval input args) (by omega)

def remainder (a b : Expr) : Expr := .sub a (.mul (quotient a b) b)
@[simp] theorem remainder_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (remainder a b).eval input args = a.eval input args % b.eval input args := by
  simp only [remainder, eval, quotient_eval]
  exact Nat.mod_eq_sub_div_mul.symm

def power (a : Expr) : ℕ → Expr
  | 0 => .const 1
  | n+1 => .mul (power a n) a
@[simp] theorem power_eval (a : Expr) (n : ℕ) (input : List Bool) (args : ℕ → ℕ) :
    (power a n).eval input args = (a.eval input args)^n := by
  induction n <;> simp [power, eval, pow_succ, *]

end IndependentSetsCut.CounterMachine.Expr

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_BitValue
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators
open Finset

def bitValue (input : List Bool) (i : ℕ) : ℕ := if (input[i]?).getD false then 1 else 0

def zeroPrefix (input : List Bool) (i : ℕ) : ℕ :=
  ∑ j ∈ range i, (1-bitValue input j)

def wordValue (input : List Bool) (k : ℕ) : ℕ :=
  ∑ i ∈ range input.length, bitValue input i * (if zeroPrefix input i = k then 1 else 0)

def prefixZeros (i : Expr) : Expr := .sum i (.zero (.bit (.arg 0)))
def word (k : Expr) : Expr := .sum .length
  (.mul (.bit (.arg 0)) (equal (prefixZeros (.arg 0)) (k.rename Nat.succ)))

@[simp] theorem prefixZeros_eval (i : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (prefixZeros i).eval input args = zeroPrefix input (i.eval input args) := by
  simp only [prefixZeros, eval, bind, zeroPrefix, bitValue]
  apply sum_congr rfl
  intro j hj
  by_cases h : (input[j]?).getD false = true <;> simp [h]

@[simp] theorem word_eval (k : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (word k).eval input args = wordValue input (k.eval input args) := by
  simp [word, eval, prefixZeros_eval, equal_eval, wordValue, bitValue, bind]
  rfl

@[simp] theorem bitValue_cons_zero (a : Bool) (s : List Bool) :
    bitValue (a::s) 0 = if a then 1 else 0 := by simp [bitValue]
@[simp] theorem bitValue_cons_succ (a : Bool) (s : List Bool) (i : ℕ) :
    bitValue (a::s) (i+1) = bitValue s i := by simp [bitValue]
@[simp] theorem zeroPrefix_zero (input : List Bool) : zeroPrefix input 0 = 0 := by simp [zeroPrefix]
@[simp] theorem zeroPrefix_cons_succ (a : Bool) (s : List Bool) (i : ℕ) :
    zeroPrefix (a::s) (i+1) = (if a then 0 else 1)+zeroPrefix s i := by
  rw [zeroPrefix, sum_range_succ']
  simp only [bitValue_cons_zero, bitValue_cons_succ, zeroPrefix]
  cases a <;> simp [add_comm]

@[simp] theorem wordValue_nil (k : ℕ) : wordValue [] k = 0 := by simp [wordValue]

 theorem wordValue_true (s : List Bool) (k : ℕ) :
    wordValue (true::s) k = (if k=0 then 1 else 0)+wordValue s k := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp [wordValue, eq_comm, add_comm]

@[simp] theorem wordValue_false_zero (s : List Bool) : wordValue (false::s) 0 = 0 := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp

 theorem wordValue_false_succ (s : List Bool) (k : ℕ) :
    wordValue (false::s) (k+1) = wordValue s k := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp [wordValue, Nat.add_comm 1]

 theorem wordValue_block_zero (n : ℕ) (s : List Bool) :
    wordValue (List.replicate n true ++ false::s) 0 = n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.cons_append, wordValue_true, ↓reduceIte, ih]; omega

 theorem wordValue_block_succ (n k : ℕ) (s : List Bool) :
    wordValue (List.replicate n true ++ false::s) (k+1) = wordValue s k := by
  induction n with
  | zero => simpa using wordValue_false_succ s k
  | succ n ih => simp [List.replicate_succ, wordValue_true, ih]

def unaryWords (words : List ℕ) : List Bool := words.flatMap (fun n => List.replicate n true ++ [false])

 theorem wordValue_encoded (words : List ℕ) (k : ℕ) :
    wordValue (unaryWords words) k = (words[k]?).getD 0 := by
  induction words generalizing k with
  | nil => simp [unaryWords]
  | cons n words ih =>
    cases k with
    | zero => simpa [unaryWords, List.append_assoc] using wordValue_block_zero n (unaryWords words)
    | succ k =>
      simp only [unaryWords, List.flatMap_cons, List.append_assoc, List.singleton_append]
      change wordValue (List.replicate n true ++ false :: unaryWords words) (k+1) = _
      rw [wordValue_block_succ, ih]
      simp

attribute [local instance] Classical.propDecidable

theorem indicator_and (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1:ℕ) else 0)*(if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP,hQ]

def divides (a b : Expr) : Expr := .zero (remainder b a)
@[simp] theorem divides_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (divides a b).eval input args = if a.eval input args ∣ b.eval input args then 1 else 0 := by
  simp [divides, eval, Nat.dvd_iff_mod_eq_zero]

def prime (n : Expr) : Expr := .mul (le (.const 2) n)
  (.zero (.sum n (.mul (le (.const 2) (.arg 0)) (divides (.arg 0) (n.rename Nat.succ)))))

@[simp] theorem prime_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (prime n).eval input args = if (n.eval input args).Prime then 1 else 0 := by
  simp only [prime, eval, le_eval, divides_eval, rename_eval, bind]
  have h : (∑ i ∈ range (n.eval input args),
      (if 2 ≤ i then 1 else 0) * (if i ∣ n.eval input args then 1 else 0) : ℕ) = 0 ↔
      ∀ i, 2 ≤ i → i < n.eval input args → ¬ i ∣ n.eval input args := by
    rw [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    constructor
    · intro h i hi hn hd
      have hh := h i (mem_range.mpr hn)
      simp [hi, hd] at hh
    · intro h i hi
      by_cases h2 : 2 ≤ i
      · simp [h2, h i h2 (mem_range.mp hi)]
      · simp [h2]
  have hx : (if 2 ≤ n.eval input args then 1 else 0) *
      (if (∑ i ∈ range (n.eval input args),
        (if 2 ≤ i then 1 else 0)*(if i ∣ n.eval input args then 1 else 0) : ℕ)=0 then 1 else 0) =
        (if (n.eval input args).Prime then 1 else 0) := by
    simp only [h]
    exact (indicator_and _ _).trans (by simp only [Nat.prime_def_lt'])
  exact hx

def powTwo (n : Expr) : Expr := .mul (positive n)
  (.zero (.sum (.add n (.const 1))
    (.mul (prime (.arg 0)) (.mul (divides (.arg 0) (n.rename Nat.succ))
      (.zero (equal (.arg 0) (.const 2)))))))

@[simp] theorem powTwo_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (powTwo n).eval input args = if ∃ k : ℕ, n.eval input args = 2^k then 1 else 0 := by
  let N := n.eval input args
  have h : (∑ i ∈ range (N+1), (if i.Prime then 1 else 0)*
      ((if i ∣ N then 1 else 0)*(if (if i=2 then 1 else 0)=0 then 1 else 0)) : ℕ) = 0 ↔
      ∀ i ≤ N, i.Prime → i ∣ N → i=2 := by
    rw [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    constructor
    · intro h i hi hp hd
      have hh := h i (mem_range.mpr (by omega))
      by_contra hn
      simp [hp,hd,hn] at hh
    · intro h i hi
      by_cases hp : i.Prime <;> by_cases hd : i ∣ N <;> simp_all
      exact h i (by omega) hp hd
  have hh : (N ≠ 0 ∧ ∀ i ≤ N, i.Prime → i ∣ N → i=2) ↔ ∃ k : ℕ, N=2^k := by
    constructor
    · rintro ⟨hn,hp⟩
      exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn (fun {d} hd hdn => hp d (Nat.le_of_dvd (by omega) hdn) hd hdn)⟩
    · rintro ⟨k,hk⟩
      rw [hk]
      refine ⟨by positivity, ?_⟩
      intro i hi hp hd
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
  simp only [powTwo, eval, positive_eval, prime_eval, divides_eval, equal_eval, rename_eval, bind]
  change (if N ≠ 0 then 1 else 0)*(if _=0 then 1 else 0) = if ∃ k, N=2^k then 1 else 0
  have hx : (if N ≠ 0 then 1 else 0)*(if
      (∑ i ∈ range (N+1), (if i.Prime then 1 else 0)*
      ((if i ∣ N then 1 else 0)*(if (if i=2 then 1 else 0)=0 then 1 else 0)) : ℕ) = 0
      then 1 else 0) = (if ∃ k, N=2^k then 1 else 0) := by
    simp only [h]
    exact (indicator_and _ _).trans (by simp only [hh])
  exact hx

def size (n : Expr) : Expr := .sum (.add n (.const 1)) (powTwo (.arg 0))

 theorem count_powers (N : ℕ) :
    (∑ i ∈ range (N+1), if ∃ k : ℕ, i=2^k then (1:ℕ) else 0) = N.size := by
  rw [sum_boole]
  have hb : {i ∈ range (N+1) | ∃ k : ℕ, i=2^k} = (range N.size).image (fun k => 2^k) := by
    ext i
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hi,k,rfl⟩
      exact ⟨k, Nat.lt_size.mpr (by omega), rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨by have := Nat.lt_size.mp hk; omega, k, rfl⟩
  rw [hb, card_image_of_injective _ (by intro a b h; exact (Nat.pow_right_injective (by omega : 2 ≤ 2)) h), card_range, Nat.cast_id]

@[simp] theorem size_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (size n).eval input args = (n.eval input args).size := by
  simp only [size, eval, powTwo_eval, bind]
  exact count_powers (n.eval input args)

def digitPower (n i : Expr) : Expr := .sum (.add n (.const 1))
  (.mul (.arg 0) (.mul (powTwo (.arg 0))
    (equal (size (.arg 0)) (.add (i.rename Nat.succ) (.const 1)))))

 theorem digitPower_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ)
    (hi : i.eval input args < (n.eval input args).size) :
    (digitPower n i).eval input args = 2^(i.eval input args) := by
  simp only [digitPower, eval, powTwo_eval, size_eval, equal_eval, rename_eval, bind]
  let N := n.eval input args
  let I := i.eval input args
  have hpow : 2^I ∈ range (N+1) := mem_range.mpr (by have hh := Nat.lt_size.mp hi; change 2^I ≤ N at hh; omega)
  rw [sum_eq_single_of_mem (2^I) hpow]
  · simp [Nat.size_pow, I]
  · intro b hb hne
    by_cases hp : ∃ k : ℕ, b=2^k
    · obtain ⟨k,rfl⟩ := hp
      have hk : k ≠ I := by rintro rfl; exact hne rfl
      simp only [Nat.size_pow, Nat.add_right_cancel_iff]
      have hk' : k ≠ i.eval input (fun j => args j) := hk
      simp [hk']
    · simp [hp]

def digit (n i : Expr) : Expr := remainder (quotient n (digitPower n i)) (.const 2)

 theorem digit_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ)
    (hi : i.eval input args < (n.eval input args).size) :
    (digit n i).eval input args = n.eval input args / 2^(i.eval input args) % 2 := by
  simp [digit, eval, digitPower_eval n i input args hi]

end IndependentSetsCut.CounterMachine.Expr

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_FramedLen
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine
open scoped BigOperators
namespace Expr

def framedLen (n : Expr) : Expr := .add (.mul (.const 2) (size n)) (.const 1)
def framedBit (n i : Expr) : Expr := cond (lt i (.mul (.const 2) (size n)))
  (cond (equal (remainder i (.const 2)) (.const 0)) (.const 1)
    (digit n (quotient i (.const 2)))) (.const 0)

@[simp] theorem framedLen_eval (n : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (framedLen n).eval input args = 2*(n.eval input args).size+1 := by
  simp [framedLen, eval]

 theorem framedBit_eval (n i : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (framedBit n i).eval input args =
      if i.eval input args < 2*(n.eval input args).size then
        if i.eval input args % 2 = 0 then 1 else n.eval input args / 2^(i.eval input args/2) % 2
      else 0 := by
  simp only [framedBit, cond_eval, lt_eval, eval, equal_eval, remainder_eval, size_eval]
  by_cases hi : i.eval input args < 2*(n.eval input args).size
  · simp only [hi, ↓reduceIte]
    by_cases h2 : i.eval input args % 2 = 0
    · simp [h2]
    · simp only [h2, ↓reduceIte]
      have hsmall : (quotient i (.const 2)).eval input args < (n.eval input args).size := by
        simp only [quotient_eval, eval]; omega
      simpa [quotient_eval, eval] using digit_eval n (quotient i (.const 2)) input args hsmall
  · simp [hi]
end Expr

end IndependentSetsCut.CounterMachine

namespace IndependentSetsCut.CounterMachine.Expr

section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

def listSum {I : Type} (l : List I) (f : I → Expr) : Expr :=
  l.foldr (fun i s => .add (f i) s) (.const 0)
@[simp] theorem listSum_eval {I : Type} (l : List I) (f : I → Expr)
    (input : List Bool) (args : ℕ → ℕ) :
    (listSum l f).eval input args = (l.map (fun i => (f i).eval input args)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (f i).eval input args + (listSum l f).eval input args = _
    simp [ih]

def least (bound predicate : Expr) : Expr :=
  .sum bound (.mul (.arg 0) (.mul (positive predicate)
    (.zero (.sum (.arg 0) (positive (predicate.rename (fun
      | 0 => 0
      | j+1 => j+2)))))))

 theorem least_eval (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (least bound predicate).eval input args =
      ∑ i ∈ range (bound.eval input args),
        if predicate.eval input (bind args i) ≠ 0 ∧
          ∀ j < i, predicate.eval input (bind args j) = 0 then i else 0 := by
  have hb (i j : ℕ) : (fun k => bind (bind args i) j (match k with
      | 0 => 0
      | k+1 => k+2)) = bind args j := by
    funext k; cases k <;> rfl
  simp only [least, eval, positive_eval, rename_eval, hb]
  apply sum_congr rfl
  intro i hi
  have hz : (∑ j ∈ range i,
      if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0) = 0 ↔
      ∀ j < i, predicate.eval input (bind args j)=0 := by
    simp only [sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _), mem_range]
    simp
  change i * ((if predicate.eval input (bind args i) ≠ 0 then 1 else 0) *
    (if (∑ j ∈ range i, if predicate.eval input (bind args j) ≠ 0 then (1:ℕ) else 0)=0 then 1 else 0)) = _
  simp only [hz]
  rw [indicator_and]
  split_ifs <;> simp

end

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem least_eq (bound predicate : Expr) (input : List Bool) (args : ℕ → ℕ) (k : ℕ)
    (hk : k < bound.eval input args)
    (hp : predicate.eval input (bind args k) ≠ 0)
    (he : ∀ j < k, predicate.eval input (bind args j) = 0) :
    (least bound predicate).eval input args = k := by
  rw [least_eval, sum_eq_single_of_mem k (mem_range.mpr hk)]
  · exact ite_eq_left ⟨hp, he⟩
  · intro j hj hne
    by_cases h : j < k
    · simp [he j h]
    · have hkj : k < j := by omega
      split_ifs with hgood
      · exact False.elim (hp (hgood.2 k hkj))
      · rfl

end IndependentSetsCut.CounterMachine.Expr

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_Represented
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.UnaryTables

section
open scoped BigOperators
open Finset

def offset (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, (f j + 1)

def words (f : ℕ → ℕ) (n : ℕ) : List Bool :=
  ((List.range n).map f).flatMap (fun v => List.replicate v true ++ [false])

lemma offset_succ (f : ℕ → ℕ) (n : ℕ) :
    offset f (n+1) = offset f n + (f n+1) := by simp [offset, sum_range_succ]

lemma offset_mono (f : ℕ → ℕ) : Monotone (offset f) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [offset_succ]
  omega

lemma words_succ (f : ℕ → ℕ) (n : ℕ) :
    words f (n+1) = words f n ++ (List.replicate (f n) true ++ [false]) := by
  simp [words,List.range_succ,List.flatMap_append]

lemma words_length (f : ℕ → ℕ) (n : ℕ) : (words f n).length = offset f n := by
  induction n with
  | zero => simp [words,offset]
  | succ n ih => simp [words_succ,ih,offset_succ]

lemma get_word (v i : ℕ) :
    ((List.replicate v true ++ [false])[i]?).getD false = true ↔ i < v := by
  by_cases h : i < v
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
    simp only [List.length_replicate]
    cases e : i-v with
    | zero => simp [h]
    | succ j => simp [h]

lemma words_bit (f : ℕ → ℕ) (n i : ℕ) :
    ((words f n)[i]?).getD false = true ↔
      ∃ j < n, offset f j ≤ i ∧ i < offset f j + f j := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words_succ]
    by_cases h : i < offset f n
    · rw [List.getElem?_append_left (by simpa [words_length] using h),ih]
      constructor
      · rintro ⟨j,hj,hl,hu⟩; exact ⟨j,Nat.lt_succ_of_lt hj,hl,hu⟩
      · rintro ⟨j,hj,hl,hu⟩
        have hj' : j < n := by
          by_contra hn
          have : j = n := by omega
          subst j
          omega
        exact ⟨j,hj',hl,hu⟩
    · rw [List.getElem?_append_right (by simpa [words_length] using Nat.le_of_not_gt h),
        words_length,get_word]
      constructor
      · intro hi; exact ⟨n,by omega,by omega,by omega⟩
      · rintro ⟨j,hj,hl,hu⟩
        have hjn : j = n := by
          by_contra hne
          have hj' : j+1 ≤ n := by omega
          have hp := offset_mono f hj'
          rw [offset_succ] at hp
          omega
        subst j
        omega

lemma indicator_exists (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (∑ j ∈ range n, if p j then 1 else 0) ≠ 0 ↔ ∃ j < n, p j := by
  rw [← Nat.pos_iff_ne_zero,Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_range]
  constructor
  · rintro ⟨j,hj,hv⟩
    exact ⟨j,hj,by by_contra hp; simp [hp] at hv⟩
  · rintro ⟨j,hj,hp⟩
    exact ⟨j,hj,by simp [hp]⟩

open scoped BigOperators
open Finset
open IndependentSetsCut.CounterMachine.Expr

def atIndex (v i : Expr) : Expr := v.subst (fun _ => i)
def closed (n : Expr) : Expr := atIndex n (.const 0)
def totalLength (n v : Expr) : Expr :=
  .sum (closed n) (.add (atIndex v (.arg 0)) (.const 1))
def startOffset (v : Expr) : Expr :=
  .sum (.arg 0) (.add (atIndex v (.arg 0)) (.const 1))
def wordBit (n v : Expr) : Expr :=
  .sum (closed n) (.mul (Expr.le (startOffset v) (.arg 1))
    (Expr.lt (.arg 1) (.add (startOffset v) (atIndex v (.arg 0)))))

@[simp] lemma atIndex_eval (v i : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (atIndex v i).eval s a = v.eval s (fun _ => i.eval s a) := by
  simp [atIndex]
@[simp] lemma closed_eval (n : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (closed n).eval s a = n.eval s (fun _ => 0) := by simp [closed,Expr.eval]
@[simp] lemma totalLength_eval (n v : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (totalLength n v).eval s a = offset (fun j => v.eval s (fun _ => j))
      (n.eval s (fun _ => 0)) := by
  simp [totalLength,Expr.eval,Expr.bind,offset]
@[simp] lemma startOffset_eval (v : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (startOffset v).eval s a = offset (fun j => v.eval s (fun _ => j)) (a 0) := by
  simp [startOffset,Expr.eval,Expr.bind,offset]
lemma wordBit_eval (n v : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (wordBit n v).eval s a = ∑ j ∈ range (n.eval s (fun _ => 0)),
      if offset (fun j => v.eval s (fun _ => j)) j ≤ a 0 ∧
        a 0 < offset (fun j => v.eval s (fun _ => j)) j + v.eval s (fun _ => j)
      then 1 else 0 := by
  simp only [wordBit,Expr.eval,closed_eval,Expr.le_eval,Expr.lt_eval,
    startOffset_eval,atIndex_eval,Expr.bind,Expr.indicator_and]

lemma table_eq_words (n v : Expr) (s : List Bool) :
    table (totalLength n v) (wordBit n v) s =
      words (fun j => v.eval s (fun _ => j)) (n.eval s (fun _ => 0)) := by
  apply List.ext_getElem
  · simp [table,words_length]
  · intro i hi hj
    simp only [table,List.getElem_ofFn]
    have hw := words_bit (fun j => v.eval s (fun _ => j)) (n.eval s (fun _ => 0)) i
    rw [List.getElem?_eq_getElem hj,Option.getD_some] at hw
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq,wordBit_eval,indicator_exists] using hw.symm

noncomputable def computer (n v : Expr) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun s => words (fun j => v.eval s (fun _ => j)) (n.eval s (fun _ => 0))) where
  tm := (tableComputer (totalLength n v) (wordBit n v)).tm
  inputAlphabet := (tableComputer (totalLength n v) (wordBit n v)).inputAlphabet
  outputAlphabet := (tableComputer (totalLength n v) (wordBit n v)).outputAlphabet
  time := (tableComputer (totalLength n v) (wordBit n v)).time
  outputsFun s := by
    simpa only [table_eq_words] using
      (tableComputer (totalLength n v) (wordBit n v)).outputsFun s

end

noncomputable def encodedComputer {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (n v : Expr)
    (spec : ∀ a, words (fun j => v.eval (ea a) (fun _ => j))
      (n.eval (ea a) (fun _ => 0)) = eb (f a)) :
    Turing.TM2ComputableInPolyTime ea eb f where
  tm := (computer n v).tm
  inputAlphabet := (computer n v).inputAlphabet
  outputAlphabet := (computer n v).outputAlphabet
  time := (computer n v).time
  outputsFun a := by simpa only [spec, id_eq] using (computer n v).outputsFun (ea a)

end IndependentSetsCut.CounterMachine.UnaryTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_ExprDrop
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators

def dropInput (offset : Expr) : Expr → Expr
  | .const n => .const n
  | .arg i => .arg i
  | .length => .sub .length (UnaryTables.closed offset)
  | .bit x => .bit (.add (UnaryTables.closed offset) (dropInput offset x))
  | .add x y => .add (dropInput offset x) (dropInput offset y)
  | .sub x y => .sub (dropInput offset x) (dropInput offset y)
  | .mul x y => .mul (dropInput offset x) (dropInput offset y)
  | .zero x => .zero (dropInput offset x)
  | .sum b f => .sum (dropInput offset b) (dropInput offset f)

lemma dropInput_eval (offset e : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (dropInput offset e).eval s a=e.eval (s.drop (offset.eval s (fun _ => 0))) a := by
  have hc (a : ℕ → ℕ) : (UnaryTables.closed offset).eval s a=offset.eval s (fun _ => 0) := by
    simp [UnaryTables.closed,UnaryTables.atIndex,eval]
  induction e generalizing a with
  | const n => rfl
  | arg n => rfl
  | length => simp [dropInput,eval,hc]
  | bit e ih => simp [dropInput,eval,hc,ih,List.getElem?_drop]
  | add x y ix iy => simp [dropInput,eval,ix,iy]
  | sub x y ix iy => simp [dropInput,eval,ix,iy]
  | mul x y ix iy => simp [dropInput,eval,ix,iy]
  | zero x ix => simp [dropInput,eval,ix]
  | sum b f ib iF => simp only [dropInput,eval,ib,iF]

end IndependentSetsCut.CounterMachine.Expr

namespace IndependentSetsCut.CounterMachine.UnaryTables
lemma words_add (f : ℕ → ℕ) (a b : ℕ) :
    words f (a+b)=words f a ++ words (fun w => f (a+w)) b := by
  induction b with
  | zero => simp [words]
  | succ b ih => rw [Nat.add_succ,words_succ,ih,words_succ,List.append_assoc]
end IndependentSetsCut.CounterMachine.UnaryTables

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Reduction_StoredFloyd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.UnaryTables
lemma wordValue_words (f : ℕ → ℕ) (n k : ℕ) (h : k<n) :
    Expr.wordValue (words f n) k = f k := by
  change Expr.wordValue (Expr.unaryWords ((List.range n).map f)) k = _
  rw [Expr.wordValue_encoded]
  simp [h]

lemma words_congr {f g : ℕ → ℕ} {n : ℕ} (h : ∀ j<n, f j=g j) : words f n=words g n := by
  unfold words
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)
end IndependentSetsCut.CounterMachine.UnaryTables

namespace LargeIndependentSets.StoredFloyd
open ShortestPaths
open IndependentSetsCut.CounterMachine

structure State (B : ℕ) where
  n : ℕ
  k : ℕ
  matrix : Capped.Matrix B n

def entry {B n : ℕ} (a : Capped.Matrix B n) (i j : ℕ) : ℕ :=
  if hi : i<n then if hj : j<n then (a.get ⟨i,hi⟩ ⟨j,hj⟩).val else 0 else 0

@[simp] lemma entry_fin {B n : ℕ} (a : Capped.Matrix B n) (i j : Fin n) :
    entry a i.val j.val = (a.get i j).val := by simp [entry,i.isLt,j.isLt]

def State.value {B : ℕ} (s : State B) (w : ℕ) : ℕ :=
  if w=0 then s.n else if w=1 then s.k else
    entry s.matrix ((w-2)/s.n) ((w-2)%s.n)

def State.bits {B : ℕ} (s : State B) : List Bool :=
  IndependentSetsCut.CounterMachine.UnaryTables.words s.value (2+s.n*s.n)

@[simp] lemma read_n {B : ℕ} (s : State B) : Expr.wordValue s.bits 0 = s.n := by
  rw [State.bits,IndependentSetsCut.CounterMachine.UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]
@[simp] lemma read_k {B : ℕ} (s : State B) : Expr.wordValue s.bits 1 = s.k := by
  rw [State.bits,IndependentSetsCut.CounterMachine.UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]

def sizeExpr : Expr := Expr.word (.const 0)
def pivotExpr : Expr := Expr.word (.const 1)
def cellExpr (i j : Expr) : Expr :=
  Expr.word (.add (.const 2) (.add (.mul i sizeExpr) j))
def minExpr (a b : Expr) : Expr := .sub a (.sub a b)
def countExpr : Expr := .add (.const 2) (.mul sizeExpr sizeExpr)

@[simp] lemma sizeExpr_eval {B : ℕ} (s : State B) (args : ℕ → ℕ) :
    sizeExpr.eval s.bits args = s.n := by simp [sizeExpr,Expr.eval]
@[simp] lemma pivotExpr_eval {B : ℕ} (s : State B) (args : ℕ → ℕ) :
    pivotExpr.eval s.bits args = s.k := by simp [pivotExpr,Expr.eval]
@[simp] lemma cellExpr_eval (i j : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (cellExpr i j).eval s args = Expr.wordValue s
      (2+i.eval s args*sizeExpr.eval s args+j.eval s args) := by
  simp [cellExpr,Expr.eval,Nat.add_assoc]
@[simp] lemma minExpr_eval (a b : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (minExpr a b).eval s args = min (a.eval s args) (b.eval s args) := by
  simp only [minExpr,Expr.eval]; omega
@[simp] lemma countExpr_eval {B : ℕ} (s : State B) (args : ℕ → ℕ) :
    countExpr.eval s.bits args = 2+s.n*s.n := by simp [countExpr,Expr.eval]

end LargeIndependentSets.StoredFloyd

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_PCP_LCTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargeIndependentSets.UniformLC
open IndependentSetsCut.CounterMachine
open scoped Classical BigOperators
noncomputable section

structure Table (L R : Type) where
  nu : ℕ
  nv : ℕ
  ne : ℕ
  hu : 0 < nu
  hv : 0 < nv
  he : 0 < ne
  left : Fin ne → Fin nu
  right : Fin ne → Fin nv
  project : Fin ne → L → R

variable {L R : Type} [Fintype L] [Fintype R]

def projectCode (f : L → R) : ℕ := (Fintype.equivFin (L → R) f).val

def Table.value (t : Table L R) (w : ℕ) : ℕ :=
  if w=0 then t.nu else if w=1 then t.nv else if w=2 then t.ne else
    if h : (w-3)/3 < t.ne then
      if (w-3)%3=0 then (t.left ⟨(w-3)/3,h⟩).val
      else if (w-3)%3=1 then (t.right ⟨(w-3)/3,h⟩).val
      else projectCode (t.project ⟨(w-3)/3,h⟩)
    else 0

def Table.bits (t : Table L R) := UnaryTables.words t.value (3+3*t.ne)

@[simp] lemma read_nu (t : Table L R) : Expr.wordValue t.bits 0=t.nu := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [Table.value]
@[simp] lemma read_nv (t : Table L R) : Expr.wordValue t.bits 1=t.nv := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [Table.value]
@[simp] lemma read_ne (t : Table L R) : Expr.wordValue t.bits 2=t.ne := by
  rw [Table.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [Table.value]

def nuExpr : Expr := Expr.word (.const 0)
def nvExpr : Expr := Expr.word (.const 1)
def neExpr : Expr := Expr.word (.const 2)

@[simp] lemma nuExpr_eval (t : Table L R) (a : ℕ → ℕ) : nuExpr.eval t.bits a=t.nu := by simp [nuExpr,Expr.eval]
@[simp] lemma nvExpr_eval (t : Table L R) (a : ℕ → ℕ) : nvExpr.eval t.bits a=t.nv := by simp [nvExpr,Expr.eval]
@[simp] lemma neExpr_eval (t : Table L R) (a : ℕ → ℕ) : neExpr.eval t.bits a=t.ne := by simp [neExpr,Expr.eval]

end
end LargeIndependentSets.UniformLC

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators

def finLookup {m : ℕ} (f : Fin m → ℕ) (x : Expr) : Expr :=
  listSum (List.finRange m) (fun i => .mul (equal x (.const i.val)) (.const (f i)))

lemma finLookup_eval {m : ℕ} (f : Fin m → ℕ) (x : Expr) (s : List Bool) (a : ℕ → ℕ)
    (i : Fin m) (hi : x.eval s a=i.val) :
    (finLookup f x).eval s a=f i := by
  simp only [finLookup,listSum_eval,eval,equal_eval,hi,ite_mul,one_mul,zero_mul]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  simp [Fin.val_inj]

noncomputable def staticLookup {α : Type} [Fintype α] (f : α → ℕ) (x : Expr) : Expr :=
  finLookup (fun i => f ((Fintype.equivFin α).symm i)) x

lemma staticLookup_eval {α : Type} [Fintype α] (f : α → ℕ) (x : Expr)
    (s : List Bool) (a : ℕ → ℕ) (v : α) (hv : x.eval s a=(Fintype.equivFin α v).val) :
    (staticLookup f x).eval s a=f v := by
  rw [staticLookup,finLookup_eval _ _ _ _ _ hv,Equiv.symm_apply_apply]

def listAll {α : Type} (xs : List α) (f : α → Expr) : Expr :=
  .zero (listSum xs (fun a => .zero (f a)))

lemma listAll_eval {α : Type} (xs : List α) (f : α → Expr) (s : List Bool) (a : ℕ → ℕ) :
    (listAll xs f).eval s a = if ∀ x ∈ xs, (f x).eval s a≠0 then 1 else 0 := by
  simp only [listAll,eval,listSum_eval]
  congr 1
  simp only [List.sum_eq_zero_iff,List.mem_map,forall_exists_index,and_imp]
  simp

end IndependentSetsCut.CounterMachine.Expr

end OAI
end

section
-- module Solutions.OAIQ069_INDEP.IndependentSets_Machines_ExprTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr

section
open scoped BigOperators

def finTable2 {m n : ℕ} (f : Fin m → Fin n → ℕ) (x y : Expr) : Expr :=
  finLookup (fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (.add y (.mul (.const n) x))
lemma finTable2_eval {m n : ℕ} (f : Fin m → Fin n → ℕ) (x y : Expr) (s : List Bool)
    (a : ℕ → ℕ) (i : Fin m) (j : Fin n) (hi : x.eval s a=i.val) (hj : y.eval s a=j.val) :
    (finTable2 f x y).eval s a=f i j := by
  unfold finTable2
  rw [finLookup_eval _ _ _ _ (finProdFinEquiv (i,j)) (by simp [eval,hi,hj])]
  rw [Equiv.symm_apply_apply]

def finTable3 {l m n : ℕ} (f : Fin l → Fin m → Fin n → ℕ) (x y z : Expr) : Expr :=
  finTable2 (fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (.add y (.mul (.const m) x)) z
lemma finTable3_eval {l m n : ℕ} (f : Fin l → Fin m → Fin n → ℕ) (x y z : Expr) (s : List Bool)
    (a : ℕ → ℕ) (i : Fin l) (j : Fin m) (k : Fin n)
    (hi : x.eval s a=i.val) (hj : y.eval s a=j.val) (hk : z.eval s a=k.val) :
    (finTable3 f x y z).eval s a=f i j k := by
  unfold finTable3
  rw [finTable2_eval _ _ _ _ _ (finProdFinEquiv (i,j)) k (by simp [eval,hi,hj]) hk]
  rw [Equiv.symm_apply_apply]

noncomputable def static2 {α β : Type} [Fintype α] [Fintype β]
    (f : α → β → ℕ) (x y : Expr) : Expr :=
  finTable2 (fun i j => f ((Fintype.equivFin α).symm i) ((Fintype.equivFin β).symm j)) x y
lemma static2_eval {α β : Type} [Fintype α] [Fintype β]
    (f : α → β → ℕ) (x y : Expr) (s : List Bool) (a : ℕ → ℕ) (i : α) (j : β)
    (hi : x.eval s a=(Fintype.equivFin α i).val) (hj : y.eval s a=(Fintype.equivFin β j).val) :
    (static2 f x y).eval s a=f i j := by
  rw [static2,finTable2_eval _ _ _ _ _ _ _ hi hj]
  simp

noncomputable def static3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℕ) (x y z : Expr) : Expr :=
  finTable3 (fun i j k => f ((Fintype.equivFin α).symm i) ((Fintype.equivFin β).symm j)
    ((Fintype.equivFin γ).symm k)) x y z
lemma static3_eval {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℕ) (x y z : Expr) (s : List Bool) (a : ℕ → ℕ) (i : α) (j : β) (k : γ)
    (hi : x.eval s a=(Fintype.equivFin α i).val) (hj : y.eval s a=(Fintype.equivFin β j).val)
    (hk : z.eval s a=(Fintype.equivFin γ k).val) :
    (static3 f x y z).eval s a=f i j k := by
  rw [static3,finTable3_eval _ _ _ _ _ _ _ _ _ hi hj hk]
  simp

lemma sum_ne_zero (bound body : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (Expr.sum bound body).eval s a≠0 ↔
      ∃ i<bound.eval s a, body.eval s (bind a i)≠0 := by
  simp only [eval,ne_eq,Finset.sum_eq_zero_iff,Finset.mem_range]
  push Not
  rfl

lemma listSum_ne_zero {α : Type} (xs : List α) (f : α → Expr) (s : List Bool) (a : ℕ → ℕ) :
    (listSum xs f).eval s a≠0 ↔ ∃ x ∈ xs, (f x).eval s a≠0 := by
  rw [listSum_eval]
  simp only [ne_eq,List.sum_eq_zero_iff,List.mem_map,forall_exists_index,and_imp]
  push Not
  simp

end
open scoped Classical BigOperators
noncomputable section

def pick {α : Type} [Fintype α] (f : α → ℕ) (pred : α → Expr) : Expr :=
  listSum (List.finRange (Fintype.card α)) fun i =>
    .mul (positive (pred ((Fintype.equivFin α).symm i))) (.const (f ((Fintype.equivFin α).symm i)))

lemma pick_eval {α : Type} [Fintype α] (f : α → ℕ) (pred : α → Expr)
    (s : List Bool) (a : ℕ → ℕ) (v : α)
    (hv : ∀ x, (pred x).eval s a ≠ 0 ↔ x=v) :
    (pick f pred).eval s a=f v := by
  have hp : ∀ x, (positive (pred x)).eval s a=if x=v then 1 else 0 := by
    intro x
    rw [positive_eval]
    by_cases h : x=v
    · simp [h,(hv v).mpr rfl]
    · have hz : (pred x).eval s a=0 := by by_contra hh; exact h ((hv x).mp hh)
      simp [h,hz]
  simp only [pick,listSum_eval,eval,hp,ite_mul,one_mul,zero_mul]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  have he : ∀ i : Fin (Fintype.card α), (Fintype.equivFin α).symm i=v ↔ i=Fintype.equivFin α v := by
    intro i
    exact Equiv.symm_apply_eq (Fintype.equivFin α)
  simp only [he]
  simp

end
end IndependentSetsCut.CounterMachine.Expr

end OAI
end


