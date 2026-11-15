-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_SourceInstructionMapper
-- name    : QMAPerfectCompleteness_Proof_SourceInstructionMapper
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:17:27.401219+00:00
-- url     : https://prove2.me/theorems/491cee6e-4f7c-4e50-a6ce-a14b7e9f9a4d
-- title:
--   Parsing and remapping source instructions
-- statement:
--   Defines finite programs that parse each G2 tag, dispatch to its unary address fields and evaluate a recipe expression on every source wire. The output instruction has the mapped addresses, with clean parser/evaluator scratch and explicit runtime and output-length bounds.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/SourceInstructionMapper.lean, retained declaration span lines 15–210.

/- Generated from Solutions.SourceInstructionMapper by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BoundedWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitExprTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ConditionalWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeWriterContext
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryDispatch
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Actual finite per-instruction programs for arbitrary recipe address expressions. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity.StructuredStack
open Code
noncomputable section

def addressCost (e : Expr) (d : ℕ) : ℕ := (e.evaluator d).cost+2*(e.evaluator d).growth+6

lemma oneAddress_bounded_exec (e : Expr) (d : ℕ) (x : Context d) (B w : ℕ) (hx : x.Valid B) (hw : w≤B)
    (tail : Str) (S : K e d → Str) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=x.encode a)
    (hparse : S (input e d)=encNat w++tail) (ha : S (address e d)=[])
    (heval : ∀ j,S (evalEmb e d (.inr j))=[]) :
    (oneAddress e d).Exec (q,S)
      (none,Function.update (Function.update S (input e d) tail) (output e d)
        ((encNat (mappedWire e x w)).reverse++S (output e d))) (addressCost e d*(B+1)) := by
  exact exec_mono _ (oneAddress_exec e d x B w hx hw tail S q hin hparse ha heval)
    (by unfold addressCost; nlinarith)

def repeatCode {A : Type} (P : Code A) : ℕ → Code A
  | 0 => load none
  | k+1 => seq P (repeatCode P k)

def mappedFields {d : ℕ} (e : Expr) (x : Context d) (ws : List ℕ) : Str :=
  ws.flatMap (fun w=>encNat (mappedWire e x w))

lemma manyAddresses_exec (e : Expr) (d : ℕ) (x : Context d) (B : ℕ) (hx : x.Valid B) (ws : List ℕ)
    (hws : ∀ w∈ws,w≤B) (tail : Str) (S : K e d → Str) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=x.encode a)
    (hparse : S (input e d)=ws.flatMap encNat++tail) (ha : S (address e d)=[])
    (heval : ∀ j,S (evalEmb e d (.inr j))=[]) :
    (repeatCode (oneAddress e d) ws.length).Exec (q,S)
      (none,Function.update (Function.update S (input e d) tail) (output e d)
        ((mappedFields e x ws).reverse++S (output e d)))
      (ws.length*addressCost e d*(B+1)+1) := by
  induction ws generalizing S q with
  | nil =>
    have he : Function.update (Function.update S (input e d) tail) (output e d)
        ((mappedFields e x []).reverse++S (output e d))=S := by
      funext k
      by_cases hi : k=input e d <;> by_cases ho : k=output e d <;>
        simp_all [mappedFields,input,output,scratch]
    simpa only [repeatCode,List.length_nil,Nat.zero_mul,Nat.zero_add,he] using load_exec none (q,S)
  | cons w ws ih =>
    have hw : w≤B := hws w (by simp)
    have htail : ∀ v∈ws,v≤B := by intro v hv; exact hws v (by simp [hv])
    have hp : S (input e d)=encNat w++(ws.flatMap encNat++tail) := by
      simpa only [List.flatMap_cons,List.append_assoc] using hparse
    have h0 := oneAddress_bounded_exec e d x B w hx hw (ws.flatMap encNat++tail) S q hin hp ha heval
    let S0 := Function.update (Function.update S (input e d) (ws.flatMap encNat++tail))
      (output e d) ((encNat (mappedWire e x w)).reverse++S (output e d))
    have hin0 : ∀ a,S0 (.inl a)=x.encode a := by
      intro a; simpa [S0,input,output,scratch] using hin a
    have hp0 : S0 (input e d)=ws.flatMap encNat++tail := by simp [S0,input,output,scratch]
    have ha0 : S0 (address e d)=[] := by simpa [S0,input,address,output,scratch] using ha
    have he0 : ∀ j,S0 (evalEmb e d (.inr j))=[] := by
      intro j
      simpa only [S0,Function.update_of_ne (evalWork_ne_output e d j),
        Function.update_of_ne (evalWork_ne_scratch e d j 0)] using heval j
    have h1 := ih htail S0 none hin0 hp0 ha0 he0
    have h := seq_exec _ _ h0 h1
    have he : Function.update (Function.update S0 (input e d) tail) (output e d)
        ((mappedFields e x ws).reverse++S0 (output e d)) =
        Function.update (Function.update S (input e d) tail) (output e d)
          ((mappedFields e x (w::ws)).reverse++S (output e d)) := by
      funext k
      by_cases hi : k=input e d <;> by_cases ho : k=output e d <;>
        simp_all [S0,mappedFields,List.reverse_append,List.append_assoc,input,output,scratch]
    rw [he] at h
    change (repeatCode (oneAddress e d) (w::ws).length).Exec (q,S) _ _ at h
    convert h using 1 <;> simp only [List.length_cons] <;> ring

def readTag (e : Expr) (d : ℕ) : Code (K e d) :=
  seq (readField (input e d) (tag e d))
    (seq (copy (tag e d) (output e d) (temporary e d)) (push (output e d) false))

lemma readTag_exec (e : Expr) (d : ℕ) (g : ℕ) (tail : Str) (S : K e d → Str) (q : Option Bool)
    (hparse : S (input e d)=encNat g++tail) (htag : S (tag e d)=[]) (htmp : S (temporary e d)=[]) :
    (readTag e d).Exec (q,S)
      (none,Function.update (Function.update (Function.update S (input e d) tail) (tag e d) (unary g))
        (output e d) ((encNat g).reverse++S (output e d))) (6*g+6) := by
  let S0 := Function.update (Function.update S (input e d) tail) (tag e d) (unary g)
  have h0 := readField_exec (input e d) (tag e d) (scratch_ne e d 0 3 (by decide)) g tail S q hparse
  have h0' : (readField (input e d) (tag e d)).Exec (q,S) (none,S0) (2*g+3) := by
    simpa only [htag,List.append_nil,unary,S0] using h0
  have h1 := copy_exec (tag e d) (output e d) (temporary e d)
    (by simp [tag,output,scratch]) (scratch_ne e d 3 2 (by decide))
    (by simp [temporary,output,scratch]) (unary g) S0 none (by simp [S0])
    (by simpa [S0,input,tag,temporary,scratch] using htmp)
  let S1 := Function.update S0 (output e d) (unary g++S (output e d))
  have hout : S0 (output e d)=S (output e d) := by simp [S0,input,tag,output,scratch]
  simp only [unary,List.reverse_replicate,List.length_replicate,hout] at h1
  have h2 := push_exec (output e d) false (none,S1)
  have h := seq_exec _ _ h0' (seq_exec _ _ h1 h2)
  have he : Function.update S1 (output e d) (false::S1 (output e d)) =
      Function.update S0 (output e d) ((encNat g).reverse++S (output e d)) := by
    simp [S1,unary,encNat]
  rw [he] at h
  change (readTag e d).Exec (q,S) _ _ at h
  convert h using 1 <;> ring



def sourceArity (g : ℕ) : ℕ := RawEncoding.g2Table[g]?.getD 0

def gateCode (e : Expr) (d : ℕ) : Code (K e d) :=
  seq (readTag e d) (selectUnary (tag e d) (load none)
    [repeatCode (oneAddress e d) 1,repeatCode (oneAddress e d) 2,
      repeatCode (oneAddress e d) 3,repeatCode (oneAddress e d) 2])

def mappedInstruction {d : ℕ} (e : Expr) (x : Context d) (i : RawEncoding.Instruction) : RawEncoding.Instruction :=
  {i with wires := i.wires.map (mappedWire e x)}

def gateCost (e : Expr) (d : ℕ) : ℕ := 3*addressCost e d+40

def gateGrowth (e : Expr) (d : ℕ) : ℕ := 3*(e.evaluator d).growth+8

lemma sourceArity_le (g : ℕ) (hg : g<4) : sourceArity g≤3 := by
  interval_cases g <;> decide

lemma gateCode_exec (e : Expr) (d : ℕ) (x : Context d) (B : ℕ) (hx : x.Valid B)
    (i : RawEncoding.Instruction) (hi : i.gate<4) (hilen : i.wires.length=sourceArity i.gate)
    (hiwire : ∀ w∈i.wires,w≤B) (tail : Str) (S : K e d → Str) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=x.encode a) (hparse : S (input e d)=i.encode++tail)
    (htag : S (tag e d)=[]) (htmp : S (temporary e d)=[]) (ha : S (address e d)=[])
    (heval : ∀ j,S (evalEmb e d (.inr j))=[]) :
    (gateCode e d).Exec (q,S)
      (none,Function.update (Function.update S (input e d) tail) (output e d)
        ((mappedInstruction e x i).encode.reverse++S (output e d)))
      (gateCost e d*(B+1)) := by
  have hp : S (input e d)=encNat i.gate++(i.wires.flatMap encNat++tail) := by
    simpa only [RawEncoding.Instruction.encode,List.append_assoc] using hparse
  have h0 := readTag_exec e d i.gate (i.wires.flatMap encNat++tail) S q hp htag htmp
  let S0 := Function.update (Function.update (Function.update S (input e d)
    (i.wires.flatMap encNat++tail)) (tag e d) (unary i.gate)) (output e d)
      ((encNat i.gate).reverse++S (output e d))
  let S1 := Function.update S0 (tag e d) []
  have hin1 : ∀ a,S1 (.inl a)=x.encode a := by
    intro a; simpa [S1,S0,input,tag,output,scratch] using hin a
  have hp1 : S1 (input e d)=i.wires.flatMap encNat++tail := by simp [S1,S0,input,tag,output,scratch]
  have ha1 : S1 (address e d)=[] := by simpa [S1,S0,input,address,tag,output,scratch] using ha
  have he1 : ∀ j,S1 (evalEmb e d (.inr j))=[] := by
    intro j
    simpa only [S1,S0,Function.update_of_ne (evalWork_ne_scratch e d j 3),
      Function.update_of_ne (evalWork_ne_output e d j),
      Function.update_of_ne (evalWork_ne_scratch e d j 0)] using heval j
  let endS := Function.update (Function.update S1 (input e d) tail) (output e d)
    ((mappedFields e x i.wires).reverse++S1 (output e d))
  have hbody : ∀ q,(repeatCode (oneAddress e d) i.wires.length).Exec (q,S1) (none,endS)
      (i.wires.length*addressCost e d*(B+1)+1) := by
    intro q
    exact manyAddresses_exec e d x B hx i.wires hiwire tail S1 q hin1 hp1 ha1 he1
  have hget : [repeatCode (oneAddress e d) 1,repeatCode (oneAddress e d) 2,
      repeatCode (oneAddress e d) 3,repeatCode (oneAddress e d) 2][i.gate]? =
      some (repeatCode (oneAddress e d) i.wires.length) := by
    rw [hilen]
    rcases i with ⟨g,ws⟩
    interval_cases g <;> rfl
  have h1 := selectUnary_exec (tag e d) (load none) i.gate _ _ hget S0 none
    (by simp [S0,input,tag,output,scratch]) (none,endS)
    (i.wires.length*addressCost e d*(B+1)+1) hbody
  have h := seq_exec _ _ h0 h1
  have he : endS = Function.update (Function.update S (input e d) tail) (output e d)
      ((mappedInstruction e x i).encode.reverse++S (output e d)) := by
    funext k
    by_cases hk : k=input e d <;> by_cases ht : k=tag e d <;> by_cases ho : k=output e d <;>
      simp_all [endS,S1,S0,mappedInstruction,RawEncoding.Instruction.encode,mappedFields,
        List.flatMap_map,List.reverse_append,List.append_assoc,input,tag,output,scratch]
  rw [he] at h
  apply exec_mono _ (by exact h)
  have hlen := (hilen.le.trans (sourceArity_le i.gate hi))
  have hp := Nat.mul_le_mul_right (B+1) (Nat.mul_le_mul_right (addressCost e d) hlen)
  unfold gateCost
  nlinarith

lemma mappedInstruction_length_le (e : Expr) (d : ℕ) (x : Context d) (B : ℕ) (hx : x.Valid B)
    (i : RawEncoding.Instruction) (hi : i.gate<4) (hilen : i.wires.length=sourceArity i.gate)
    (hiwire : ∀ w∈i.wires,w≤B) :
    (mappedInstruction e x i).encode.length ≤ gateGrowth e d*(B+1) := by
  have hwire (w : ℕ) (hw : w∈i.wires) : mappedWire e x w ≤ (e.evaluator d).growth*(B+1) := by
    rw [← value_values]
    exact (e.evaluator d).bound (values x w) B (values_bound x B w hx (hiwire w hw))
  have hsum : (i.wires.map (fun w=>mappedWire e x w+1)).sum ≤
      i.wires.length*((e.evaluator d).growth*(B+1)+1) := by
    have aux : ∀ ws : List ℕ, (∀ w∈ws,mappedWire e x w≤(e.evaluator d).growth*(B+1)) →
        (ws.map (fun w=>mappedWire e x w+1)).sum ≤ ws.length*((e.evaluator d).growth*(B+1)+1) := by
      intro ws
      induction ws with
      | nil => intro hws; simp
      | cons w ws ih =>
        intro hws
        have ht := hws w (by simp)
        have hs := ih (by intro v hv; exact hws v (by simp [hv]))
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
    exact aux i.wires hwire
  have hlen := hilen.le.trans (sourceArity_le i.gate hi)
  have hp := Nat.mul_le_mul_right ((e.evaluator d).growth*(B+1)+1) hlen
  simp only [mappedInstruction,RawEncoding.Instruction.encode,List.length_append,
    Main.Encoding.encNat_length,List.length_flatMap,List.map_map,Function.comp_def]
  unfold gateGrowth
  nlinarith

end
end QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM


