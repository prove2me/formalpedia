-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding
-- name    : QMAPerfectCompleteness_Proof_VerifierEncoding
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:45:22.377357+00:00
-- url     : https://prove2.me/theorems/affb46e6-776b-4885-911c-86309aeca14a
-- title:
--   Total parsers for unary verifier encodings
-- statement:
--   Defines parsers for unary natural numbers, in-range wire tuples, injectively placed gate instructions, and complete verifier encodings. Encoding identities establish exact parsing with an unconsumed suffix; invalid tags, repeated or out-of-range wires, and malformed fields fail. These algorithms are auxiliary encoding infrastructure and make no runtime claim by themselves.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VerifierEncoding.lean, lines 8–113.

/- Generated from Solutions.VerifierEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes



/-! Total parsers for the exact unary verifier encoding used by the platform.
These algorithms and correctness lemmas do not claim a TM2 runtime theorem. -/
namespace QMAPerfectCompleteness.Main.Encoding
open QAlgorithms.Complexity (Str encNat)

def parseNat : Str → Option (ℕ × Str)
  | [] => none
  | false :: s => some (0, s)
  | true :: s => (parseNat s).map fun p => (p.1 + 1, p.2)

@[simp] theorem parseNat_encode (n : ℕ) (tail : Str) :
    parseNat (encNat n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [encNat, List.replicate_succ, parseNat, List.append_assoc] using ih

/-- Read exactly r in-range wire addresses, leaving the unconsumed suffix. -/
def parseWires (n : ℕ) : (r : ℕ) → Str → Option ((Fin r → Fin n) × Str)
  | 0, s => some (Fin.elim0, s)
  | r + 1, s => do
      let (a, s') ← parseNat s
      if ha : a < n then
        let (t, s'') ← parseWires n r s'
        pure (Fin.cons ⟨a, ha⟩ t, s'')
      else none

def wireCode {n r : ℕ} (t : Fin r → Fin n) : Str :=
  (List.ofFn fun i => encNat (t i).val).flatten

@[simp] theorem parseWires_encode {n : ℕ} (r : ℕ) (t : Fin r → Fin n) (tail : Str) :
    parseWires n r (wireCode t ++ tail) = some (t, tail) := by
  induction r with
  | zero =>
    simp only [wireCode, List.ofFn_zero, List.flatten_nil, List.nil_append, parseWires,
      Option.some.injEq, Prod.mk.injEq, and_true]
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    have hi := ih (fun i => t i.succ)
    simp only [wireCode] at hi
    have hc : Fin.cons (t 0) (fun i => t i.succ) = t := Fin.cons_self_tail t
    simp [wireCode, List.ofFn_succ, List.append_assoc, parseWires, hi, (t 0).isLt, hc]

/-- Parse a gate position and its injective placement. Duplicate or out-of-range wires fail. -/
def parseInstr (G : GateSet) (n : ℕ) (s : Str) : Option (Instr G n × Str) := do
  let (g, s') ← parseNat s
  if hg : g < G.length then
    let (t, s'') ← parseWires n (G.get ⟨g, hg⟩).arity s'
    if ht : Function.Injective t then pure (⟨⟨g, hg⟩, ⟨t, ht⟩⟩, s'') else none
  else none

@[simp] theorem parseInstr_encode {G : GateSet} {n : ℕ} (i : Instr G n) (tail : Str) :
    parseInstr G n (i.encode ++ tail) = some (i, tail) := by
  rcases i with ⟨g, t⟩
  have ht := parseWires_encode (G.get g).arity (t : Fin (G.get g).arity → Fin n) tail
  simp only [wireCode, List.get_eq_getElem] at ht
  simp [parseInstr, Instr.encode, List.append_assoc, g.isLt, ht, t.injective]

/-- Parse a prescribed number of instructions. -/
def parseGateBody (G : GateSet) (n : ℕ) : ℕ → Str → Option (List (Instr G n) × Str)
  | 0, s => some ([], s)
  | r + 1, s => do
      let (i, s') ← parseInstr G n s
      let (is, s'') ← parseGateBody G n r s'
      pure (i :: is, s'')

@[simp] theorem parseGateBody_encode {G : GateSet} {n : ℕ} (gs : List (Instr G n)) (tail : Str) :
    parseGateBody G n gs.length (gs.flatMap Instr.encode ++ tail) = some (gs, tail) := by
  induction gs with
  | nil => rfl
  | cons i gs ih => simp [parseGateBody, List.append_assoc, ih]

def parseGates (G : GateSet) (n : ℕ) (s : Str) : Option (List (Instr G n) × Str) := do
  let (r, s') ← parseNat s
  parseGateBody G n r s'

@[simp] theorem parseGates_encode {G : GateSet} {n : ℕ} (gs : List (Instr G n)) (tail : Str) :
    parseGates G n (encodeGates gs ++ tail) = some (gs, tail) := by
  simp [parseGates, encodeGates, List.append_assoc]

/-- Parse a verifier, including register sizes and the final output-wire address. -/
def parseVerifier (G : GateSet) (s : Str) : Option (Verifier G × Str) := do
  let (m, s') ← parseNat s
  let (a, s'') ← parseNat s'
  let (o, s''') ← parseNat s''
  if ho : o < m + a then
    let (gs, tail) ← parseGates G (m + a) s'''
    pure (⟨m, a, gs, ⟨o, ho⟩⟩, tail)
  else none

@[simp] theorem parseVerifier_encode {G : GateSet} (V : Verifier G) (tail : Str) :
    parseVerifier G (V.encode ++ tail) = some (V, tail) := by
  rcases V with ⟨m, a, gs, o⟩
  simp [parseVerifier, Verifier.encode, List.append_assoc, o.isLt]

def decodeVerifier (G : GateSet) (s : Str) : Option (Verifier G) := do
  let (V, tail) ← parseVerifier G s
  if tail = [] then some V else none

@[simp] theorem decodeVerifier_encode {G : GateSet} (V : Verifier G) :
    decodeVerifier G V.encode = some V := by
  have h := parseVerifier_encode V []
  simp only [List.append_nil] at h
  simp [decodeVerifier, h]



@[simp] theorem encNat_length (n : ℕ) : (encNat n).length = n + 1 := by simp [encNat]













end QMAPerfectCompleteness.Main.Encoding


