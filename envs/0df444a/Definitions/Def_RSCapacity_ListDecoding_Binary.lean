-- Prove2me | Definitions.Def_RSCapacity_ListDecoding_Binary
-- name    : RSCapacity_ListDecoding_Binary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:18.388202+00:00
-- url     : https://prove2.me/theorems/1ca9df5e-3a3d-4af4-afef-0215f85e7f21
-- title:
--   Finite-field tables and deterministic execution contracts
-- statement:
--   Let $F$ be any finite field, with $q=|F|$. A field presentation is a bijection between $F$ and the labels $0,\ldots,q-1$. The public descriptor contains $q$, the labels of zero and one, the complete addition and multiplication tables, and the negation and inversion tables, all in increasing label order. Inversion at zero is represented by zero. No characteristic, arithmetic or decoding oracle is supplied.
--
--   Natural numbers have the self-delimiting binary-alphabet representation $1^a0$. A list is its encoded length followed by its encoded entries. The descriptor has polynomial size in $q$, even with these unary numbers.
--
--   For a finite binary program $P$, input $w$, output relation $R$, and real bound $B$, the execution contract asserts
--   $$\exists t\in\mathbb N:\ P\text{ first halts on }w\text{ at step }t,\quad t\le B,\quad R(\operatorname{out}_t).$$
--   The version without $B$ asserts finite termination with the same exact output relation. These are ordinary predicates on the published three-tape machine's instruction trace. They contain no assumed solver, decoder, correctness result or time bound. Existential programs must separately be syntactically deterministic.
--
--   This interface makes the source's finite-field algorithms and their total running time auditable in one uniform operational model. Every parsing, tape movement, table lookup, intermediate computation and output write must be charged by the execution bound.
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), §1 pp.1–2; Theorem 3.3 p.10; Algorithm 1 p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJSFull_Computation

namespace RSCapacity.ListDecoding

abbrev Bits := FuzzyExtractors.ImprovedJSFull.Bits
abbrev Program := FuzzyExtractors.ImprovedJSFull.Program

/-- Self-delimiting unary natural numbers on the binary alphabet. This
deliberately simple representation has polynomial overhead in field size. -/
def encodeNat (a : ℕ) : Bits := List.replicate a true ++ [false]

def encodeList {α : Type} (encode : α → Bits) (xs : List α) : Bits :=
  encodeNat xs.length ++ xs.flatMap encode

/-- A presentation has only a labelling bijection. All operation tables below
are derived from the field, with no algorithm, correctness or cost witnesses. -/
structure FieldPresentation (F : Type) [Field F] [Fintype F] where
  label : F ≃ Fin (Fintype.card F)

namespace FieldPresentation

variable {F : Type} [Field F] [Fintype F] (P : FieldPresentation F)

def encodeElement (x : F) : Bits := encodeNat (P.label x).val

/-- Fixed order: q, zero, one, addition, multiplication,
negation, inversion. Inversion at zero is the field's total inverse (zero). -/
def encode : Bits :=
  let elements := List.ofFn fun i : Fin (Fintype.card F) => P.label.symm i
  encodeNat (Fintype.card F) ++
    P.encodeElement 0 ++ P.encodeElement 1 ++
    (elements.flatMap fun a => elements.flatMap fun b => P.encodeElement (a + b)) ++
    (elements.flatMap fun a => elements.flatMap fun b => P.encodeElement (a * b)) ++
    elements.flatMap (fun a => P.encodeElement (-a)) ++
    elements.flatMap (fun a => P.encodeElement a⁻¹)

end FieldPresentation

/-- Exact finite execution on the published local-instruction machine.
Determinism is required separately on each existential program. -/
def Executes (P : Program) (input : Bits) (R : Bits → Prop) : Prop :=
  ∃ t : ℕ, FuzzyExtractors.ImprovedJSFull.firstHalt P input (fun _ => false) t ∧
    R (FuzzyExtractors.ImprovedJSFull.readOutput
      (FuzzyExtractors.ImprovedJSFull.run P input (fun _ => false) t) t)

def ExecutesWithin (P : Program) (input : Bits) (bound : ℝ) (R : Bits → Prop) : Prop :=
  ∃ t : ℕ, FuzzyExtractors.ImprovedJSFull.firstHalt P input (fun _ => false) t ∧
    (t : ℝ) ≤ bound ∧
    R (FuzzyExtractors.ImprovedJSFull.readOutput
      (FuzzyExtractors.ImprovedJSFull.run P input (fun _ => false) t) t)

end RSCapacity.ListDecoding


