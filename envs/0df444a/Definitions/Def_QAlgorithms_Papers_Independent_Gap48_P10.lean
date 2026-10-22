-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
-- name    : QAlgorithms_Papers_Independent_Gap48_P10
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:13:18.016799+00:00
-- url     : https://prove2.me/theorems/0825a44f-c6ec-41b0-a31b-c0878a7dc54d
-- title:
--   Definitions for Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators
-- statement:
--   The objects the formalized statements of *Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators* (arXiv:1312.6584) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RealMat`: Fixed three-coordinate Bloch matrix space, equation (12), PDF p.3.
--   - `ParityMat`: Entrywise binary parity matrices, Definitions 4.5-4.9, PDF p.4.
--   - `scalarOmega`: Scalar gate omega I, PDF pp.1-2.
--   - `CliffordLetter`: The T-free generating alphabet of the 192-element group, PDF pp.1-2.
--   - `cliffordLetterMatrix`: Exact matrices of the Clifford generators, PDF pp.1-2.
--   - `cliffordWordMatrix`: Printed-order multiplication, PDF p.2. The empty word denotes I.
--   - `cliffordSet`: The finite Clifford operator set, Definition 2.1, PDF p.2. Positive words generate the stated group because its generators have finite order.
--   - `Clifford`: Terminals identify Clifford operators, never arbitrary spellings, PDF p.2.
--   - `cliffordOfWord`: A Clifford operator constructed from a T-free word, PDF p.2.
--   - `cliffordI`: The distinguished identity terminal, PDF p.2.
--   - `cliffordH`: H as an operator terminal, PDF p.2.
--   - `cliffordSH`: SH as an operator terminal, PDF p.2.
--   - `cliffordHSH`: HSH as an operator terminal, PDF p.12.
--   - `SmallLetter`: Generators of the 64-element subgroup, Definition 2.1, PDF p.2.
--   - `smallLetterMatrix`: Exact subgroup generator matrices, PDF p.2.
--   - `smallSet`: The subgroup S of Definition 2.1, PDF p.2.
--   - `SmallClifford`: Operator-valued terminal in the 64-element subgroup, Definition 2.1, PDF p.2.
--   - `transversal`: Transversal H from Definition 2.1, PDF p.2.
--   - `nonidentityTransversal`: Nonidentity transversal H prime, PDF p.2.
--   - `cliffordE`: Exact E = H S^3 omega^3, PDF p.11, including its scalar phase.
--   - `cliffordE2`: E squared, PDF p.11.
--   - `axisTGate`: Ordered x,y,z variants Tx,Ty,Tz of T, PDF p.11.
--   - `Input`: Source input alphabet: one Clifford operator or one T, PDF pp.2-3.
--   - `inputMatrix`: Matrix of an input token, PDF pp.2-3.
--   - `inputWordMatrix`: Input words are in printed order, PDF p.2.
--   - `inputTCount`: Counts actual T tokens, with each Clifford terminal costing zero, PDF p.3.
--   - `CliffordT`: Source Clifford+T operator set; no ancillas or approximation, PDF pp.1-2.
--   - `Token`: Output syntax tokens; the axis tokens each count as one T rotation, PDF pp.11-12.
--   - `tokenMatrix`: Output token matrices, PDF pp.1,11.
--   - `NormalForm`: Common data for the three binary-syllable normal forms, equations (2),(20),(24). A false/true body entry selects the first/second named syllable.
--   - `normalTokens`: Source syntax (T|epsilon)(aT|bT)*C, PDF pp.1,11,12.
--   - `normalValue`: Exact value of a normal expression, PDF pp.1,11,12.
--   - `normalTCount`: T-count is fixed by the actual syntax in (2), PDF pp.1-2.
--   - `maTokens`: Matsumoto-Amano syntax, equation (2), PDF p.1.
--   - `maValue`: Absolute U(2) value of a Matsumoto-Amano form, PDF pp.1-2.
--   - `chronologicalValue`: Chronological execution: the head acts first, PDF p.2.
--   - `letterTCount`: Actual T-letter count in a chronological elementary word, PDF p.3.
--   - `expandClifford`: A fixed T-free expansion of each Clifford operator, PDF p.2. Choice only selects a spelling in a fixed finite group; no runtime is assigned to it.
--   - `expandToken`: Expand one syntax token to chronological elementary letters, PDF pp.2,11.
--   - `normalWord`: The actual chronological word returned from a normal-form expression, PDF p.2.
--   - `RewriteRow`: A finite suffix-rewrite table row, implementing the proof of Corollary 2.4, PDF p.3. The stack is reversed: its head is the rightmost displayed output token.
--   - `SuffixMachine`: A finite local table machine. No row or transition depends on the full input, PDF p.3.
--   - `tableLookup`: First matching table row and the actual number of row comparisons, PDF p.3.
--   - `machineStep`: One bounded suffix update with a primitive-operation charge, PDF p.3. The charge pays for take/drop, bounded token comparisons in every inspected row, and each pushed token. An unchanged tail is shared; it is never copied. Clifford/operator tokens belong to fixed finite alphabets, so their comparisons and the table operations are unit cost, exactly the symbolic model of the proof.
--   - `machineRun`: Foreground symbolic execution, starting at I, PDF p.3. Input is read once, left to right, by incremental right multiplication.
--   - `LinearNormalizer`: Operational meaning of linear symbolic normalization, Corollary 2.4, PDF pp.2-3. The finite machine and constant precede every input, including the empty word. The returned stack itself is the reversed output expression; no uncharged parsing or copying is used to obtain its normal-form syntax. A single appended T can create a Clifford/T syllable plus a new terminal, so a full window must permit two extra output tokens (Corollary 2.4, p.3).
--   - `operatorBloch`: Bloch map in ordered X,Y,Z coordinates, equation (12), PDF p.3. The real trace pairing extracts the coefficient of each conjugated Pauli matrix.
--   - `SpecialOrthogonal`: The source's SO(3), PDF p.3; determinant one excludes reflections.
--   - `cube`: The cube of Remark 4.2, PDF p.3.
--   - `InZsqrt2`: Quadratic integers Z[sqrt(2)], Definition 4.3, PDF p.3.
--   - `InDsqrt2`: Ring D[sqrt(2)] = Z[1/sqrt(2)], Definition 4.3, PDF p.3.
--   - `realDenominator`: Common natural denominator exponent of a real matrix, Definition 4.6, PDF p.4.
--   - `realLde`: Least common real-matrix exponent; fallback 0 only outside its domain, PDF p.4. Every use below is on matrices with entries in D[sqrt(2)] or normal-form images.
--   - `quadraticCoordinates`: Unique quadratic coefficients on Z[sqrt(2)], PDF pp.3-4. Outside that ring the fallback is (0,0); k-parity statements carry its domain.
--   - `parity`: Constant coefficient modulo 2, Definition 4.5, PDF p.4.
--   - `matrixParity`: Scaled entrywise parity, Definition 4.7, PDF p.4.
--   - `parityEquivalent`: Column permutation, not row permutation, Definition 4.9, PDF p.4.
--   - `parityPattern`: The three nonzero parity patterns, Lemma 4.10, PDF pp.4-5.
--   - `blochCase`: Four mutually exclusive clauses of Lemma 4.10, PDF pp.4-5.
--   - `leftSyllable`: The three possible left syllable matrices T,HT,SHT, PDF pp.4-7.
--   - `omegaCoordinatesValue`: Coefficients in descending omega-power order, Definition 4.3, PDF p.4.
--   - `InZomega`: Cyclotomic integers, PDF pp.4,8.
--   - `InDomega`: Dyadic cyclotomic coefficients, PDF p.4.
--   - `complexDenominator`: Common complex-matrix denominator exponent, based on sqrt(2), PDF p.8.
--   - `complexLde`: Least complex-matrix exponent, distinct from the Bloch exponent, PDF p.8.
--   - `Residue`: The quotient Z[omega]/(2) as four coefficient residues, PDF p.8.
--   - `ResidueMat`: Two-by-two matrices over the coefficient residue ring, PDF pp.8-9.
--   - `omegaCoordinates`: Unique cyclotomic coordinates on Z[omega]; zero fallback off-domain, PDF p.8.
--   - `residue`: Coefficientwise residue, Definition 7.3, PDF p.8.
--   - `bits`: Binary pqrs encoding in descending powers omega^3,...,1, PDF p.8.
--   - `residueMultiply`: Multiplication modulo omega^4+1 over F2, PDF p.8. Descending coordinate i has exponent 3-i; a product at exponents 6-i-j contributes to coordinate l exactly when i+j is congruent to l+3 modulo 4.
--   - `Reducible`: Reducibility is divisibility by rho(sqrt(2))=1010 in this quotient, PDF p.8.
--   - `matrixResidue`: Entrywise k-residue, Definition 7.4, PDF p.8; validity is carried explicitly.
--   - `residueAction`: Right action by a subgroup operator, Definition 7.6, PDF pp.8-9. This includes a global shift, column swap, and independent second-column shift.
--   - `residueEquivalent`: The source S-equivalence, Definition 7.6, PDF pp.8-9.
--   - `residueMatrix`: A 2x2 residue matrix written with four binary-digit numerals, PDF pp.8-10.
--   - `ModifiedForm`: Modified normal syntax in (19): the subgroup terminal is atomic, PDF p.9.
--   - `modifiedValue`: Exact matrix of expression (19), PDF p.9.
--   - `modifiedTCount`: Count actual T letters in (19), PDF p.9.
--   - `modifiedHCount`: H-count of (19), excluding every H inside its atomic subgroup terminal, PDF p.9.
--   - `FigureVertex`: One retained Figure-2 vertex, PDF p.10. Offsets are integers, not naturals. A fixed exponent records the two top rows; otherwise the threshold is k>=2.
--   - `figureVertices`: The 26 unstarred, reduced vertices of Figure 2, PDF p.10. Numbers a,b,c,d abbreviate their four binary-digit strings, not ring integers. Rows are read left to right, with the two start vertices first.
--   - `VertexCounts`: Every equality and threshold printed on a vertex, Theorem 7.10, PDF pp.9-10.
--   - `AxisForm`: Axis syntax: only adjacent equal axes are forbidden, Proposition 8.2, PDF p.12.
--   - `axisTokens`: The actual axis expression, PDF pp.11-12.
--   - `axisValue`: Absolute operator value of an axis expression, PDF pp.11-12.
--   - `OriginalBS`: Original nonunique BS syntax, equation (21), PDF p.12.
--   - `originalBSValue`: Matrix of the original BS expression (21), PDF p.12.
--   - `cliffordZ`: Z terminal with its exact T-free spelling, PDF p.12.
--   - `cliffordX`: X terminal with its exact T-free spelling, PDF p.12.
--   - `cliffordYS`: YS terminal: omega^2 X S^3, including the required phase, PDF p.12.
--   - `cliffordXOmega`: X omega terminal, PDF p.12.
--   - `originalBSWitness`: The two original-BS identity witnesses and the second pair, PDF p.12.
--   - `TwoSidedBS`: Two-sided BS syntax (25), PDF p.12. Short prefixes prohibit a following tail.
--   - `twoSidedBSValue`: Exact matrix of (25), PDF p.12.
--   - `twoSidedBSWitness`: The four explicit two-sided BS witnesses, PDF p.12.
-- source:
--   Remarks on Matsumoto and Amano's normal form for single-qubit Clifford+T operators, arXiv:1312.6584v2, https://arxiv.org/abs/1312.6584v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

/-!
Statements from Giles and Selinger, arXiv:1312.6584v2.
Products of matrices and displayed words act right to left. Clifford terminals
are operators, with the finite phase group generated by omega, not U(1).
The accepted chronological Letter alphabet and frozen ordered Pauli basis are
imported; paper-specific normal-form definitions remain local. Runtime is stated
only for the finite suffix-table machine below. Matrix-input arithmetic synthesis is deferred
in HARD.md rather than encoded by assigning a cost to a choice function.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P10

open scoped Classical BigOperators Pointwise

open QAlgorithms.Papers.Independent.Next46.P21 (Letter letterMatrix)
open QAlgorithms.QubitChannels (sigma)

-- Equation (1), PDF p.1: notation for Mathlib matrices, without a new declaration.
local notation "Mat" => Matrix Bool Bool ℂ

/-- Fixed three-coordinate Bloch matrix space, equation (12), PDF p.3. -/
abbrev RealMat := Matrix (Fin 3) (Fin 3) ℝ

/-- Entrywise binary parity matrices, Definitions 4.5-4.9, PDF p.4. -/
abbrev ParityMat := Matrix (Fin 3) (Fin 3) (ZMod 2)

-- Equation (1), PDF p.1: reuse the exact scalar entry of the frozen T gate.
local notation "omega" => QAlgorithms.gateT true true

/-- Scalar gate omega I, PDF pp.1-2. -/
def scalarOmega : Mat := omega • 1

/-- The T-free generating alphabet of the 192-element group, PDF pp.1-2. -/
inductive CliffordLetter where
  | h | s | omega
  deriving DecidableEq

/-- Exact matrices of the Clifford generators, PDF pp.1-2. -/
def cliffordLetterMatrix : CliffordLetter → Mat
  | .h => QAlgorithms.hadamard
  | .s => QAlgorithms.phaseS
  | .omega => scalarOmega

/-- Printed-order multiplication, PDF p.2. The empty word denotes I. -/
def cliffordWordMatrix (w : List CliffordLetter) : Mat :=
  (w.map cliffordLetterMatrix).prod

/-- The finite Clifford operator set, Definition 2.1, PDF p.2.
Positive words generate the stated group because its generators have finite order. -/
def cliffordSet : Set Mat := Set.range cliffordWordMatrix

/-- Terminals identify Clifford operators, never arbitrary spellings, PDF p.2. -/
abbrev Clifford := {U : Mat // U ∈ cliffordSet}

/-- A Clifford operator constructed from a T-free word, PDF p.2. -/
def cliffordOfWord (w : List CliffordLetter) : Clifford :=
  ⟨cliffordWordMatrix w, ⟨w, rfl⟩⟩

/-- The distinguished identity terminal, PDF p.2. -/
def cliffordI : Clifford := cliffordOfWord []

/-- H as an operator terminal, PDF p.2. -/
def cliffordH : Clifford := cliffordOfWord [.h]

/-- SH as an operator terminal, PDF p.2. -/
def cliffordSH : Clifford := cliffordOfWord [.s, .h]

/-- HSH as an operator terminal, PDF p.12. -/
def cliffordHSH : Clifford := cliffordOfWord [.h, .s, .h]

/-- Generators of the 64-element subgroup, Definition 2.1, PDF p.2. -/
inductive SmallLetter where
  | s | x | omega
  deriving DecidableEq

/-- Exact subgroup generator matrices, PDF p.2. -/
def smallLetterMatrix : SmallLetter → Mat
  | .s => QAlgorithms.phaseS
  | .x => QAlgorithms.pauliX
  | .omega => scalarOmega

/-- The subgroup S of Definition 2.1, PDF p.2. -/
def smallSet : Set Mat :=
  Set.range (fun w : List SmallLetter => (w.map smallLetterMatrix).prod)

/-- Operator-valued terminal in the 64-element subgroup, Definition 2.1, PDF p.2. -/
abbrev SmallClifford := {U : Mat // U ∈ smallSet}

/-- Transversal H from Definition 2.1, PDF p.2. -/
def transversal : Set Mat := {1, QAlgorithms.hadamard, QAlgorithms.phaseS * QAlgorithms.hadamard}

/-- Nonidentity transversal H prime, PDF p.2. -/
def nonidentityTransversal : Set Mat := {QAlgorithms.hadamard, QAlgorithms.phaseS * QAlgorithms.hadamard}

/-- Exact E = H S^3 omega^3, PDF p.11, including its scalar phase. -/
def cliffordE : Clifford :=
  cliffordOfWord ([.h] ++ List.replicate 3 .s ++ List.replicate 3 .omega)

/-- E squared, PDF p.11. -/
def cliffordE2 : Clifford :=
  cliffordOfWord (([.h] ++ List.replicate 3 .s ++ List.replicate 3 .omega) ++
    ([.h] ++ List.replicate 3 .s ++ List.replicate 3 .omega))

/-- Ordered x,y,z variants Tx,Ty,Tz of T, PDF p.11. -/
def axisTGate (r : Fin 3) : Mat :=
  if r = 0 then cliffordE.val * QAlgorithms.gateT * cliffordE2.val
  else if r = 1 then cliffordE2.val * QAlgorithms.gateT * cliffordE.val
  else QAlgorithms.gateT

/-- Source input alphabet: one Clifford operator or one T, PDF pp.2-3. -/
inductive Input where
  | clifford (C : Clifford)
  | t

/-- Matrix of an input token, PDF pp.2-3. -/
def inputMatrix : Input → Mat
  | .clifford C => C.val
  | .t => QAlgorithms.gateT

/-- Input words are in printed order, PDF p.2. -/
def inputWordMatrix (w : List Input) : Mat := (w.map inputMatrix).prod

/-- Counts actual T tokens, with each Clifford terminal costing zero, PDF p.3. -/
def inputTCount (w : List Input) : ℕ :=
  (w.filter fun a => match a with | .t => true | .clifford _ => false).length

/-- Source Clifford+T operator set; no ancillas or approximation, PDF pp.1-2. -/
def CliffordT (U : Mat) : Prop := ∃ w : List Input, inputWordMatrix w = U

/-- Output syntax tokens; the axis tokens each count as one T rotation, PDF pp.11-12. -/
inductive Token where
  | clifford (C : Clifford)
  | t
  | axis (r : Fin 3)

/-- Output token matrices, PDF pp.1,11. -/
def tokenMatrix : Token → Mat
  | .clifford C => C.val
  | .t => QAlgorithms.gateT
  | .axis r => axisTGate r

/-- Common data for the three binary-syllable normal forms, equations (2),(20),(24).
A false/true body entry selects the first/second named syllable. -/
structure NormalForm where
  leadingT : Bool
  body : List Bool
  terminal : Clifford

/-- Source syntax (T|epsilon)(aT|bT)*C, PDF pp.1,11,12. -/
def normalTokens (a b : Clifford) (M : NormalForm) : List Token :=
  (if M.leadingT then [.t] else []) ++
  M.body.flatMap (fun q => [.clifford (if q then b else a), .t]) ++
  [.clifford M.terminal]

/-- Exact value of a normal expression, PDF pp.1,11,12. -/
def normalValue (a b : Clifford) (M : NormalForm) : Mat :=
  ((normalTokens a b M).map tokenMatrix).prod

/-- T-count is fixed by the actual syntax in (2), PDF pp.1-2. -/
def normalTCount (M : NormalForm) : ℕ :=
  (if M.leadingT then 1 else 0) + M.body.length

/-- Matsumoto-Amano syntax, equation (2), PDF p.1. -/
def maTokens := normalTokens cliffordH cliffordSH

/-- Absolute U(2) value of a Matsumoto-Amano form, PDF pp.1-2. -/
def maValue := normalValue cliffordH cliffordSH

/-- Chronological execution: the head acts first, PDF p.2. -/
def chronologicalValue (w : List Letter) : Mat := (w.map letterMatrix).reverse.prod

/-- Actual T-letter count in a chronological elementary word, PDF p.3. -/
def letterTCount (w : List Letter) : ℕ := (w.filter (fun a => decide (a = .t))).length

/-- A fixed T-free expansion of each Clifford operator, PDF p.2.
Choice only selects a spelling in a fixed finite group; no runtime is assigned to it. -/
def expandClifford (C : Clifford) : List Letter :=
  (Classical.choose C.property).reverse.map fun a =>
    match a with | .h => .h | .s => .s | .omega => .phase

/-- Expand one syntax token to chronological elementary letters, PDF pp.2,11. -/
def expandToken : Token → List Letter
  | .clifford C => expandClifford C
  | .t => [.t]
  | .axis r =>
      if r = 0 then expandClifford cliffordE2 ++ [.t] ++ expandClifford cliffordE
      else if r = 1 then expandClifford cliffordE ++ [.t] ++ expandClifford cliffordE2
      else [.t]

/-- The actual chronological word returned from a normal-form expression, PDF p.2. -/
def normalWord (a b : Clifford) (M : NormalForm) : List Letter :=
  (normalTokens a b M).reverse.flatMap expandToken

/-- A finite suffix-rewrite table row, implementing the proof of Corollary 2.4, PDF p.3.
The stack is reversed: its head is the rightmost displayed output token. -/
structure RewriteRow where
  suffixTokens : List Token
  nextInput : Input
  replacement : List Token

/-- A finite local table machine. No row or transition depends on the full input, PDF p.3. -/
structure SuffixMachine where
  window : ℕ
  table : List RewriteRow

/-- First matching table row and the actual number of row comparisons, PDF p.3. -/
def tableLookup : List RewriteRow → List Token → Input → Option RewriteRow × ℕ
  | [], _, _ => (none, 0)
  | row :: rows, topTokens, a =>
      if row.suffixTokens = topTokens ∧ row.nextInput = a then (some row, 1)
      else
        let ans := tableLookup rows topTokens a
        (ans.1, ans.2 + 1)

/-- One bounded suffix update with a primitive-operation charge, PDF p.3.
The charge pays for take/drop, bounded token comparisons in every inspected row,
and each pushed token. An unchanged tail is shared; it is never copied.
Clifford/operator tokens belong to fixed finite alphabets, so their comparisons
and the table operations are unit cost, exactly the symbolic model of the proof. -/
def machineStep (m : SuffixMachine) (s : List Token) (a : Input) : List Token × ℕ :=
  let ans := tableLookup m.table (s.take m.window) a
  match ans.1 with
  | none => (s, 2 * m.window + (m.window + 2) * ans.2 + 1)
  | some row =>
      (row.replacement ++ s.drop m.window,
       2 * m.window + row.replacement.length + (m.window + 2) * ans.2 + 1)

/-- Foreground symbolic execution, starting at I, PDF p.3.
Input is read once, left to right, by incremental right multiplication. -/
def machineRun (m : SuffixMachine) (w : List Input) : List Token × ℕ :=
  w.foldl (fun acc a =>
    let next := machineStep m acc.1 a
    (next.1, acc.2 + next.2)) ([.clifford cliffordI], 1)

/-- Operational meaning of linear symbolic normalization, Corollary 2.4, PDF pp.2-3.
The finite machine and constant precede every input, including the empty word.
The returned stack itself is the reversed output expression; no uncharged parsing
or copying is used to obtain its normal-form syntax.
A single appended T can create a Clifford/T syllable plus a new terminal,
so a full window must permit two extra output tokens (Corollary 2.4, p.3). -/
def LinearNormalizer {α : Type} (syntaxFn : α → List Token) (value : α → Mat) : Prop :=
  ∃ m : SuffixMachine, ∃ B : ℕ, 0 < B ∧
    (∀ row ∈ m.table, row.suffixTokens.length ≤ m.window ∧
      row.replacement.length ≤ m.window + 2) ∧
    ∀ w : List Input,
      (machineRun m w).2 ≤ B * (w.length + 1) ∧
      ∃ M : α, (machineRun m w).1 = (syntaxFn M).reverse ∧
        value M = inputWordMatrix w

/-- Bloch map in ordered X,Y,Z coordinates, equation (12), PDF p.3.
The real trace pairing extracts the coefficient of each conjugated Pauli matrix. -/
def operatorBloch (U : Mat) : RealMat :=
  fun i j => (Matrix.trace (sigma i * U * sigma j * star U)).re / 2

/-- The source's SO(3), PDF p.3; determinant one excludes reflections. -/
def SpecialOrthogonal (U : RealMat) : Prop :=
  U.transpose * U = 1 ∧ U * U.transpose = 1 ∧ U.det = 1

/-- The cube of Remark 4.2, PDF p.3. -/
def cube : Set (Fin 3 → ℝ) := {x | ∀ i, -1 ≤ x i ∧ x i ≤ 1}

/-- Quadratic integers Z[sqrt(2)], Definition 4.3, PDF p.3. -/
def InZsqrt2 (z : ℝ) : Prop := ∃ a b : ℤ, z = (a : ℝ) + (b : ℝ) * Real.sqrt 2

/-- Ring D[sqrt(2)] = Z[1/sqrt(2)], Definition 4.3, PDF p.3. -/
def InDsqrt2 (z : ℝ) : Prop := ∃ k : ℕ, InZsqrt2 ((Real.sqrt 2) ^ k * z)

/-- Common natural denominator exponent of a real matrix, Definition 4.6, PDF p.4. -/
def realDenominator (U : RealMat) (k : ℕ) : Prop :=
  ∀ i j, InZsqrt2 ((Real.sqrt 2) ^ k * U i j)

/-- Least common real-matrix exponent; fallback 0 only outside its domain, PDF p.4.
Every use below is on matrices with entries in D[sqrt(2)] or normal-form images. -/
def realLde (U : RealMat) : ℕ :=
  if h : ∃ k, realDenominator U k then Nat.find h else 0

/-- Unique quadratic coefficients on Z[sqrt(2)], PDF pp.3-4.
Outside that ring the fallback is (0,0); k-parity statements carry its domain. -/
def quadraticCoordinates (z : ℝ) : ℤ × ℤ :=
  if h : ∃ ab : ℤ × ℤ, z = (ab.1 : ℝ) + (ab.2 : ℝ) * Real.sqrt 2
  then Classical.choose h else (0, 0)

/-- Constant coefficient modulo 2, Definition 4.5, PDF p.4. -/
def parity (z : ℝ) : ZMod 2 := (quadraticCoordinates z).1

/-- Scaled entrywise parity, Definition 4.7, PDF p.4. -/
def matrixParity (U : RealMat) (k : ℕ) : ParityMat :=
  fun i j => parity ((Real.sqrt 2) ^ k * U i j)

/-- Column permutation, not row permutation, Definition 4.9, PDF p.4. -/
def parityEquivalent (P Q : ParityMat) : Prop :=
  ∃ e : Equiv.Perm (Fin 3), ∀ i j, P i (e j) = Q i j

/-- The three nonzero parity patterns, Lemma 4.10, PDF pp.4-5. -/
def parityPattern (r : Fin 3) : ParityMat :=
  if r = 0 then !![1, 1, 0; 1, 1, 0; 0, 0, 0]
  else if r = 1 then !![0, 0, 0; 1, 1, 0; 1, 1, 0]
  else !![1, 1, 0; 0, 0, 0; 1, 1, 0]

/-- Four mutually exclusive clauses of Lemma 4.10, PDF pp.4-5. -/
def blochCase (M : NormalForm) (tag : Fin 4) : Prop :=
  let U := operatorBloch (maValue M)
  let k := realLde U
  if tag = 0 then k = 0 ∧ maValue M ∈ cliffordSet
  else if tag = 1 then 0 < k ∧ parityEquivalent (matrixParity U k) (parityPattern 0) ∧ M.leadingT = true
  else if tag = 2 then 0 < k ∧ parityEquivalent (matrixParity U k) (parityPattern 1) ∧
    M.leadingT = false ∧ M.body.head? = some false
  else 0 < k ∧ parityEquivalent (matrixParity U k) (parityPattern 2) ∧
    M.leadingT = false ∧ M.body.head? = some true

/-- The three possible left syllable matrices T,HT,SHT, PDF pp.4-7. -/
def leftSyllable (r : Fin 3) : Mat :=
  if r = 0 then QAlgorithms.gateT
  else if r = 1 then QAlgorithms.hadamard * QAlgorithms.gateT
  else QAlgorithms.phaseS * QAlgorithms.hadamard * QAlgorithms.gateT

/-- Coefficients in descending omega-power order, Definition 4.3, PDF p.4. -/
def omegaCoordinatesValue (a : Fin 4 → ℤ) : ℂ :=
  (a 0 : ℂ) * omega ^ 3 + (a 1 : ℂ) * omega ^ 2 + (a 2 : ℂ) * omega + (a 3 : ℂ)

/-- Cyclotomic integers, PDF pp.4,8. -/
def InZomega (z : ℂ) : Prop := ∃ a : Fin 4 → ℤ, omegaCoordinatesValue a = z

/-- Dyadic cyclotomic coefficients, PDF p.4. -/
def InDomega (z : ℂ) : Prop := ∃ k : ℕ, InZomega ((2 : ℂ) ^ k * z)

/-- Common complex-matrix denominator exponent, based on sqrt(2), PDF p.8. -/
def complexDenominator (U : Mat) (k : ℕ) : Prop :=
  ∀ i j, InZomega (((Real.sqrt 2 : ℝ) : ℂ) ^ k * U i j)

/-- Least complex-matrix exponent, distinct from the Bloch exponent, PDF p.8. -/
def complexLde (U : Mat) : ℕ :=
  if h : ∃ k, complexDenominator U k then Nat.find h else 0

/-- The quotient Z[omega]/(2) as four coefficient residues, PDF p.8. -/
abbrev Residue := Fin 4 → ZMod 2

/-- Two-by-two matrices over the coefficient residue ring, PDF pp.8-9. -/
abbrev ResidueMat := Matrix Bool Bool Residue

/-- Unique cyclotomic coordinates on Z[omega]; zero fallback off-domain, PDF p.8. -/
def omegaCoordinates (z : ℂ) : Fin 4 → ℤ :=
  if h : InZomega z then Classical.choose h else 0

/-- Coefficientwise residue, Definition 7.3, PDF p.8. -/
def residue (z : ℂ) : Residue := fun j => (omegaCoordinates z j : ZMod 2)

/-- Binary pqrs encoding in descending powers omega^3,...,1, PDF p.8. -/
def bits (n : ℕ) : Residue := fun i => ((n / 2 ^ (3 - i.val)) % 2 : ℕ)

/-- Multiplication modulo omega^4+1 over F2, PDF p.8.
Descending coordinate i has exponent 3-i; a product at exponents 6-i-j
contributes to coordinate l exactly when i+j is congruent to l+3 modulo 4. -/
def residueMultiply (a b : Residue) : Residue :=
  fun l => ∑ i : Fin 4, ∑ j : Fin 4,
    if (i.val + j.val) % 4 = (l.val + 3) % 4 then a i * b j else 0

/-- Reducibility is divisibility by rho(sqrt(2))=1010 in this quotient, PDF p.8. -/
def Reducible (a : Residue) : Prop := ∃ b : Residue, residueMultiply (bits 10) b = a

/-- Entrywise k-residue, Definition 7.4, PDF p.8; validity is carried explicitly. -/
def matrixResidue (U : Mat) (k : ℕ) : ResidueMat :=
  fun i j => residue (((Real.sqrt 2 : ℝ) : ℂ) ^ k * U i j)

/-- Right action by a subgroup operator, Definition 7.6, PDF pp.8-9.
This includes a global shift, column swap, and independent second-column shift. -/
def residueAction (R : ResidueMat) (A : SmallClifford) : ResidueMat :=
  fun i j => ∑ l : Bool, residueMultiply (R i l) (residue (A.val l j))

/-- The source S-equivalence, Definition 7.6, PDF pp.8-9. -/
def residueEquivalent (R Q : ResidueMat) : Prop :=
  ∃ A : SmallClifford, residueAction R A = Q

/-- A 2x2 residue matrix written with four binary-digit numerals, PDF pp.8-10. -/
def residueMatrix (a b c d : ℕ) : ResidueMat :=
  fun i j => if i then (if j then bits d else bits c) else (if j then bits b else bits a)

/-- Modified normal syntax in (19): the subgroup terminal is atomic, PDF p.9. -/
structure ModifiedForm where
  leadingT : Bool
  body : List Bool
  tail : Fin 3
  terminal : SmallClifford

/-- Exact matrix of expression (19), PDF p.9. -/
def modifiedValue (M : ModifiedForm) : Mat :=
  (if M.leadingT then QAlgorithms.gateT else 1) *
  (M.body.map (fun b => (if b then QAlgorithms.phaseS * QAlgorithms.hadamard
    else QAlgorithms.hadamard) * QAlgorithms.gateT)).prod *
  (if M.tail = 0 then 1 else if M.tail = 1 then QAlgorithms.hadamard
    else QAlgorithms.phaseS * QAlgorithms.hadamard) * M.terminal.val

/-- Count actual T letters in (19), PDF p.9. -/
def modifiedTCount (M : ModifiedForm) : ℕ :=
  (if M.leadingT then 1 else 0) + M.body.length

/-- H-count of (19), excluding every H inside its atomic subgroup terminal, PDF p.9. -/
def modifiedHCount (M : ModifiedForm) : ℕ :=
  M.body.length + (if M.tail = 0 then 0 else 1)

/-- One retained Figure-2 vertex, PDF p.10. Offsets are integers, not naturals.
A fixed exponent records the two top rows; otherwise the threshold is k>=2. -/
structure FigureVertex where
  pattern : ResidueMat
  tOffset : ℤ
  hOffset : ℤ
  fixedK : Option ℕ
  minK : ℕ

/-- The 26 unstarred, reduced vertices of Figure 2, PDF p.10.
Numbers a,b,c,d abbreviate their four binary-digit strings, not ring integers.
Rows are read left to right, with the two start vertices first. -/
def figureVertices : Fin 26 → FigureVertex := ![
  ⟨residueMatrix 1 0 0 1, 0, 0, (some 0), 0⟩,
  ⟨residueMatrix 1 0 0 2, (-1), 0, (some 0), 0⟩,
  ⟨residueMatrix 1 1 1 1, 2, 1, (some 1), 1⟩,
  ⟨residueMatrix 1 1 4 4, 2, 1, (some 1), 1⟩,
  ⟨residueMatrix 1 2 1 2, 1, 1, (some 1), 1⟩,
  ⟨residueMatrix 1 2 4 8, 1, 1, (some 1), 1⟩,
  ⟨residueMatrix 1 1 2 2, 1, 1, (some 1), 1⟩,
  ⟨residueMatrix 1 1 8 8, 1, 1, (some 1), 1⟩,
  ⟨residueMatrix 1 2 2 4, 0, 1, (some 1), 1⟩,
  ⟨residueMatrix 1 2 8 1, 0, 1, (some 1), 1⟩,
  ⟨residueMatrix 3 3 3 3, 3, 2, none, 2⟩,
  ⟨residueMatrix 3 3 12 12, 3, 2, none, 2⟩,
  ⟨residueMatrix 3 6 3 6, 2, 2, none, 2⟩,
  ⟨residueMatrix 3 6 12 9, 2, 2, none, 2⟩,
  ⟨residueMatrix 3 3 6 6, 2, 2, none, 2⟩,
  ⟨residueMatrix 3 3 9 9, 2, 2, none, 2⟩,
  ⟨residueMatrix 3 6 6 12, 1, 2, none, 2⟩,
  ⟨residueMatrix 3 6 9 3, 1, 2, none, 2⟩,
  ⟨residueMatrix 8 7 7 8, 2, 1, none, 2⟩,
  ⟨residueMatrix 8 7 13 2, 2, 1, none, 2⟩,
  ⟨residueMatrix 8 14 7 1, 1, 1, none, 2⟩,
  ⟨residueMatrix 8 14 13 4, 1, 1, none, 2⟩,
  ⟨residueMatrix 8 7 14 1, 1, 1, none, 2⟩,
  ⟨residueMatrix 8 7 11 4, 1, 1, none, 2⟩,
  ⟨residueMatrix 8 14 14 2, 0, 1, none, 2⟩,
  ⟨residueMatrix 8 14 11 8, 0, 1, none, 2⟩]

/-- Every equality and threshold printed on a vertex, Theorem 7.10, PDF pp.9-10. -/
def VertexCounts (v : FigureVertex) (t h k : ℕ) : Prop :=
  2 * (k : ℤ) - (t : ℤ) = v.tOffset ∧
  2 * (k : ℤ) - (h : ℤ) = v.hOffset ∧ v.minK ≤ k ∧
  (∀ q, v.fixedK = some q → k = q)

/-- Axis syntax: only adjacent equal axes are forbidden, Proposition 8.2, PDF p.12. -/
structure AxisForm where
  axes : List (Fin 3)
  adjacentDistinct : axes.IsChain (· ≠ ·)
  terminal : Clifford

/-- The actual axis expression, PDF pp.11-12. -/
def axisTokens (M : AxisForm) : List Token :=
  M.axes.map Token.axis ++ [.clifford M.terminal]

/-- Absolute operator value of an axis expression, PDF pp.11-12. -/
def axisValue (M : AxisForm) : Mat := ((axisTokens M).map tokenMatrix).prod

/-- Original nonunique BS syntax, equation (21), PDF p.12. -/
structure OriginalBS where
  leadingH : Bool
  body : List Bool
  terminal : Clifford

/-- Matrix of the original BS expression (21), PDF p.12. -/
def originalBSValue (M : OriginalBS) : Mat :=
  (if M.leadingH then QAlgorithms.hadamard else 1) *
  (M.body.map (fun b => if b then QAlgorithms.phaseS * QAlgorithms.hadamard *
    QAlgorithms.gateT * QAlgorithms.hadamard else QAlgorithms.gateT * QAlgorithms.hadamard)).prod * M.terminal.val

/-- Z terminal with its exact T-free spelling, PDF p.12. -/
def cliffordZ : Clifford := cliffordOfWord [.s, .s]

/-- X terminal with its exact T-free spelling, PDF p.12. -/
def cliffordX : Clifford := cliffordOfWord [.h, .s, .s, .h]

/-- YS terminal: omega^2 X S^3, including the required phase, PDF p.12. -/
def cliffordYS : Clifford := cliffordOfWord [.omega, .omega, .h, .s, .s, .h, .s, .s, .s]

/-- X omega terminal, PDF p.12. -/
def cliffordXOmega : Clifford := cliffordOfWord [.h, .s, .s, .h, .omega]

/-- The two original-BS identity witnesses and the second pair, PDF p.12. -/
def originalBSWitness (j : Fin 4) : OriginalBS :=
  if j = 0 then ⟨true, [], cliffordH⟩
  else if j = 1 then ⟨false, [], cliffordI⟩
  else if j = 2 then ⟨false, [true], cliffordZ⟩
  else ⟨true, [true], cliffordI⟩

/-- Two-sided BS syntax (25), PDF p.12. Short prefixes prohibit a following tail. -/
structure TwoSidedBS where
  left : Clifford
  prefixLength : Fin 5
  body : List Bool
  shortBody : prefixLength.val < 4 → body = []
  right : Clifford

/-- Exact matrix of (25), PDF p.12. -/
def twoSidedBSValue (M : TwoSidedBS) : Mat :=
  M.left.val * (QAlgorithms.gateT * QAlgorithms.hadamard) ^ M.prefixLength.val *
  (M.body.map (fun b => if b then QAlgorithms.phaseS * QAlgorithms.hadamard *
    QAlgorithms.gateT * QAlgorithms.hadamard else QAlgorithms.gateT * QAlgorithms.hadamard)).prod * M.right.val

/-- The four explicit two-sided BS witnesses, PDF p.12. -/
def twoSidedBSWitness (j : Fin 4) : TwoSidedBS :=
  if j = 0 then ⟨cliffordZ, 1, [], by simp, cliffordI⟩
  else if j = 1 then ⟨cliffordI, 1, [], by simp, cliffordX⟩
  else if j = 2 then ⟨cliffordYS, 2, [], by simp, cliffordI⟩
  else ⟨cliffordI, 2, [], by simp, cliffordXOmega⟩

/-! Sanity checks for the paper-local definitions. These are not theorem proofs. -/

example : (omega : ℂ) = Complex.exp (Complex.I * Real.pi / 4) := rfl

example : letterMatrix .phase = scalarOmega := rfl

example : sigma 0 = QAlgorithms.pauliX := rfl

example (A B : Set Mat) (U : Mat) :
    U ∈ A * B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = U := Set.mem_mul

example : cliffordWordMatrix [] = 1 := rfl

example : inputWordMatrix [] = 1 := rfl

example : inputTCount [.t, .clifford cliffordI, .t] = 2 := rfl

example : normalTCount ⟨false, [], cliffordI⟩ = 0 := rfl

example : normalTCount ⟨true, [], cliffordI⟩ = 1 := rfl

example : maTokens ⟨false, [], cliffordI⟩ = [.clifford cliffordI] := rfl

example : maValue ⟨false, [], cliffordI⟩ = 1 := by
  simp [maValue, normalValue, normalTokens, tokenMatrix,
    cliffordI, cliffordOfWord, cliffordWordMatrix]

example : SpecialOrthogonal (1 : RealMat) := by simp [SpecialOrthogonal]

example : chronologicalValue [] = 1 := rfl

example : letterTCount [.h, .s, .phase, .t] = 1 := rfl

example (m : SuffixMachine) : machineRun m [] = ([.clifford cliffordI], 1) := rfl

example : InZsqrt2 0 := ⟨0, 0, by simp⟩

example : InDsqrt2 0 := ⟨0, 0, 0, by simp⟩

example : InZomega 0 := ⟨0, by simp [omegaCoordinatesValue]⟩

example : InDomega 0 := ⟨0, 0, by simp [omegaCoordinatesValue]⟩

example : bits 0 = 0 := by ext i; simp [bits]

example : parityPattern 0 2 0 = 0 := rfl

example : figureVertices 0 = ⟨residueMatrix 1 0 0 1, 0, 0, (some 0), 0⟩ := rfl

example : modifiedTCount ⟨false, [], 0, ⟨1, ⟨[], rfl⟩⟩⟩ = 0 := rfl

example : modifiedHCount ⟨false, [], 1, ⟨1, ⟨[], rfl⟩⟩⟩ = 1 := rfl

example : (originalBSWitness 0).leadingH = true := by simp [originalBSWitness]

example : (twoSidedBSWitness 2).prefixLength = 2 := by simp [twoSidedBSWitness]

end QAlgorithms.Papers.Independent.Gap48.P10


