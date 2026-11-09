-- Prove2me | Definitions.Def_GenericGroupWE_Main_Circuit
-- name    : GenericGroupWE_Main_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:55.906419+00:00
-- url     : https://prove2.me/theorems/0b2e9e3d-206a-467b-9d62-60d3b3913ab8
-- title:
--   Circuit quadratic equations, explicit indexing, and square padding
-- statement:
--   The raw published circuit type is reused with its total evaluation; no fan-out or terminal-output condition is imposed. The bit encoding charges for every declared input and serializes the published size-aware circuit data. Missing or forward gate references read as zero, matching the published evaluator; valid acyclic circuits have their usual semantics.
--
--   For input, constant, AND, OR and NOT gates, equations set the gate variable equal to the corresponding expression. Boolean equations are imposed on every variable, and the final output is constrained to one. Empty circuits instead impose the inconsistent constant equation. Extra variables are unused padding bits. The count is at least two and at least the encoded circuit length.
--
--   $$q_{\mathrm{AND}}=b_k-b_ib_j,\quad q_{\mathrm{OR}}=b_k-b_i-b_j+b_ib_j,\quad q_{\mathrm{NOT}}=b_k+b_i-1.$$
--
--   Subsets and exponent tuples are ordered by explicit numerical codes. The rectangular stack is made square by retaining its monomial columns first and appending zeros, with the exact order from equation (33). The square tested space uses the same coefficients and tests as its rectangular version.
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §4, Boolean quadratic gate equations, PDF p. 11 (printed p. 10); §5.1, padding, PDF p. 15 (printed p. 14); §6.1 and §6.5, PDF pp. 24 and 30 (printed pp. 23 and 29); published raw MIPRE circuit encoding, definition id 308ee67a-afe6-463d-9b28-a14534139ac8.

import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_GenericGroupWE_Main_Group
import Definitions.Def_GenericGroupWE_Main_Tables

namespace GenericGroupWE.Main

open scoped BigOperators

/-- Explicit input declarations are charged to the circuit length. -/
def circuitBits (C : MIPRE.SAT.Circuit) : Bits :=
  pack [List.replicate C.inputs false, (MIPRE.Cost.encode C).toBits]

def SatisfiesCircuit (C : MIPRE.SAT.Circuit) (w : Bits) : Prop :=
  w.length = C.inputs ∧ C.evalBits w = true

def circuitVariables (C : MIPRE.SAT.Circuit) (padding : ℕ) : ℕ :=
  max 2 (C.inputs + C.gates.length + (circuitBits C).length + padding)

noncomputable def variableAt {K : Type*} [Field K] (N i : ℕ) : MvPolynomial (Fin N) K :=
  if hi : i < N then MvPolynomial.X ⟨i, hi⟩ else 0

/-- Total raw-circuit semantics: forward or missing references read as zero, as in MIPRE.
This agrees with the ordinary gate equations on every acyclic circuit. -/
noncomputable def gateEquation {K : Type*} [Field K] (C : MIPRE.SAT.Circuit)
    (padding index : ℕ) (g : MIPRE.SAT.Gate) :
    MvPolynomial (Fin (circuitVariables C padding)) K :=
  let N := circuitVariables C padding
  let out := variableAt N (C.inputs + index)
  let gate : ℕ → MvPolynomial (Fin N) K :=
    fun j => if j < index then variableAt N (C.inputs + j) else 0
  out - match g with
    | .input i => if i < C.inputs then variableAt N i else 0
    | .const b => if b then 1 else 0
    | .and i j => gate i * gate j
    | .or i j => gate i + gate j - gate i * gate j
    | .not i => 1 - gate i

noncomputable def quadraticEquations (K : Type*) [Field K] (C : MIPRE.SAT.Circuit)
    (padding : ℕ) : List (MvPolynomial (Fin (circuitVariables C padding)) K) :=
  let N := circuitVariables C padding
  (List.ofFn fun i : Fin N => (MvPolynomial.X i)^2 - MvPolynomial.X i) ++
    C.gates.mapIdx (gateEquation C padding) ++
    [if C.gates.isEmpty then -1 else variableAt N (C.inputs + C.gates.length - 1) - 1]

noncomputable def circuitQuadratics (K : Type*) [Field K] (C : MIPRE.SAT.Circuit)
    (padding : ℕ) : Fin (quadraticEquations K C padding).length →
      MvPolynomial (Fin (circuitVariables C padding)) K :=
  fun i => (quadraticEquations K C padding)[i]

/-- Canonical numerical ordering of subsets and exponent tuples, independent of field data. -/
def subsetCode {N : ℕ} (S : Finset (Fin N)) : ℕ := ∑ i ∈ S, 2^i.val

def exponentCode {N e : ℕ} (α : OrdinaryMonomial N e) : ℕ :=
  ∑ i : Fin N, (α.val i).val * (e+1)^i.val

noncomputable def columnList (N d : ℕ) : List (BitMonomial N d) := by
  classical
  exact (Finset.univ.toList : List (BitMonomial N d)).mergeSort
    (fun S T => subsetCode S.val ≤ subsetCode T.val)

def rowCode {N d : ℕ} (row : StackRow N d) : ℕ :=
  ((row.1.1.val * (weightDegree N + 1)^((rankTarget N d)^2) +
    exponentCode row.1.2) * 2^N) + subsetCode row.2.val

noncomputable def rowList (N d : ℕ) : List (StackRow N d) := by
  classical
  exact (Finset.univ.toList : List (StackRow N d)).mergeSort (fun a b => rowCode a ≤ rowCode b)

/-- Eq. (33): append zero columns after all assignment monomials. -/
noncomputable def squareAssignment {K : Type*} [Field K] {N d : ℕ}
    (b : BooleanAssignment N) : Matrix (Fin (matrixOrder N d)) (Fin (matrixOrder N d)) K :=
  fun i j => match (rowList N d)[i.val]?, (columnList N d)[j.val]? with
    | some row, some col => assignmentStack b row col
    | _, _ => 0

noncomputable def squareTestedSpace {K : Type*} [Field K] {N k d : ℕ}
    (q : Fin k → MvPolynomial (Fin N) K) :
    Set (Matrix (Fin (matrixOrder N d)) (Fin (matrixOrder N d)) K) :=
  {A | ∃ coefficients : BooleanAssignment N → K,
    A = ∑ b, coefficients b • squareAssignment b ∧
      ∀ (h : WeightLabel N d) (s : Fin k) (U : Finset (Fin N)), U.card + 2 ≤ 2*d →
        ∑ b, coefficients b * stackWeight h b *
          MvPolynomial.eval (booleanPoint b) (q s) * bitProduct b U = 0}

end GenericGroupWE.Main


