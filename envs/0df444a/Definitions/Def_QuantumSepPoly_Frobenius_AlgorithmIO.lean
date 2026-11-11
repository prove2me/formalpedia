-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_AlgorithmIO
-- name    : QuantumSepPoly_Frobenius_AlgorithmIO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:17.592229+00:00
-- url     : https://prove2.me/theorems/c79904fc-039e-46aa-92ac-a051aa810a82
-- title:
--   Scalar input and output encodings
-- statement:
--   A complex matrix is stored in row-major order as pairs of real and imaginary entries. Product-vector outputs occupy fixed real registers. A decision accepts exactly when its designated output register equals one. CSP inputs list all ordered tuples and all label tuples in an explicit recursively defined order, including repetitions. Natural output registers hold the assignment labels.
--   $$\operatorname{output}=\operatorname{decode}(\text{first halting execution state}).$$
--   The encoding supplies neither an optimum nor a free output distribution. Costs arise from the RAM execution defined separately.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 19 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_RealRAM
import Definitions.Def_QuantumSepPoly_Frobenius_MatrixGeometry
import Definitions.Def_QuantumSepPoly_Frobenius_DenseCSP

noncomputable section

namespace QuantumSepPoly.Frobenius

/-- A fixed row-major scalar representation: complex entries are pairs of reals. -/
def encodeMatrix {d : ℕ} (M : Bip d) : List ℝ :=
  (List.finRange d).flatMap fun a => (List.finRange d).flatMap fun c =>
  (List.finRange d).flatMap fun b => (List.finRange d).flatMap fun e =>
    [(M (a,c) (b,e)).re, (M (a,c) (b,e)).im]

def matrixInitial {d : ℕ} (η : ℝ) (M : Bip d) : RAMState := ramInitial η d (encodeMatrix M)

def outputPair (d : ℕ) (s : RAMState) : Vec d × Vec d :=
  (fun i => (s.real (1+2*i.val) : ℂ) + Complex.I*s.real (2+2*i.val),
   fun i => (s.real (1+2*d+2*i.val) : ℂ) + Complex.I*s.real (2+2*d+2*i.val))

def productOutput {d : ℕ} (P : RAMProgram) (τ : ℝ) (M : Bip d) (tape : RandomTape) : Vec d × Vec d :=
  outputPair d (ramResult P (matrixInitial τ M) tape)

def accepts {d : ℕ} (P : RAMProgram) (η : ℝ) (M : Bip d) (tape : RandomTape) : Prop :=
  (ramResult P (matrixInitial η M) tape).real 1 = 1

/-- Explicit base-n enumeration, with no classical choice of table order. -/
def allWords (n : ℕ) : (k : ℕ) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k+1 => (List.finRange n).flatMap fun x =>
      (allWords n k).map fun y => Fin.cons x y

/-- Dense CSP tables in lexicographic order, including every repeated tuple.
Only the constraint tables are read, no value/optimum oracle is part of the input. -/
def encodeCSP {n k q : ℕ} (I : MaxCSP n k (Fin q)) : List ℝ :=
  [(k : ℝ),(q : ℝ)] ++ ((allWords n k).flatMap fun t => (allWords q k).map (I.predicate t))

def cspInitial {n k q : ℕ} (ε : ℝ) (I : MaxCSP n k (Fin q)) : RAMState :=
  ramInitial ε n (encodeCSP I)

/-- Natural output registers hold an assignment; malformed entries are explicitly rejected. -/
def CSPOutput {n k q : ℕ} (P : RAMProgram) (ε : ℝ) (I : MaxCSP n k (Fin q))
    (tape : RandomTape) (z : Fin n → Fin q) : Prop :=
  ∀ i, (ramResult P (cspInitial ε I) tape).nat (i.val+1) = (z i).val

end QuantumSepPoly.Frobenius


