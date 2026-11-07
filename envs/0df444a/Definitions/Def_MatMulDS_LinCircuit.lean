-- Prove2me | Definitions.Def_MatMulDS_LinCircuit
-- name    : MatMulDS_LinCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:29.237368+00:00
-- url     : https://prove2.me/theorems/4ecab20b-8959-40d0-8f96-212f1d21b53b
-- title:
--   Linear straight-line circuits; row-major matrix inputs
-- statement:
--   A **linear straight-line circuit** over a field $\mathbb F$ is a list of gates, each an input $x_i$, a scalar multiple $c\cdot g$ of a gate, or a sum $g+h$ of two gates, together with a list of output gates. It computes linear combinations of its inputs, and its size is its number of gates. Its $p$th output is taken to be $0$ when $p$ is past the end of its output list.
--
--   A matrix is fed in row-major order: entry $(i,j)$ of an $m\times n$ matrix is input $in+j$, with 0-based indices. This layer is shared by bilinear algorithms and by bilinear data structures, and the products $\Phi(x)[a_p]\Psi(y)[b_p]$ are also defined here.
--
--   **Formalization Note** A reference to a gate that does not exist yet reads $0$, so a circuit needs no well-formedness proof.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), §4.1, p.15 (PDF p.17)

import Mathlib

set_option autoImplicit false

namespace MatMulDS

/-!
# Linear straight-line circuits

Alman, Nogler, Vassilevska Williams, *Subquadratic Time Matrix Multiplication Data Structures Beyond
the Dual Exponent, with Applications*, STOC 2027 submission (held file sha256 6c5a1c16…), §4.1, p.15:
"Most of these circuits are linear: they only use scalar multiplications and additions, outputting a
linear combination of their inputs."

**Formalization Note.**
* Inputs are indexed by `ℕ`. A matrix is fed in row-major order (`matList`, `matInput`).
* A gate reads the inputs or earlier gates. A reference to a gate that does not exist yet reads `0`,
  so a circuit needs no well-formedness proof and a constant zero costs one gate at most.
* An index past the end of the output list reads `0` (`LinCircuit.out`). This is the convention at the
  end of Definition 4.1, p.16: "an index p ∈ [Pnew] outside the output range of C^A_new or C^B_new
  contributes zero".
-/

/-- A gate of a linear circuit: an input, a scalar multiple of a gate, or a sum of two gates. -/
inductive LinGate (F : Type) where
  | input (i : ℕ)
  | scale (c : F) (g : ℕ)
  | add (g h : ℕ)

/-- A multi-output linear straight-line circuit: its gates in order, and the gate of each output.
Source: STOC 2027 submission (held file sha256 6c5a1c16…), §4.1, p.15. -/
structure LinCircuit (F : Type) where
  gates : List (LinGate F)
  outputs : List ℕ

variable {F : Type} [Field F]

/-- The value of a gate on the input `x`, given the values `vals` of the gates before it. -/
def LinGate.eval (x : ℕ → F) (vals : List F) : LinGate F → F
  | .input i => x i
  | .scale c g => c * vals.getD g 0
  | .add g h => vals.getD g 0 + vals.getD h 0

/-- The values of all gates of a circuit on the input `x`, in order. -/
def LinCircuit.gateValues (C : LinCircuit F) (x : ℕ → F) : List F :=
  C.gates.foldl (fun vals g => vals ++ [g.eval x vals]) []

/-- The list of outputs of a circuit on the input `x`. -/
def LinCircuit.eval (C : LinCircuit F) (x : ℕ → F) : List F :=
  C.outputs.map fun o => (C.gateValues x).getD o 0

/-- The `p`th output of a circuit on the input `x` (`0` outside the output range). -/
def LinCircuit.out (C : LinCircuit F) (x : ℕ → F) (p : ℕ) : F :=
  (C.eval x).getD p 0

/-- The size of a circuit: its number of gates. -/
def LinCircuit.size (C : LinCircuit F) : ℕ := C.gates.length

/-- The entries of a matrix in row-major order. -/
def matList {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : List F :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => A i j

/-- A matrix as the input of a linear circuit: the entry in row `i` and column `j` of an `m × n`
matrix is input `i * n + j`. -/
def matInput {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : ℕ → F :=
  fun a => (matList A).getD a 0

/-- The products `Φ(x)[a p] · Ψ(y)[b p]`, for `p < r`, as the input of a linear circuit (`0` from
index `r` on). -/
def productInput (Φ Ψ : LinCircuit F) {r : ℕ} (a b : Fin r → ℕ) (x y : ℕ → F) : ℕ → F :=
  fun p => if h : p < r then Φ.out x (a ⟨p, h⟩) * Ψ.out y (b ⟨p, h⟩) else 0

end MatMulDS


