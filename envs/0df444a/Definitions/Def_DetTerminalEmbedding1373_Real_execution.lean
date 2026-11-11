-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_execution
-- name    : DetTerminalEmbedding1373_Real_execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:08.852201+00:00
-- url     : https://prove2.me/theorems/4d97ae20-fa54-4def-808b-b8b2175e9bcb
-- title:
--   Input layouts and the single map denoted by the two programs
-- statement:
--   Input coordinates occupy finite row-major arrays; every other input cell is zero. Separate layouts supply signing tests, correlation pairs, and terminal coordinates. Output vectors are read directly from the executed program's output array. Define one persistent state and one map by
--
--   $$D=\operatorname{runToHalt}(P_{\rm pre},X,\varepsilon,S),\qquad F_D(q)=\operatorname{output}(\operatorname{runToHalt}(P_{\rm query},D,q)).$$
--
--   Each query starts with the same persistent state $D$, fresh registers and the supplied query array. The denotation has a total fallback for nonhalting computations, but all algorithmic targets assert actual halting for every admissible input and every real query. This interface makes the map an output of fixed finite code, rather than an arbitrary family of separately chosen query images.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 3–4, 20–22, Theorem 1.1, Sections 5–6 two-phase construction; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_potential
import Definitions.Def_DetTerminalEmbedding1373_Real_solver
import Definitions.Def_DetTerminalEmbedding1373_Real_signingProgram
import Definitions.Def_DetTerminalEmbedding1373_Real_solverProgram
import Definitions.Def_DetTerminalEmbedding1373_Real_preprocessingProgram
import Definitions.Def_DetTerminalEmbedding1373_Real_queryProgram

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real

/-- Row-major input layout, zero outside its finite array. Input placement is not
an algorithmic oracle: each cell holds exactly one input coordinate. -/
noncomputable def packMatrix {n d : ℕ} (x : Fin n → E d) (z : ℤ) : ℝ :=
  ∑ i, ∑ j, if z = ((i.val * d + j.val : ℕ) : ℤ) then x i j else 0

noncomputable def packScalars {n : ℕ} (x : Fin n → ℝ) (z : ℤ) : ℝ :=
  ∑ i, if z = (i.val : ℤ) then x i else 0

def freshMachine (rs : ℕ → ℤ → ℝ) (is : ℕ → ℤ → ℤ) : MachineState :=
  ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, rs, is, false, 0⟩

noncomputable def signingInput {L d : ℕ} (m : ℕ) (v : Fin L → E d)
    (δ : Fin L → ℝ) : MachineState :=
  freshMachine (fun bank => if bank = 7 then packMatrix v
    else if bank = 8 then packScalars δ else fun _ => 0)
    (fun bank z => if bank = 0 then
      if z = 0 then (d : ℤ) else if z = 1 then (m : ℤ)
      else if z = 2 then (L : ℤ) else 0 else 0)

noncomputable def computedSignMatrix {L d : ℕ} (m : ℕ) (v : Fin L → E d)
    (δ : Fin L → ℝ) : Matrix (Fin m) (Fin d) ℝ :=
  fun i j => (finalState signingProgram (signingInput m v δ)).reals 9
    ((i.val * d + j.val : ℕ) : ℤ)

noncomputable def computedProjection {L d : ℕ} (m : ℕ) (v : Fin L → E d)
    (δ : Fin L → ℝ) : E d →ₗ[ℝ] E m :=
  Matrix.toEuclideanLin (fun i j =>
    (finalState signingProgram (signingInput m v δ)).reals 11
      ((i.val * d + j.val : ℕ) : ℤ))

noncomputable def solverInput {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ)
    (η : ℝ) : MachineState :=
  freshMachine (fun bank => if bank = 0 then fun z => if z = 0 then η else 0
    else if bank = 60 then packMatrix a else if bank = 61 then packScalars c else fun _ => 0)
    (fun bank z => if bank = 0 then
      if z = 0 then (N : ℤ) else if z = 1 then (m : ℤ) else 0 else 0)

noncomputable def outputVector (s : MachineState) (bank m : ℕ) : E m :=
  WithLp.toLp 2 (fun j => s.reals bank (j.val : ℤ))

noncomputable def computedSolution {N m : ℕ} (a : Fin N → E m) (c : Fin N → ℝ)
    (η : ℝ) : E m :=
  outputVector (finalState solverProgram (solverInput a c η)) 63 m

noncomputable def preprocessingInput {n d : ℕ} (x : Fin n → E d) (ε : ℝ)
    (S : ℕ) : MachineState :=
  freshMachine (fun bank => if bank = 0 then fun z => if z = 0 then ε else 0
    else if bank = 1 then packMatrix x else fun _ => 0)
    (fun bank z => if bank = 0 then
      if z = 0 then (n : ℤ) else if z = 1 then (d : ℤ)
      else if z = 2 then (S : ℤ) else 0 else 0)

/-- One preprocessed state, independent of all future query points. -/
noncomputable def preprocess {n d : ℕ} (x : Fin n → E d) (ε : ℝ) (S : ℕ) : MachineState :=
  finalState preprocessingProgram (preprocessingInput x ε S)

/-- A fresh evaluation starts from the same persistent data; query placement
changes only input bank 2. All scratch values read by queryProgram are initialized
by its instructions. Registers and the instruction counter start at zero. -/
noncomputable def queryInput {d : ℕ} (D : MachineState) (q : E d) : MachineState :=
  freshMachine (Function.update D.reals 2 (packScalars (fun j => q j))) D.ints

/-- The single map denoted by the fixed query program on the fixed state D.
Nonhalting has a totalized denotation; every goal instance proves halting for all q. -/
noncomputable def embedding {d : ℕ} (D : MachineState) (M : ℕ) (q : E d) : E M :=
  outputVector (finalState queryProgram (queryInput D q)) 70 M

end DetTerminalEmbedding1373.Real


