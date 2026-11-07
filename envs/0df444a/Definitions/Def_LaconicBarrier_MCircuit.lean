-- Prove2me | Definitions.Def_LaconicBarrier_MCircuit
-- name    : LaconicBarrier_MCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:12.832323+00:00
-- url     : https://prove2.me/theorems/21496655-1f6e-4b04-85fc-ce888cf3f260
-- title:
--   Multi-output Boolean circuits, their size and their description
-- statement:
--   A **circuit with $n$ inputs and several outputs** is a published single-output circuit (constants, NOT, AND, OR gates in topological order; wire $i<n$ is input $i$, wire $n+g$ is gate $g$) together with a list of output wires. Its value on $x \in \{0,1\}^n$ is the list of the values of the output wires; its **size** is the number of gates plus the number of outputs.
--
--   Its **description** is the tuple of $1^n$, $1^s$ ($s$ the number of gates), the fixed code of its gates and the output wires in binary; it is injective and decodable in polynomial time.
--
--   Two string conventions are fixed: a fixed-length output $u10\cdots0$ is read as the string $u$ (an all-zero output as the empty string), and a string $s$ is fed to a circuit with $n$ inputs as $s10\cdots0$ cut or padded to length $n$.
--
--   **Formalization Note** The size counts gates and outputs; any standard size measure differs by at most a polynomial, which the mission's hardness notions ("for every constant $K$") absorb.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.2, p.15 (adversary circuits); Definition 4.15, p.22 (sampler descriptions)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit
import Definitions.Def_KarpLiptonOM_circuitCode
import Definitions.Def_KarpLiptonOM_binW
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_LaconicBarrier_RunsWithin

namespace LaconicBarrier

open KarpLiptonOM

/-- A Boolean circuit with `n` inputs and several outputs (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), Definition 4.2, p.15: adversaries of "circuit size
`|A_λ| ≤ Γ(λ)`"; Definition 4.15, p.22: advice samplers given by "a Boolean-circuit description"):
a published single-output circuit `base` (gates in topological order) together with the list `outs`
of wires read as outputs. Wire `i < n` is input `i`, wire `n + g` is gate `g`. -/
structure MCircuit (n : ℕ) where
  /-- the gates -/
  base : Circuit n
  /-- the output wires, in order -/
  outs : List ℕ
  /-- every output wire exists -/
  outs_wf : ∀ i ∈ outs, i < n + base.gates.length

/-- The values of all wires on input `x` (inputs, then the gates in order), by the fold of the
published `Circuit.eval`. -/
def MCircuit.wires {n : ℕ} (C : MCircuit n) (x : List Bool) : List Bool :=
  C.base.gates.foldl (fun vals g => vals ++ [match g with
      | .const b => b
      | .not i => !(vals.getD i false)
      | .and i j => vals.getD i false && vals.getD j false
      | .or i j => vals.getD i false || vals.getD j false]) x

/-- The output string of the circuit on input `x ∈ {0,1}ⁿ`: the values of the output wires. -/
def MCircuit.eval {n : ℕ} (C : MCircuit n) (x : List Bool) : List Bool :=
  C.outs.map (fun i => (C.wires x).getD i false)

/-- The size of the circuit: gates plus output wires. -/
def MCircuit.size {n : ℕ} (C : MCircuit n) : ℕ := C.base.gates.length + C.outs.length

/-- The description of the circuit: the tuple of `1ⁿ`, `1^s` (`s` gates), the fixed code of its gates
(`circuitCode`) and the output wires in binary with `⌈log₂(n + s + 1)⌉` digits. The code is
injective and decodable in polynomial time. -/
def MCircuit.code {n : ℕ} (C : MCircuit n) : List Bool :=
  QAdvFew.PoQOracle.tup ([unary n, unary C.base.gates.length,
    circuitCode n C.base.gates.length C.base] ++
    C.outs.map (binW (Nat.size (n + C.base.gates.length))))

/-- Reading a circuit's fixed-length output as a string of any length: strip the trailing zeros and
then the final `1` (the output `u10⋯0` stands for `u`; an all-zero output stands for the empty
string). -/
def unpadOut (o : List Bool) : List Bool :=
  ((o.reverse.dropWhile (fun b => !b)).drop 1).reverse

/-- Feeding a string to a circuit with `n` inputs: `s10⋯0` cut or padded to length `n`. -/
def padIn (n : ℕ) (s : List Bool) : List Bool :=
  (s ++ true :: List.replicate n false).take n

end LaconicBarrier


