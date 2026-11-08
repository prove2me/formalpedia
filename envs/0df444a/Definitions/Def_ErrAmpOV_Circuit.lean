-- Prove2me | Definitions.Def_ErrAmpOV_Circuit
-- name    : ErrAmpOV_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:39.649189+00:00
-- url     : https://prove2.me/theorems/795a7aca-e531-4f61-b837-2257d149151a
-- title:
--   Boolean circuits of fan-in at most 2, their size and evaluation
-- statement:
--   A **Boolean circuit** over a set $\iota$ of input bits is a list of gates and a list of output wires. A wire is either an input bit or the value of a numbered gate. A gate is a constant, the NOT of a wire, or the AND or OR of two wires, so its fan-in is at most 2, and its fan-out is unbounded.
--
--   Gates are numbered $0,1,\dots$ and evaluated in order. On input $x\in\{0,1\}^\iota$ the circuit outputs the values of its output wires, in order. The **size** of a circuit is its number of gates; input bits are not counted.
--
--   This is the computational model of every statement in the mission: deterministic circuits, the zero-error probabilistic circuits of Definition 2.1, and the multi-output routing circuits of Theorem 2.3.
--
--   **Formalization Note** The paper fixes no gate basis. A gate that reads a gate not yet computed, and an output that reads a gate number at least the size, read `false`. So every gate list is a circuit, with no well-formedness side condition, and the only effect is a free constant `false`, which changes sizes by at most one gate.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), §2.1, pp.5–6 (unnumbered circuit model)

import Mathlib

set_option autoImplicit false

namespace ErrAmpOV

/-!
# Boolean circuits: fan-in ≤ 2, many outputs, size = number of gates

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
§2.1, pp.5–6 (unnumbered: "deterministic Boolean circuits … has size S(n)"; the circuits of
Definition 2.1 and Theorem 2.3 have several output wires).

**Formalization Note.**
* The paper fixes no gate basis. Gates are constants, NOT (fan-in 1), AND and OR (fan-in 2);
  fan-out is unbounded. Any two complete fan-in-2 bases differ by a constant factor in size.
* Inputs are indexed by a type `ι` (e.g. `Fin 2 × Fin n × Fin d` for OV) and are not gates.
  `size` is the number of gates.
* Gates are numbered `0, 1, …` in list order; a wire is an input `inp i` or the value of gate
  `gate k`. Gate number `k` is evaluated after gates `0, …, k-1`. A gate that reads gate `j ≥ k`
  (not yet computed), and an output that reads a gate number `≥ size`, read `false`. So every
  gate list is a circuit, with no well-formedness side condition; the only effect is a free
  constant `false`, which changes sizes by at most one gate.
-/

/-- A wire: an input bit `inp i`, or the value of gate number `k`. -/
inductive Wire (ι : Type) : Type where
  | inp (i : ι)
  | gate (k : ℕ)

/-- A gate of fan-in at most 2: a constant, NOT, AND or OR of wires. -/
inductive Gate (ι : Type) : Type where
  | const (b : Bool)
  | not (a : Wire ι)
  | and (a b : Wire ι)
  | or (a b : Wire ι)

/-- A Boolean circuit over inputs indexed by `ι`: a list of gates (gate `k` is the `k`-th
entry) and a list of output wires. -/
structure Circuit (ι : Type) : Type where
  gates : List (Gate ι)
  outs : List (Wire ι)

/-- The value of a wire on input `x`, given the values `vals` of the gates computed so far;
a gate not (yet) computed reads `false`. -/
def Wire.read {ι : Type} (x : ι → Bool) (vals : List Bool) : Wire ι → Bool
  | .inp i => x i
  | .gate k => vals.getD k false

/-- The value of a gate on input `x`, given the values `vals` of the earlier gates. -/
def Gate.eval {ι : Type} (x : ι → Bool) (vals : List Bool) : Gate ι → Bool
  | .const b => b
  | .not a => !(a.read x vals)
  | .and a b => a.read x vals && b.read x vals
  | .or a b => a.read x vals || b.read x vals

/-- The size of a circuit: its number of gates (inputs are not counted). -/
def Circuit.size {ι : Type} (C : Circuit ι) : ℕ := C.gates.length

/-- The values of all gates on input `x`, in order. -/
def Circuit.values {ι : Type} (C : Circuit ι) (x : ι → Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [g.eval x vals]) []

/-- The output of a circuit on input `x`: the values of its output wires, in order. -/
def Circuit.eval {ι : Type} (C : Circuit ι) (x : ι → Bool) : List Bool :=
  C.outs.map (Wire.read x (C.values x))

end ErrAmpOV


