-- Prove2me | Definitions.Def_AffDisp4n_Src
-- name    : AffDisp4n_Src
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:31.162043+00:00
-- url     : https://prove2.me/theorems/24f29e4d-f875-4dd7-b68f-838d45e492cd
-- title:
--   Inputs and output of a straight-line $B_2$-circuit
-- statement:
--   A gate of a straight-line circuit reads two **sources**, and the circuit's output is a source too. Let $V$ index the inputs of the circuit and let $k$ be the number of gates listed before the gate in question. A source is one of the following:
--
--   1. a constant $c \in \mathbb F_2$;
--   2. an input $v \in V$: a variable $X_i$ in an ordinary circuit, or a parameter or an auxiliary variable in a fair semi-circuit;
--   3. an earlier gate $j < k$.
--
--   Given values for the inputs and for the earlier gates, a source has a value in $\mathbb F_2$. Renaming the inputs along a map $V \to V'$ renames the sources.
--
--   This is the wiring vocabulary shared by $B_2$-circuits and by the acyclic part of a fair semi-circuit.
--
--   **Formalization Note** $\{0,1\}$ is identified with $\mathbb F_2$ = `ZMod 2`, as in the paper (§2.1, p.12).
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, pp.12–13; §2.3 (ii)–(iii), pp.13–14

import Mathlib

namespace AffDisp4n

/-- An **input of a gate**, or the **output**, of a straight-line B₂-circuit whose inputs are
indexed by `V` and that has `k` earlier gates (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, pp.12–13, and §2.3 (ii)–(iii),
pp.13–14): a constant `const c` with `c ∈ 𝔽₂`, an input `input v` (a variable; in a fair
semi-circuit, a parameter or an auxiliary variable), or an earlier gate `gate j` with `j < k`.

**Formalization Note** `{0,1}` is identified with `𝔽₂ = ZMod 2`, as on p.12. -/
inductive Src (V : Type) (k : ℕ) where
  /-- a constant `c ∈ 𝔽₂` -/
  | const (c : ZMod 2)
  /-- an input `v ∈ V` -/
  | input (v : V)
  /-- an earlier gate `j < k` -/
  | gate (j : Fin k)

/-- The value of a source, given the values `x` of the inputs and `y` of the earlier gates. -/
def Src.val {V : Type} {k : ℕ} (x : V → ZMod 2) (y : Fin k → ZMod 2) : Src V k → ZMod 2
  | .const c => c
  | .input v => x v
  | .gate j => y j

/-- A source is a gate. -/
def Src.IsGate {V : Type} {k : ℕ} : Src V k → Prop
  | .gate _ => True
  | _ => False

/-- Renaming the inputs of a source along `e : V → V'`. -/
def Src.map {V V' : Type} {k : ℕ} (e : V → V') : Src V k → Src V' k
  | .const c => .const c
  | .input v => .input (e v)
  | .gate j => .gate j

end AffDisp4n


