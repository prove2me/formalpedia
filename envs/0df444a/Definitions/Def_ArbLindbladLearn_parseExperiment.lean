-- Prove2me | Definitions.Def_ArbLindbladLearn_parseExperiment
-- name    : ArbLindbladLearn_parseExperiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:39.117014+00:00
-- url     : https://prove2.me/theorems/0e7a5774-225d-465d-9751-9ee20ec95ba7
-- title:
--   Operand layout of the experiment instruction
-- statement:
--   The experiment instruction reads two Clifford circuits from integer memory: a length $L$ followed by $L$ triples (kind $0=H$, $1=S$, $2=\mathrm{CNOT}$, then qubit indices in $[0,n)$, distinct for CNOT); the second circuit follows the first, and the $n$ outcome bits are written right after it. Malformed operands are rejected.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34; access model, §1.1, p.2

import Mathlib
import Definitions.Def_ArbLindbladLearn_Gate

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- Decode one gate from an integer triple `(kind, i, j)`: kind `0 = H_i`, `1 = S_i`,
`2 = CNOT_{ij}`; qubit indices must lie in `[0, n)` (and `i ≠ j` for `CNOT`); `j` is ignored for
`H`, `S`. Anything else is malformed. (Machine of Corollary 4.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
p.34.) -/
def parseGate (n : ℕ) (k i j : ℤ) : Option (Gate n) :=
  if hi : 0 ≤ i ∧ i < n then
    if k = 0 then some (.H ⟨i.toNat, by omega⟩)
    else if k = 1 then some (.S ⟨i.toNat, by omega⟩)
    else if k = 2 then
      (if hj : 0 ≤ j ∧ j < n ∧ i ≠ j then
        some (.CNOT ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩) else none)
    else none
  else none

/-- Decode a gate list stored at `base` in integer memory: a length `L ≥ 0` at `base`, then `L`
triples at `base + 1 + 3k`, `base + 2 + 3k`, `base + 3 + 3k`. -/
def parseCircuit (n : ℕ) (mem : ℤ → ℤ) (base : ℤ) : Option (List (Gate n)) :=
  if mem base < 0 then none else
    (List.range (mem base).toNat).mapM fun k =>
      parseGate n (mem (base + 1 + 3 * k)) (mem (base + 2 + 3 * k)) (mem (base + 3 + 3 * k))

/-- Decode the operands of an `experiment` at `base`: the preparation circuit `C₁`, then the
measurement circuit `C₂` stored right after it, and the address where the `n` outcome bits are
written (right after `C₂`). -/
def parseExperiment (n : ℕ) (mem : ℤ → ℤ) (base : ℤ) :
    Option (List (Gate n) × List (Gate n) × ℤ) :=
  match parseCircuit n mem base with
  | none => none
  | some C₁ =>
    let base₂ := base + 1 + 3 * (C₁.length : ℤ)
    match parseCircuit n mem base₂ with
    | none => none
    | some C₂ => some (C₁, C₂, base₂ + 1 + 3 * (C₂.length : ℤ))

end ArbLindbladLearn


