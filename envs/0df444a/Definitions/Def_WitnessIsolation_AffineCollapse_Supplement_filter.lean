-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_filter
-- name    : WitnessIsolation_AffineCollapse_Supplement_filter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:34.763977+00:00
-- url     : https://prove2.me/theorems/38f78176-a9d2-4cbc-915a-c8070e0a8b7a
-- title:
--   The one-equation filter
-- statement:
--   Fix a valid description $H$ with $n$ declared variables, a vector $a\in\mathbb F_2^n$ and a bit $b\in\mathbb F_2$. The **one-equation filter** produces the description $H\wedge[\langle a,x\rangle=b]$ on the same $n$ ordered variables: the gates of $H$ are kept, a constant-false accumulator is appended, and for each coordinate $i$ seven gates compute $a_i\wedge x_i$ and XOR it into the accumulator (the XOR uses two negations, two conjunctions and a disjunction); a negation is added when $b=0$, and a final conjunction with the output of $H$ is the new output. Here $\langle a,x\rangle=\bigoplus_i a_ix_i$, false is $0$ and true is $1$; $a=0$ is allowed.
--
--   A pruning family $I$ **implements the filter** if, at every input length $L$, its random tape has $L+1$ bits and, for every input that decodes to a description $H$ with $n$ variables (so $n\le L$), its output decodes to $H\wedge[\langle a,x\rangle=b]$, where $a$ is read from tape bits $0,\dots,n-1$ and $b$ from tape bit $L$. A uniform tape therefore gives uniform independent $(a,b)\in\mathbb F_2^n\times\mathbb F_2$.
--
--   This is the transformation of the converse clause of Theorem 1.4. The facts that the construction computes $H\wedge[\langle a,x\rangle=b]$, that a polynomial-size implementing family exists, and that it succeeds with probability exactly $1/2$ on one- and two-solution inputs are clauses of `two_point_threshold`, not of this definition.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 3, PDF p. 4, Theorem 1.4 (converse clause); proof p. 9, PDF p. 10

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- XOR of wires i,j, using five ordinary bounded-fan-in gates at fresh wire k. -/
def xorGates (i j k : ℕ) : List Gate :=
  [.neg i, .neg j, .conj i (k+1), .conj k j, .disj (k+2) (k+3)]

/-- Append a seven-gate parity update per coordinate, after a false accumulator. -/
def equationGates (n g : ℕ) (a : Bits n) : List Gate :=
  [.const false] ++ (List.finRange n).flatMap (fun i =>
    let k := n+g+1+7*i.val
    [.const (a i), .conj i.val k] ++
      xorGates (k+1) (if i.val=0 then n+g else k-1) (k+2))

def equationFilter (d : Description) (a : Bits d.inputs) (b : Bool) : Description :=
  let endParity := d.inputs+d.gates.length+7*d.inputs
  let eq := if b then [] else [.neg endParity]
  let eqWire := if b then endParity else endParity+1
  ⟨d.inputs, d.gates ++ equationGates d.inputs d.gates.length a ++ eq ++
    [.conj d.output eqWire], d.inputs+d.gates.length+1+7*d.inputs+eq.length⟩

/-- Dot product in F₂, with false=0 and true=1, including the zero a. -/
def dotBit {n : ℕ} (a x : Bits n) : Bool :=
  (List.finRange n).foldl (fun b i => Bool.xor b (a i && x i)) false

/-- `I` implements the one-equation filter `H ↦ H ∧ [⟨a,x⟩ = b]` of Theorem 1.4
(printed p. 3 / PDF p. 4): on input length `L` the tape has `L+1` bits, `a` is read from
bits `0,…,n-1` (`n ≤ L` for every decodable input, so the `% (L+1)` is the identity) and
`b` from bit `L`. Unused bits are ignored, so `(a,b)` is uniform on `F₂ⁿ × F₂`, `a = 0`
included. -/
def ImplementsEquationFilter (I : PruningFamily) : Prop :=
  ∀ L, ∃ e : I.randomLength L = L+1,
    ∀ (h : Bits L) (d : Description), decode (List.ofFn h) = some d →
    ∀ r : Bits (L+1),
      decode (I.run L h (fun i => r ⟨i.val, by omega⟩)) =
        some (equationFilter d
          (fun i => r ⟨i.val % (L+1), Nat.mod_lt _ (by omega)⟩) (r ⟨L, by omega⟩))

end WitnessIsolation.AffineCollapse.Supplement


