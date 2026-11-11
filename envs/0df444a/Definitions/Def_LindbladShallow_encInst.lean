-- Prove2me | Definitions.Def_LindbladShallow_encInst
-- name    : LindbladShallow_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:21:03.585024+00:00
-- url     : https://prove2.me/theorems/b810bf6b-d21c-4496-b081-8be7b09eb78d
-- title:
--   Length-faithful encodings of inputs and circuit descriptions
-- statement:
--   Inputs and circuit descriptions are written as words over a six-letter alphabet $\{0,1,-,\mathrm{sep},[,]\}$: natural numbers in binary without leading zeros, integers with a sign, rationals as numerator and denominator, lists element by element between brackets, and local matrices entry by entry. The input word lists the sites, the terms (kind, ordered support, matrices) and $T,\epsilon$; the circuit word lists $f$, the offsets and, segment by segment, the auxiliary positions and the layers gate by gate.
--
--   These encodings make "time polynomial in the input and output-description lengths" (Theorem 2.1) a statement about a fixed machine.
--
--   **Formalization Note** The encodings are length-faithful: the length is proportional to the raw size of the data. A pairing-function code or unary numerals would make lengths exponentially longer and the time clause vacuous.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Theorem 2.1, p.10; App. C, p.70

import Mathlib
import Definitions.Def_LindbladShallow_Circuit

namespace LindbladShallow

/-- The finite alphabet of input and output descriptions: two bits, a minus sign, a separator and
two brackets. -/
inductive Sym
  | b0 | b1 | neg | sep | lb | rb
  deriving DecidableEq

/-- A natural number in binary, least significant bit first, without leading zeros
(`0` is the empty word). Length `⌊log₂ n⌋ + 1` for `n ≥ 1`. -/
def encNat (n : ℕ) : List Sym := (Nat.bits n).map fun b => if b then .b1 else .b0

/-- An integer: a minus sign if negative, then the binary numeral of `|z|`. -/
def encInt (z : ℤ) : List Sym := (if z < 0 then [.neg] else []) ++ encNat z.natAbs

/-- A bracketed list of words separated by `sep`: `[w₁ sep w₂ sep … w_k]`. -/
def encWords (ws : List (List Sym)) : List Sym := [Sym.lb] ++ List.intercalate [Sym.sep] ws ++ [Sym.rb]

/-- A rational number as `[numerator sep denominator]` (lowest terms, positive denominator). -/
def encRat (q : ℚ) : List Sym := encWords [encInt q.num, encNat q.den]

/-- A site of `ℤ^D` as the bracketed list of its coordinates. -/
def encSite {D : ℕ} (x : Fin D → ℤ) : List Sym := encWords ((List.ofFn x).map encInt)

/-- The basis configuration number `N` of the qubits of a support of `m` sites: bit
`(i, k)` is bit `i·d0 + k` of `N`. -/
def cfgOf (d0 m N : ℕ) : LocBasis d0 m := fun p => N.testBit (p.1.val * d0 + p.2.val)

/-- A `ℚ + iℚ` matrix written entry by entry, rows then columns, both in the order of the
configuration numbers `0, …, 2^{m·d0} − 1`; each entry is `[re sep im]`. -/
def encMat {d0 m : ℕ} (A : QIMat d0 m) : List Sym :=
  encWords ((List.range (2 ^ (m * d0))).flatMap fun N =>
    (List.range (2 ^ (m * d0))).map fun N' =>
      encWords [encRat (A (cfgOf d0 m N) (cfgOf d0 m N')).1,
        encRat (A (cfgOf d0 m N) (cfgOf d0 m N')).2])

/-- A term: a kind tag (`0` Hamiltonian, `1` dissipative), its ordered support, and its matrix or
its list of jump matrices. -/
def encTerm {P : Params} (t : Term P) : List Sym :=
  match t.data with
  | .ham H => encWords [[.b0], encWords (t.supp.map encSite), encMat H]
  | .jump L => encWords [[.b1], encWords (t.supp.map encSite), encWords (L.map encMat)]

/-- The input description (arXiv:2610.05362, §2.1, p.9): the site list, the ordered term list,
`T` and `ϵ`, all written explicitly.

**Formalization Note** The encoding is length-faithful: numerals are binary, lists are written
element by element, and matrices entry by entry, so its length is proportional to the raw input
size. (An `Encodable`/`Nat.pair` code or unary numerals would make lengths exponentially longer
and the time clause of Theorem 2.1 vacuous.) The fixed parameters `P` are not part of the input. -/
def encInst {P : Params} (I : Instance P) : List Sym :=
  encWords [encWords (I.sites.map encSite), encWords (I.terms.map encTerm), encRat I.T,
    encRat I.ε]

/-- The code of a one-qubit symbol (`0, …, 10`; `CX` has code `11`). -/
def GateName.code : GateName → ℕ
  | .H => 0 | .X => 1 | .Z => 2 | .S => 3 | .Sdg => 4 | .T => 5 | .Tdg => 6
  | .Ax => 7 | .Axdg => 8 | .Az => 9 | .Azdg => 10

/-- A gate: its symbol code and its position(s). -/
def encGate {D : ℕ} : Gate D → List Sym
  | .one g p => encWords [encNat g.code, encSite p]
  | .cx a b => encWords [encNat 11, encSite a, encSite b]

/-- A segment: its auxiliary positions, then its layers, each the list of its gates. -/
def encSeg {D : ℕ} (s : Segment D) : List Sym :=
  encWords [encWords (s.aux.map encSite),
    encWords (s.layers.map fun L => encWords (L.map encGate))]

/-- The output circuit description: `f`, the offsets `u_k`, and the segments, gate by gate
(arXiv:2610.05362, p.10: "A stored circuit lists its one- and two-qubit gates, wire indices …").
Length-faithful, like `encInst`. -/
def encCirc {P : Params} (c : Circuit P) : List Sym :=
  encWords [encNat c.f,
    encWords (List.ofFn fun k => encWords (List.ofFn fun i => encNat (c.u k i))),
    encWords (c.segs.map encSeg)]

end LindbladShallow


