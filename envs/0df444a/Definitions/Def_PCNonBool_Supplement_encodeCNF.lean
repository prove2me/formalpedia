-- Prove2me | Definitions.Def_PCNonBool_Supplement_encodeCNF
-- name    : PCNonBool_Supplement_encodeCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:26:07.002119+00:00
-- url     : https://prove2.me/theorems/12228272-5311-4e21-acd6-bef282edc581
-- title:
--   Binary encoding of CNF formulas
-- statement:
--   CNF formulas are written over a finite alphabet with two bits, three variable-kind marks, a separator and two end marks. A literal is its sign bit, the binary code of its variable index, and a separator; a clause is its literals followed by an end mark; a formula is its clauses in order.
--
--   The encoding is injective and its length is linear in the total bit length of the formula, so "polynomial time" with respect to it is polynomial time in the usual sense. It is the input and output format of the algorithm $A$ and of automating algorithms in Theorem 7.1.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_PCNonBool_Supplement_CNF

namespace PCNonBool.Supplement

/-- The tape alphabet of the encodings used for Theorem 7.1 (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53)): two bits,
three variable-kind marks, a separator and two end marks. -/
inductive Sym : Type
  | b0 | b1 | kw | kbar | kfour | sep | endM | endL
  deriving DecidableEq

instance : Fintype Sym :=
  ⟨{Sym.b0, Sym.b1, Sym.kw, Sym.kbar, Sym.kfour, Sym.sep, Sym.endM, Sym.endL}, by
    intro x; cases x <;> simp⟩

/-- A natural number in binary (Mathlib's `Computability.encodeNat`), written with `b0`, `b1`. -/
def encNat (v : ℕ) : List Sym :=
  (Computability.encodeNat v).map (fun b => if b then Sym.b1 else Sym.b0)

/-- A literal `(v, s)`: its sign bit, the binary code of `v`, then `sep`. -/
def encLit (l : Lit) : List Sym :=
  (if l.2 then Sym.b1 else Sym.b0) :: (encNat l.1 ++ [Sym.sep])

/-- A clause: its literals in order, then `endM`. -/
def encClause (C : Clause) : List Sym := C.flatMap encLit ++ [Sym.endM]

/-- The standard binary encoding of a CNF formula (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §7, p.50 (PDF p.53), the input and output
of the algorithm `A` and of an automating algorithm): the encodings of its clauses in order.

**Formalization Note** The encoding is injective (each literal ends in `sep`, each clause in
`endM`, and `encodeNat` is the canonical binary code), and its length is linear in the total
bit length of the formula, so polynomial time with respect to it is polynomial time in the
usual sense. -/
def encodeCNF (Φ : CNF) : List Sym := Φ.flatMap encClause

end PCNonBool.Supplement


