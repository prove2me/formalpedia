-- Prove2me | Definitions.Def_ObfEF_Incremental_Encoding
-- name    : ObfEF_Incremental_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:56:07.453715+00:00
-- url     : https://prove2.me/theorems/ae8574a1-e0f0-4c98-809c-eacb538ff9e0
-- title:
--   Binary encodings of circuits, formulas and proofs for the algorithm of Lemma 3.6
-- statement:
--   Lemma 3.6 asserts a polynomial-time algorithm that reads two circuits and an Extended Frege proof and writes a derivation. These are the fixed bit-string encodings it works on.
--
--   1. A natural number $k$ is written in self-delimiting binary: each bit $b$ of $k$ (least significant first) as $1b$, closed by $0$.
--   2. A formula is written in prefix notation: a variable $x_v$ as $00$ followed by the code of $v$; $\bot$ as $01$; $\varphi\to\psi$ as $1$ followed by the codes of $\varphi$ and $\psi$.
--   3. A list is written element by element, each preceded by $1$, and closed by $0$.
--   4. A circuit is written as the codes of $il$, $ol$ and $|C|$, then the operation of every noninput vertex in order ($\mathrm{const}\ b\mapsto 00b$, $\mathrm{NOT}\ a\mapsto01a$, $\mathrm{AND}\ a\,b\mapsto10ab$, $\mathrm{OR}\ a\,b\mapsto11ab$, a vertex being $0$ + an input index or $1$ + a noninput index), then the output vertices.
--   5. The input of Lemma 3.6's algorithm is the code of $C_0$, followed by the code of $C_1$ and the code of the proof (a list of formulas); its output is the code of the derivation (a list of formulas).
--
--   All codes are prefix-free and have length linear in the size of the object times the bit length of its largest index, so polynomial time in the code length is polynomial time in the usual sense.
--
--   **Formalization Note.** `Enc.nat`, `Enc.fml`, `Enc.list`, `Enc.circuit`, `Enc.lemma36Input`.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 49, Lemma 3.6 (the algorithm's input and output); p. 24 (algorithms)

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_Formula

/-!
# Binary encodings of numbers, formulas, proofs and circuits (for Lemma 3.6)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), p. 49, Lemma 3.6
("a polynomial-time algorithm that … maps every EF proof … to a derivation"), and p. 24
(algorithms).

The algorithm of Lemma 3.6 reads the two circuits and the proof and writes the derivation. These
are the fixed bit-string encodings it works on. All are prefix-free; numbers are written in binary
(each bit `b` of `Nat.bits k`, least significant first, as `1b`, closed by `0`), so the length of a
code is linear in the size of the object times the bit length of its largest index.
-/

namespace ObfEF.Incremental

namespace Enc

/-- A natural number in self-delimiting binary. -/
def nat (k : ℕ) : List Bool := (k.bits.flatMap fun b => [true, b]) ++ [false]

/-- A formula in prefix (Polish) notation: `var v ↦ 00·nat v`, `⊥ ↦ 01`, `φ → ψ ↦ 1·φ·ψ`. -/
def fml : Fml → List Bool
  | .var v => [false, false] ++ nat v
  | .bot => [false, true]
  | .imp φ ψ => true :: (fml φ ++ fml ψ)

/-- A list: every element preceded by `1`, the list closed by `0`. -/
def list {α : Type} (e : α → List Bool) (l : List α) : List Bool :=
  (l.flatMap fun a => true :: e a) ++ [false]

/-- A vertex of a circuit with inputs `Fin il`: `v_r ↦ 0·nat r`, noninput `j ↦ 1·nat j`. -/
def vertex {il j : ℕ} : Fin il ⊕ Fin j → List Bool
  | .inl r => false :: nat r
  | .inr j' => true :: nat j'

/-- An operation: `const b ↦ 00b`, `NOT a ↦ 01·a`, `AND a b ↦ 10·a·b`, `OR a b ↦ 11·a·b`. -/
def op {il j : ℕ} : Op (Fin il ⊕ Fin j) → List Bool
  | .const b => [false, false, b]
  | .not a => [false, true] ++ vertex a
  | .and a b => [true, false] ++ vertex a ++ vertex b
  | .or a b => [true, true] ++ vertex a ++ vertex b

/-- A circuit: `il`, `ol`, `|C|`, the operations of its noninput vertices in order, and its outputs. -/
def circuit {il ol : ℕ} (C : Circuit (Fin il) ol) : List Bool :=
  nat il ++ nat ol ++ nat C.size ++
    ((List.finRange C.size).flatMap fun j => op (C.op j)) ++
    ((List.finRange ol).flatMap fun k => vertex (C.out k))

/-- The input of the algorithm of Lemma 3.6: the codes of `C₀`, `C₁` and the proof `π`. -/
def lemma36Input {il ol : ℕ} (C₀ C₁ : Circuit (Fin il) ol) (π : List Fml) : List Bool :=
  circuit C₀ ++ circuit C₁ ++ list fml π

end Enc

end ObfEF.Incremental


