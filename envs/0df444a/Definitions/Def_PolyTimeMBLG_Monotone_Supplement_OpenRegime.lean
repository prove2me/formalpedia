-- Prove2me | Definitions.Def_PolyTimeMBLG_Monotone_Supplement_OpenRegime
-- name    : PolyTimeMBLG_Monotone_Supplement_OpenRegime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:33:02.888168+00:00
-- url     : https://prove2.me/theorems/74ac97bd-228a-4f10-bea3-b1ffefc40858
-- title:
--   §6 — polynomial-size circuits and polynomial-time MBLG in the open regime
-- statement:
--   A **Boolean circuit** $C$ on inputs $x_1,\dots,x_n$ is a sequence of gates, each a fan-in-two AND, a fan-in-two OR or a NOT gate reading inputs or earlier gates, with a designated output wire; its **size** is the number of gates. Its language is $C^{-1}(1)\subseteq\{0,1\}^n$. For a polynomial $p$, the **family of $p(n)$-size circuits** consists, for each $n$, of the circuits on $n$ inputs with at most $p(n)$ gates.
--
--   The **open regime** (§6, p. 9) is the MBLG game of §3 in which the adversary first reveals the circuit $C$ whose language it enumerates. An **open-regime generator** $G$ receives $1^n$, the circuit $C$ and the distinct words $x^1,\dots,x^i\in C^{-1}(1)$ printed so far, and returns a word of length $n$. It is **polynomial-time** if one Turing machine computes it within a number of steps polynomial in the length of the encoded input $(C,1^n,x^1\cdots x^i)$. Index $i\in\{0,\dots,|C^{-1}(1)|-1\}$ is a **mistake** when
--   $$G(C,1^n,x^1\cdots x^i)\notin C^{-1}(1)\setminus\{x^1,\dots,x^i\}.$$
--
--   The family of $p(n)$-size circuits is **polynomial-time MBLG in the open regime** if there are a polynomial $e$ and a polynomial-time open-regime generator $G$ such that for every $n\ge1$, every circuit $C$ on $n$ inputs of size at most $p(n)$ and every enumeration of $C^{-1}(1)$, $G$ makes at most $e(n)$ mistakes.
--
--   These notions are the intermediate step of the proof of Theorem 3: Lemma 14 derives them from generation for 3-CNFs, and Lemma 15 rules them out under one-way functions.
--
--   **Formalization Note** Circuits are the published `QCSepTotal.Circuit (Fin n)` (gates reference only inputs and earlier gates; no constant gates). A circuit is encoded over the alphabet `Option Bool` (size in unary, separator, gate codes with wire indices in unary, output wire), and the open-regime input is this code followed by the base encoding of $(1^n,x^1\cdots x^i)$; its length is polynomial in $n+\text{size}(C)$ plus $(n+1)(i+1)$. Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime`, required on every input, including circuits of any size and $n=0$. The size condition $|F_n|\le2^{\mathrm{poly}(n)}$ of Definition 6 is not repeated: there are at most $2^{O(p(n)\log(n+p(n)))}$ circuits on $n$ inputs with at most $p(n)$ gates, so it always holds. Polynomials $p$ and $e$ have natural coefficients.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), §6, paragraph before Lemma 14 (open regime) and Lemmas 14–15, p. 9; MBLG model, §3, Definitions 5–6, p. 5. PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Generation
import Definitions.Def_QCSepTotal_Circuit

namespace PolyTimeMBLG.Monotone.Supplement

open QCSepTotal

/-- The language `C⁻¹(1) ⊆ {0,1}ⁿ` of a Boolean circuit `C` with inputs `x₁, …, xₙ`
(fan-in-two AND/OR gates and NOT gates, size = number of gates: the published
`QCSepTotal.Circuit`). -/
def circuitLanguage {n : ℕ} (C : Circuit (Fin n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => C.eval x = true)

/-- A number in unary over the alphabet `Option Bool`. -/
def encUnary (m : ℕ) : List (Option Bool) := List.replicate m (some true)

/-- Code of a wire: `some false`, the input index in unary, `none` for an input `x_{i+1}`;
`some true`, the gate index in unary, `none` for an earlier gate. -/
def encWire {n k : ℕ} : Fin n ⊕ Fin k → List (Option Bool)
  | .inl i => some false :: encUnary i.val ++ [none]
  | .inr j => some true :: encUnary j.val ++ [none]

/-- Code of a gate: a tag (`some false, some false` for AND, `some false, some true` for OR,
`some true` for NOT) followed by the codes of the wires it reads. -/
def encGate {n k : ℕ} : Gate (Fin n) k → List (Option Bool)
  | .and a b => [some false, some false] ++ encWire a ++ encWire b
  | .or a b => [some false, some true] ++ encWire a ++ encWire b
  | .not a => some true :: encWire a

/-- Codes of the gates of a circuit, in order. -/
def encGates {n : ℕ} : {k : ℕ} → Gates (Fin n) k → List (Option Bool)
  | _, .nil => []
  | _, .snoc C g => encGates C ++ encGate g

/-- Code of a circuit over `Option Bool`: its size in unary, `none`, the gate codes in order,
and the code of the output wire. It is self-delimiting and has length polynomial in
`n + size C`. -/
def encodeCircuit {n : ℕ} (C : Circuit (Fin n)) : List (Option Bool) :=
  encUnary C.size ++ none :: encGates C.gates ++ encWire C.out

/-- A history in the open regime (§6, p. 9): a word length `n`, the circuit `C` with `n` inputs
revealed by the adversary at the start, and a duplicate-free sequence `x¹, …, xⁱ` of words of
length `n` printed so far. -/
structure OpenHistory where
  /-- the word length -/
  n : ℕ
  /-- the revealed circuit -/
  C : Circuit (Fin n)
  /-- the distinct words printed so far, in order -/
  xs : {xs : List (Fin n → Bool) // xs.Nodup}

/-- Input encoding of an open-regime history: the circuit code followed by the base encoding
`1ⁿ # x¹ # ⋯ # xⁱ #` of `(1ⁿ, x¹⋯xⁱ)`. -/
def encodeOpenHistory (h : OpenHistory) : List (Option Bool) :=
  encodeCircuit h.C ++ encodeHistory ⟨h.n, h.xs⟩

/-- An open-regime generator: given `1ⁿ`, the circuit `C` and the distinct words seen so far,
it returns a word of length `n`. -/
def OpenGenerator : Type := (h : OpenHistory) → (Fin h.n → Bool)

/-- The output word of an open-regime generator as a raw list of `n` bits. -/
def OpenGenerator.outputBits (G : OpenGenerator) (h : OpenHistory) : List Bool :=
  List.ofFn (G h)

/-- `G` is polynomial time: one finite TM2 machine computes its output bits from the encoded
input (circuit, `1ⁿ`, words) within `P(length of the encoding)` steps for one polynomial `P`, on
every input. -/
def OpenGenerator.IsPolyTime (G : OpenGenerator) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeOpenHistory id G.outputBits)

/-- Definition 5 (p. 5) in the open regime: the number of indices `i ∈ {0, …, |C⁻¹(1)| - 1}` at
which `G`, shown `C` and the first `i` words of the enumeration `xs` of `C⁻¹(1)`, outputs a word
outside `C⁻¹(1) \ {x¹, …, xⁱ}`. -/
def openMistakeCount (G : OpenGenerator) {n : ℕ} (C : Circuit (Fin n))
    (xs : List (Fin n → Bool)) (hxs : xs.Nodup) : ℕ :=
  ((Finset.range (circuitLanguage C).card).filter (fun i =>
    G ⟨n, C, ⟨xs.take i, hxs.sublist (List.take_sublist i xs)⟩⟩ ∉
      circuitLanguage C \ (xs.take i).toFinset)).card

/-- `G` makes at most `e(n)` mistakes on the `p(n)`-size circuits in the open regime: for every
`n ≥ 1`, every circuit `C` with `n` inputs and at most `p(n)` gates, and every enumeration of
`C⁻¹(1)` (a duplicate-free list whose set of entries is `C⁻¹(1)`), at most `e(n)` mistakes. -/
def OpenMakesAtMostMistakes (G : OpenGenerator) (p : Polynomial ℕ) (e : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ C : Circuit (Fin n), C.size ≤ p.eval n →
    ∀ (xs : List (Fin n → Bool)) (hxs : xs.Nodup),
      xs.toFinset = circuitLanguage C → (openMistakeCount G C xs hxs : ℝ) ≤ e n

/-- The family of `p(n)`-size circuits is polynomial-time MBLG in the open regime (§6, p. 9): one
polynomial-time open-regime generator makes at most `e(n)` mistakes on it for a polynomial `e`. -/
def IsOpenPolyTimeMBLG (p : Polynomial ℕ) : Prop :=
  ∃ e : Polynomial ℕ, ∃ G : OpenGenerator, G.IsPolyTime ∧
    OpenMakesAtMostMistakes G p (fun n => ((e.eval n : ℕ) : ℝ))

end PolyTimeMBLG.Monotone.Supplement


