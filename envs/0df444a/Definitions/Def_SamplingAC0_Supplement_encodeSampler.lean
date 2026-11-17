-- Prove2me | Definitions.Def_SamplingAC0_Supplement_encodeSampler
-- name    : SamplingAC0_Supplement_encodeSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:40:25.805947+00:00
-- url     : https://prove2.me/theorems/fdc571e0-f9b1-4a81-987e-82d1ff660bcf
-- title:
--   Binary description of an AC$^0$ sampler
-- statement:
--   The **description** of an AC$^0$ sampler is a binary string listing the number $\ell$ of outputs, the number $m$ of inputs, and then each output circuit: its gates in order (each as its type, AND or OR, followed by the list of its inputs) and finally its output. A gate input is written with a tag saying whether it is a literal $x_j$ or $\neg x_j$, a constant, or an earlier gate, followed by its index or value. Numbers are written in unary ($k$ ones followed by a zero), so every component is self-delimiting and the description determines the sampler.
--
--   Theorem 7's clause "the circuit can be constructed efficiently" asks for a polynomial-time algorithm that outputs this description.
--
--   **Formalization Note** Indices and lengths are unary. For circuits with polynomially many inputs, gates and wires the description has polynomial length and is convertible to and from a binary-index description in polynomial time, so polynomial-time constructibility means the same for either. Injectivity of the code is proved in the mission's sanity checks.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7 p.4

import Mathlib
import Definitions.Def_SamplingAC0_Supplement_ACSampler
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- Self-delimiting code of a natural number `k`: `k` ones followed by a zero. -/
def encNat (k : ℕ) : List Bool :=
  List.replicate k true ++ [false]

/-- Code of a length-prefixed list: its length, then the codes of its entries. -/
def encList {α : Type} (e : α → List Bool) (l : List α) : List Bool :=
  encNat l.length ++ l.flatMap e

/-- Code of a gate input: tag `00` + variable index + polarity for a literal, tag `01` + value for a
constant, tag `1` + gate index for an earlier gate. -/
def encSrc {m : ℕ} : MantriCVQ.Src (Fin m) → List Bool
  | .lit v b => [false, false] ++ encNat v.val ++ [b]
  | .const b => [false, true, b]
  | .gate i => [true] ++ encNat i

/-- Code of a gate: its type bit (`true` = AND), then its list of inputs. -/
def encGate {m : ℕ} (g : MantriCVQ.ACGate (Fin m)) : List Bool :=
  [g.isAnd] ++ encList encSrc g.inputs

/-- Code of a circuit: its list of gates, then its output. -/
def encCircuit {m : ℕ} (C : MantriCVQ.ACCircuit (Fin m)) : List Bool :=
  encList encGate C.gates ++ encSrc C.output

/-- **Binary description of an AC0 sampler.** Riazanov–Viola, *Sampling Tools and the Power of
AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7, p.4 ("The circuit can be
constructed efficiently"): the string a construction algorithm outputs.

`encodeSampler C` lists the number of outputs `ℓ`, the number of inputs `m`, and then the code of
each output circuit in order. Every component is self-delimiting, so the code is injective.

**Formalization Note.** Numbers (indices, lengths, `ℓ`, `m`) are written in unary. For a circuit
whose number of inputs, gates and wires is polynomial this code has polynomial length, and it is
convertible to and from a binary-index code in polynomial time, so "computable in polynomial time"
means the same for either code. -/
def encodeSampler {ℓ : ℕ} (C : ACSampler ℓ) : List Bool :=
  encNat ℓ ++ encNat C.m ++ (List.ofFn C.out).flatMap encCircuit

end SamplingAC0.Supplement


