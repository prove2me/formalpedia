-- Prove2me | Definitions.Def_PvsNP_complexity_classes
-- name    : PvsNP_complexity_classes
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T01:02:46.905075+00:00
-- url     : https://prove2.me/theorems/f11fc272-7ccc-49f6-87ab-438611f32c11
-- title:
--   The complexity classes $\mathsf{P}$, $\mathsf{NP}$ and $\mathsf{coNP}$
-- statement:
--   A **decision problem** is a function $L : \{0,1\}^* \to \{\mathrm{true}, \mathrm{false}\}$, i.e. a language given by its characteristic function; a **complexity class** is a set of decision problems.
--
--   A function $f : \alpha \to \beta$ between types carrying bitstring encodings is **polynomial-time computable** if some two-stack Turing machine computes $f$ on the encoded inputs within a number of steps bounded by a polynomial in the input length (Mathlib's `Turing.TM2ComputableInPolyTime`).
--
--   $$\mathsf{P} = \{\, L \;:\; L \text{ is polynomial-time computable} \,\}$$
--
--   $$\mathsf{NP} = \{\, L \;:\; \exists\, p \in \mathbb{N}[X],\ \exists\, R : \{0,1\}^* \times \{0,1\}^* \to \{\mathrm{true},\mathrm{false}\} \text{ polynomial-time computable},\ \forall x,\ L(x) = \mathrm{true} \iff \exists\, w,\ |w| \le p(|x|) \wedge R(x,w) = \mathrm{true} \,\}$$
--
--   This is the verifier definition of $\mathsf{NP}$ (Arora–Barak, Definition 2.1): the witness $w$ is a bitstring of length at most $p(|x|)$ and the verifier $R$ runs in polynomial time in the length of its (encoded) pair input.
--
--   $$\mathsf{coNP} = \{\, L \;:\; L^{\mathrm{c}} \in \mathsf{NP} \,\},$$ where $L^{\mathrm{c}}$ is the pointwise Boolean negation of $L$.
-- source:
--   Sanjeev Arora and Boaz Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009; google-deepmind/formal-conjectures, FormalConjectures/Millennium/PvsNP.lean and FormalConjecturesForMathlib/Computability/Complexity.lean, https://github.com/google-deepmind/formal-conjectures

import Definitions.Def_PvsNP_bitstring_encoding
import Mathlib.Computability.TuringMachine.Computable

/-!
# Complexity classes P, NP and coNP

Decision problems are Boolean-valued functions on bitstrings, complexity classes are sets of
decision problems, and polynomial-time computability is the notion
`Turing.TM2ComputableInPolyTime` from Mathlib, taken with respect to the canonical bitstring
encodings.

Adapted from the `FormalConjecturesForMathlib.Computability.Complexity` file of the
`google-deepmind/formal-conjectures` project (Apache License 2.0), following
Arora–Barak, *Computational Complexity: A Modern Approach* (2009), Definitions 1.13 and 2.1.
-/

open Computability Turing

namespace PvsNP

/-- The type of decision problems: predicates on bitstrings, valued in `Bool`. -/
abbrev DecisionProblem := List Bool → Bool

/-- The type of complexity classes: sets of decision problems. -/
abbrev DecisionComplexityClass := Set DecisionProblem

/-- `IsPolyTimeWithEncoding ea eb f` asserts that `f` is computable in polynomial time by a
two-stack Turing machine when its input and output are encoded via `ea` and `eb`. -/
def IsPolyTimeWithEncoding {α β Γα Γβ : Type} (ea : Encoding α Γα) (eb : Encoding β Γβ)
    (f : α → β) : Prop :=
  Nonempty (TM2ComputableInPolyTime ea.encode eb.encode f)

/-- A function between types with canonical bitstring encodings is polynomial-time computable
if it is computable in polynomial time with respect to those encodings. -/
def IsPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β) : Prop :=
  IsPolyTimeWithEncoding (BitstringEncoding.toEncoding (α := α))
    (BitstringEncoding.toEncoding (α := β)) f

/-- The class `P`: decision problems decidable in polynomial time by a deterministic Turing
machine. -/
def P : DecisionComplexityClass :=
  { L | IsPolyTime L }

/-- The class `NP`: decision problems `L` for which there is a polynomial `p` and a
polynomial-time verifier `R` such that `L x = true` if and only if some witness `w` of length
at most `p |x|` satisfies `R (x, w) = true`. -/
def NP : DecisionComplexityClass :=
  { L | ∃ (p : Polynomial ℕ), ∃ R : (List Bool × List Bool) → Bool,
      IsPolyTime R ∧
      ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w) }

/-- The class `coNP`: decision problems whose pointwise complement lies in `NP`. -/
def coNP : DecisionComplexityClass :=
  { L | Lᶜ ∈ NP }

end PvsNP


