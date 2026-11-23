-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Supplement_Encoding
-- name    : SkutellaCQP_MaxSNP_Supplement_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:46:00.305625+00:00
-- url     : https://prove2.me/theorems/73227bd2-18eb-40e0-b7b9-0f13586e04c0
-- title:
--   Finite binary encodings and uniform polynomial-time maps
-- statement:
--   Natural numbers are written in self-delimiting binary, integers with a sign bit, rationals with their reduced numerator and positive denominator, and lists with their lengths followed by their entries. These codes retain arbitrary finite rational data without a unary-magnitude restriction.
--
--   For explicitly encoded types, a map $f$ is polynomial-time when a single finite-alphabet Turing machine transforms the code of every input into the code of its image:
--   $$F(\operatorname{enc}(x))=\operatorname{enc}(f(x)).$$
--   The running-time bound is uniform over all input sizes. This module uses the published finite-alphabet polynomial-time predicate; it supplies no assumed optimization algorithm or correctness certificate.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), DOI 10.1145/375827.375840, pp. 3, 9, 14, 23, 33; approximation and polynomial-time transformations

import Mathlib
import Definitions.Def_Grunbaum2003_ContainmentPolyTime

namespace SkutellaCQP.MaxSNP.Supplement

/-- Self-delimiting binary natural number: unary length of the binary digits, delimiter,
then the digits. The magnitude is encoded in binary, not unary. -/
def natCode (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- Sign and magnitude of an integer. -/
def intCode (z : ℤ) : List Bool := (decide (z < 0)) :: natCode z.natAbs

/-- Reduced numerator and positive denominator of a rational. -/
def ratCode (q : ℚ) : List Bool := intCode q.num ++ natCode q.den

/-- A self-delimiting list of self-delimiting codes. -/
def listCode {α : Type} (e : α → List Bool) (xs : List α) : List Bool :=
  natCode xs.length ++ xs.flatMap e

/-- Pairing of arbitrary bit strings. -/
def wordPair (x y : List Bool) : List Bool := listCode (listCode fun b : Bool => [b]) [x, y]

/-- Standard polynomial-time computability between explicitly encoded types.
The witness is an actual uniform finite multi-stack Turing machine through the reused
published `ContainmentPolyTime`, not a cost annotation on an arbitrary function. -/
def PolyMap {α β : Type} (eα : α → List Bool) (eβ : β → List Bool) (f : α → β) : Prop :=
  ∃ F : List Bool → List Bool, Grunbaum2003.ContainmentPolyTime F ∧
    ∀ x, F (eα x) = eβ (f x)

/-- Polynomial-time computation on valid encodings. The string machine is total and
polynomial-time on all strings; only its interpretation is restricted to valid instances.
This avoids requiring exponentially long outputs on malformed succinct input records. -/
def PolyMapOn {α β : Type} (valid : α → Prop) (eα : α → List Bool)
    (eβ : β → List Bool) (f : α → β) : Prop :=
  ∃ F : List Bool → List Bool, Grunbaum2003.ContainmentPolyTime F ∧
    ∀ x, valid x → F (eα x) = eβ (f x)

end SkutellaCQP.MaxSNP.Supplement


