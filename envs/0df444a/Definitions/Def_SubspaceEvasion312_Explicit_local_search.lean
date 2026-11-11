-- Prove2me | Definitions.Def_SubspaceEvasion312_Explicit_local_search
-- name    : SubspaceEvasion312_Explicit_local_search
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:21.626522+00:00
-- url     : https://prove2.me/theorems/ab7e307a-35bc-43e4-90b0-a77fa6708517
-- title:
--   The deterministic conditional-expectation local map
-- statement:
--   Fix an ordered list containing every element of $F_q$ exactly once. It defines lexicographic enumerations of all vectors and all finite tuples. For local dimensions $s,b$, rank bound $r$, and forbidden intersection size $d$, enumerate $r$ generating vectors in $F_q^s\times F_q^b$ and ordered $d$-tuples of coefficient vectors in $F_q^r$. Their linear combinations describe every potential bad $d$-point configuration of rank at most $r$; duplicate descriptions are harmless.
--
--   Given a partial table for $f$, a configuration with repeated input coordinates or disagreement with an assigned value has conditional probability zero. Otherwise, if $u$ of its inputs are unassigned, its conditional bad-event probability is
--
--   $$q^{-bu}.$$
--
--   The score is the sum over the enumerated configurations. Process inputs in the specified lexicographic order, choosing a minimum-score output by deterministic strict improvements starting from zero. The resulting table defines the actual local function, with zero only as a total-function fallback outside the exhaustive table. Producing the whole table is charged in Theorem 9. Neither an evasive map nor a minimizing oracle is supplied as input. This semantic algorithm fixes the function that later register programs must realize.
-- source:
--   Brakensiek, Chen, Cheraghchi, Goyal, Guruswami, Putterman, Zhang, STOC 2027 submission #312 (October 2026), Theorem 9 proof, printed p. 8 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/312.pdf; PDF SHA256 a6946cb436bf453cfc53c1547fdd79e55134761b2192ee39f145dfc45490f6bc; continued printed p. 9 (PDF p. 10)

import Definitions.Def_SubspaceEvasion312_Explicit_effective

noncomputable section

namespace SubspaceEvasion312.Explicit
open scoped BigOperators

/-- Lexicographic enumeration from an explicit ordering of the finite field. -/
def allVectors {F : Type} (alphabet : List F) : (n : ℕ) → List (Vec F n)
  | 0 => [Fin.elim0]
  | n + 1 => alphabet.flatMap fun a => (allVectors alphabet n).map (Fin.cons a)

def allTuples {X : Type} (xs : List X) : (n : ℕ) → List (Fin n → X)
  | 0 => [Fin.elim0]
  | n + 1 => xs.flatMap fun a => (allTuples xs n).map (Fin.cons a)

/-- All r generating vectors and all ordered d-tuples of coefficient vectors.
Repeated tuples are harmless; repeated projected inputs have probability zero. -/
def eventPoints {F : Type} [Field F] {s b r d : ℕ}
    (basis : Fin r → Vec F s × Vec F b) (coeff : Fin d → Vec F r) :
    List (Vec F s × Vec F b) :=
  List.ofFn fun j => ∑ i : Fin r, coeff j i • basis i

/-- Conditional bad-event probability. All denominators are positive since q>=2.
An assigned pair that disagrees, or repeated input coordinates, makes it zero. -/
def eventProbability {F : Type} [Field F] [Fintype F] {s b : ℕ}
    (assigned points : List (Vec F s × Vec F b)) : ℚ := by
  classical
  exact if (points.map Prod.fst).Nodup ∧
      (∀ z ∈ points, ∀ w ∈ assigned, z.1 = w.1 → z.2 = w.2) then
    1 / (Fintype.card F : ℚ) ^ (b * (points.filter
      (fun z => !(assigned.any (fun w => decide (w.1 = z.1))))).length)
  else 0

def conditionalScore {F : Type} [Field F] [Fintype F] {s b : ℕ}
    (alphabet : List F) (r d : ℕ) (assigned : List (Vec F s × Vec F b)) : ℚ :=
  let bases := allTuples ((allVectors alphabet s).flatMap fun x =>
    (allVectors alphabet b).map fun y => (x,y)) r
  let coefficients := allTuples (allVectors alphabet r) d
  ((bases.map fun basis => (coefficients.map fun coeff =>
    eventProbability assigned (eventPoints basis coeff)).sum)).sum

/-- Deterministic strict improvements from zero select a conditional-expectation minimizer. -/
def chooseValue {F : Type} [Field F] [Fintype F] {s b : ℕ}
    (alphabet : List F) (r d : ℕ) (assigned : List (Vec F s × Vec F b))
    (x : Vec F s) : Vec F b :=
  (allVectors alphabet b).foldl (fun best w =>
    if conditionalScore alphabet r d (assigned ++ [(x,w)]) <
       conditionalScore alphabet r d (assigned ++ [(x,best)]) then w else best) 0

def localTable {F : Type} [Field F] [Fintype F] (alphabet : List F)
    (s b r d : ℕ) : List (Vec F s × Vec F b) :=
  (allVectors alphabet s).foldl (fun assigned x =>
    assigned ++ [(x, chooseValue alphabet r d assigned x)]) []

/-- The actual function returned by the conditional-expectation construction. -/
def localFunction {F : Type} [Field F] [Fintype F] (alphabet : List F)
    (s b r d : ℕ) (x : Vec F s) : Vec F b := by
  classical
  exact ((localTable alphabet s b r d).find? (fun z => decide (z.1 = x))).map Prod.snd |>.getD 0

/-- The table is an output format, not free advice: its whole production is charged. -/
def localTableData {F : Type} [Field F] [Fintype F] (alphabet : List F)
    (s b r d : ℕ) : List F :=
  ((allVectors alphabet s).map fun x => vectorData (localFunction alphabet s b r d x)).flatten

end SubspaceEvasion312.Explicit


