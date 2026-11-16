-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Encoding
-- name    : HypercliqueCircuits_Circuits_Supplement_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:09:14.182289+00:00
-- url     : https://prove2.me/theorems/1f03aed8-c9b9-47b2-ac37-aaaaec91fcf7
-- title:
--   Natural-word encodings and ordered finite tuples
-- statement:
--   Inputs and outputs are lists of natural-number words on the published oracle-free machine. Boolean false and true are encoded by 0 and 1. A tuple in $[n]^r$ is ordered by its mixed-radix index
--
--   $$\operatorname{index}(i)=\sum_{j=0}^{r-1} i_j n^j.$$
--
--   An assignment is a list of its $n$ Boolean words in variable order. The empty tuple is present once when $r=0$, including $n=0$. These encodings supply finite data to actual programs; they supply no algorithm, answer, time bound, or circuit. Every emitted word is charged by the published execution cost.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, pp.2,24–26, Theorems 2–5 and §4 (PDF 3,25–27); encoding convention using the published Machine definition

import Definitions.Def_HypercliqueCircuits_Circuits_Machine

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- Natural words on the published oracle-free machine; no opaque atoms. -/
def words (xs : List ℕ) : List (Cell Empty) := xs.map Sum.inl

def bit (b : Bool) : ℕ := if b then 1 else 0

/-- Mixed-radix order: coordinate zero is least significant. Includes the
unique empty tuple when r = 0, even for n = 0. -/
def tuples (r n : ℕ) : List (Fin r → Fin n) :=
  (List.finRange (n ^ r)).map (finFunctionFinEquiv.symm)

/-- An assignment is emitted as n Boolean natural words, in variable order. -/
def assignmentWords {n : ℕ} (x : Fin n → Bool) : List (Cell Empty) :=
  words ((List.finRange n).map (fun i => bit (x i)))

end HypercliqueCircuits.Circuits.Supplement


