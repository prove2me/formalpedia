-- Prove2me | Definitions.Def_BulteauTranspositions_NPHard_PermutationConstruction
-- name    : BulteauTranspositions_NPHard_PermutationConstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:55:50.683985+00:00
-- url     : https://prove2.me/theorems/a10ed949-2238-4112-b2cc-c8bca43a10fc
-- title:
--   Table 1 permutation and the total SAT sorting map
-- statement:
--   The value interval widths are 9,15,18,15 for copy,and,or,var, respectively, exactly t_h−s_h+3(n_i−n_o). Prefix sums give p_h and q_h. Each target gate supplies its input ports’ α and β offsets from p. Table 1 then gives the entire output list for each block; prefixing zero gives π_I. Bijection, endpoint fixation, equivalence and polynomial running time are obligations, not assumptions of the construction.
--
--   The total SAT sorting map parses a source word, normalizes its formula, builds these gates and this permutation, and sets the budget to the actual number of triples. A malformed SAT word maps to the fixed no-instance (0,2,1,3) with budget zero. Neither a satisfiability oracle nor a choice of a permutation satisfying equivalence is used. The proof’s misnumbered R/P justifications (insight I2) do not alter any table entry.
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, definitions and constructions, printed/PDF pp. 31–34; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_SATConstruction

namespace BulteauTranspositions.NPHard

/-- The nonnegative increments t_h-s_h+3(n_i-n_o), evaluated for the four block types. -/
def Gate.valueWidth (g : Gate) : ℕ :=
  match g.kind with
  | .copy => 9 | .and => 15 | .or => 18 | .var => 15

def valueOffset (gs : List Gate) (h : ℕ) : ℕ := ((gs.take h).map Gate.valueWidth).sum

/-- The target block assigns alpha and beta. The option rejects a wire not an input. -/
def Gate.inputOffsets (g : Gate) (p w : ℕ) : Option (ℕ × ℕ) :=
  match g.kind with
  | .copy => if w = g.w0 then some (p,p+4) else none
  | .var => if w = g.w0 then some (p+5,p+9) else none
  | .and => if w = g.w1 then some (p,p+7) else
      if w = g.w2 then some (p+3,p+9) else none
  | .or => if w = g.w1 then some (p,p+13) else
      if w = g.w2 then some (p+3,p+16) else none

def wireOffsets (gs : List Gate) (w : ℕ) : ℕ × ℕ :=
  ((gs.zipIdx).findSome? fun gh => gh.1.inputOffsets (valueOffset gs gh.2) w).getD (0,0)

/-- Exactly the four rows of Table 1 (p.33), omitting its repeated left boundary column. -/
def tableRow (gs : List Gate) (h : ℕ) (g : Gate) : List ℕ :=
  let p := valueOffset gs h
  let ab := wireOffsets gs g.w0
  let ab1 := wireOffsets gs g.w1
  let ab2 := wireOffsets gs g.w2
  match g.kind with
  | .copy => [ab1.1+2,p+8,p+4,p+3,ab2.1+2,p+7,ab1.2+1,ab1.1+1,p+6,
      ab2.2+1,ab2.1+1,p+9]
  | .and => [p+14,p+7,p+3,p+13,p+9,p+6,ab.1+2,p+12,p+11,ab.2+1,ab.1+1,p+15]
  | .or => [p+7,p+13,p+3,p+9,ab.1+2,p+12,p+11,ab.2+1,ab.1+1,p+16,p+6,
      p+15,p+10,p+8,p+18]
  | .var => [ab1.1+2,p+5,p+3,ab2.1+2,p+12,p+1,p+14,p+4,ab1.2+1,ab1.1+1,
      p+13,p+9,p+8,p+2,p+11,ab2.2+1,ab2.1+1,p+15]

def permutationValues (gs : List Gate) : List ℕ :=
  0 :: gs.zipIdx.flatMap (fun gh => tableRow gs gh.2 gh.1)

def constructedPermutation (gs : List Gate) (x : ℕ) : ℕ := (permutationValues gs).getD x 0

/-- Malformed SAT words go to the fixed no-instance (0,2,1,3) with budget zero. -/
def sortingReduction (s : List CookPvsNP.SatSym) : List Bool :=
  match parseCNF s with
  | none => encodeSorting 3 (fun x => [0,2,1,3].getD x 0) 0
  | some F =>
      let gs := satGates (normalize F)
      encodeSorting (assemblyWord gs).length (constructedPermutation gs)
        ((assemblyTriples gs).length : ℤ)

end BulteauTranspositions.NPHard


