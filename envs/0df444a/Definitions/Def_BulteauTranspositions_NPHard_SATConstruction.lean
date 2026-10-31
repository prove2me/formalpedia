-- Prove2me | Definitions.Def_BulteauTranspositions_NPHard_SATConstruction
-- name    : BulteauTranspositions_NPHard_SATConstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:54:44.417586+00:00
-- url     : https://prove2.me/theorems/800e0b36-201c-44d0-83c4-2c38468347f4
-- title:
--   The concrete SAT-to-3DT construction and normalization
-- statement:
--   CNF formulas and satisfiability use the published CookPvsNP definitions. Normalized formulas have at least two clauses, at least two occurrences in every clause, and at least two occurrences of each polarity of each appearing Boolean variable. Literal repetitions are retained as distinct occurrence ports. The compact formula code records clause boundaries, literal signs, and renamed variable indices.
--
--   The construction creates one var gate per Boolean variable, copy chains for its positive and negative occurrence ports, left-associated or chains for clauses, a left-associated and chain for the formula, and a feedback copy chain. Blocks are concatenated in variable order (positive chain then negative chain), clause order, conjunction order, and feedback order. Every intermediate port is allocated a fresh number. Two-leaf chains are single gates. With one Boolean variable the feedback uses the formula wire directly and creates zero copy gates. The last conjunction input is Γγ, reading the obvious Γl typo as resolved on p.29 (insight I1).
--
--   Concrete preprocessing handles all CNF inputs: an empty clause produces a fixed unsatisfiable two-clause formula, sparse variables are compactly renamed, singleton literals are duplicated, and two copies of a tautological clause are added for each variable, including two fresh variables. The empty conjunction is preserved as satisfiable by this construction. A separate parser reads exactly the published unary-index SAT syntax, accepting the empty conjunction and rejecting bare index digits or unterminated clauses. No semantic correctness or running-time claim is a structure field.
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, definitions and constructions, printed/PDF pp. 26–27; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Encoding

namespace BulteauTranspositions.NPHard

def formulaVars (F : CookPvsNP.CNF) : List ℕ := (F.flatten.map Prod.snd).eraseDups

/-- A compact formula code: clause counts, clause lengths, and sign/index pairs.
Variable names are renamed in order of first appearance, preserving every occurrence. -/
def encodeFormula (F : CookPvsNP.CNF) : List Bool :=
  let vs := formulaVars F
  encodeNats (F.length :: F.flatMap fun C =>
    C.length :: C.flatMap (fun l => [l.1.toNat,vs.idxOf l.2]))

/-- The standing normalization assumptions of §3.3, with variables indexed from zero. -/
def Normalized (F : CookPvsNP.CNF) : Prop :=
  2 ≤ F.length ∧ (∀ C ∈ F, 2 ≤ C.length) ∧
  ∀ x ∈ formulaVars F, 2 ≤ F.flatten.count (true,x) ∧ 2 ≤ F.flatten.count (false,x)

def duplicateSingleton : List CookPvsNP.Literal → List CookPvsNP.Literal
  | [l] => [l,l]
  | ls => ls

/-- Concrete preprocessing for all CNF inputs, including empty clauses/conjunctions.
Two fresh variables ensure at least two var blocks; every polarity gains two occurrences. -/
def normalize (F : CookPvsNP.CNF) : CookPvsNP.CNF :=
  let raw := if [] ∈ F then [[(true,0),(true,0)],[(false,0),(false,0)]] else F
  let vs := formulaVars raw
  let compact := raw.map fun C => duplicateSingleton (C.map fun l => (l.1,vs.idxOf l.2))
  compact ++ (List.range (vs.length + 2)).flatMap
    (fun x => [[(true,x),(false,x)],[(true,x),(false,x)]])

/-- A chain with at least two leaves; the two-leaf case is exactly one copy gate. -/
def copyChain (root : ℕ) (leaves : List ℕ) (next : ℕ) : List Gate × ℕ :=
  match leaves with
  | [] | [_] => ([],next)
  | [a,b] => ([⟨.copy,root,a,b⟩],next)
  | a :: b :: c :: rest =>
      let tail := copyChain next (b :: c :: rest) (next+1)
      (⟨.copy,root,a,next⟩ :: tail.1,tail.2)

/-- Left-associated or/and chain, with the final gate writing the designated root. -/
def foldChain (kind : GateKind) (root : ℕ) (leaves : List ℕ) (next : ℕ) : List Gate × ℕ :=
  match leaves with
  | [] | [_] => ([],next)
  | [a,b] => ([⟨kind,root,a,b⟩],next)
  | a :: b :: c :: rest =>
      let tail := foldChain kind root (next :: c :: rest) (next+1)
      (⟨kind,next,a,b⟩ :: tail.1,tail.2)
termination_by leaves.length

/-- The first m wires are feedback ports, the next 2m are literal roots;
then come one port for each literal occurrence, clause roots, and the formula root. -/
def satGates (F : CookPvsNP.CNF) : List Gate := Id.run do
  let vs := formulaVars F
  let m := vs.length
  let occ := F.flatten
  let o := 3*m
  let cbase := o + occ.length
  let root := cbase + F.length
  let mut next := root + 1
  let mut gs : List Gate := []
  for i in List.range m do
    -- With one Boolean variable, the zero-gate feedback is a direct wire.
    let feedback := if m = 1 then root else i
    gs := gs ++ [⟨.var,feedback,m+2*i,m+2*i+1⟩]
    for sign in [true,false] do
      let r := m + 2*i + (if sign then 0 else 1)
      let leaves := (occ.zipIdx.filter fun li => li.1 == (sign,vs.getD i 0)).map
        (fun li => o + li.2)
      let chain := copyChain r leaves next
      gs := gs ++ chain.1
      next := chain.2
  let mut offset := 0
  for ci in F.zipIdx do
    let leaves := (List.range ci.1.length).map fun j => o + offset + j
    let chain := foldChain .or (cbase+ci.2) leaves next
    gs := gs ++ chain.1
    next := chain.2
    offset := offset + ci.1.length
  let conjunction := foldChain .and root ((List.range F.length).map (cbase+·)) next
  gs := gs ++ conjunction.1
  next := conjunction.2
  let feedback := copyChain root (List.range m) next
  return gs ++ feedback.1

def satInstance (F : CookPvsNP.CNF) : Instance := (assembly (satGates F)).inst

def normalizedSatInstance (F : CookPvsNP.CNF) : Instance := satInstance (normalize F)

/-- Parse the published CookPvsNP code, rejecting a bare unary digit or unterminated clause. -/
def parseCNFAux : List CookPvsNP.SatSym → Option CookPvsNP.Literal →
    List CookPvsNP.Literal → CookPvsNP.CNF → Option CookPvsNP.CNF
  | [], none, [], clauses => some clauses
  | [], _, _, _ => none
  | .one :: rest, some l, clause, clauses =>
      parseCNFAux rest (some (l.1,l.2+1)) clause clauses
  | .one :: _, none, _, _ => none
  | .pos :: rest, current, clause, clauses =>
      parseCNFAux rest (some (true,0)) (clause ++ current.toList) clauses
  | .neg :: rest, current, clause, clauses =>
      parseCNFAux rest (some (false,0)) (clause ++ current.toList) clauses
  | .endClause :: rest, current, clause, clauses =>
      parseCNFAux rest none [] (clauses ++ [clause ++ current.toList])

def parseCNF (s : List CookPvsNP.SatSym) : Option CookPvsNP.CNF :=
  parseCNFAux s none [] []

end BulteauTranspositions.NPHard


