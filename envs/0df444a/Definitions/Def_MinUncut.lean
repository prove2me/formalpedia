-- Prove2me | Definitions.Def_MinUncut
-- name    : MinUncut
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.311878+00:00
-- url     : https://prove2.me/theorems/266d9361-309c-4919-960a-be2a8662202f
-- statement:
--   This block sets up a gap-style reduction from 3-CNF satisfiability to the minimum-uncut problem. A Literal is a natural-number variable name with a sign; it evaluates under an assignment Nat → Bool to the variable's value if positive and its negation otherwise. A Clause is a triple of literals evaluating to the disjunction of its three literals, a Formula is a finite list of clauses, and a formula is Satisfiable if some assignment makes every clause true. A prefix-style binary encoding is defined: a natural number's binary digits are framed by prefixing true before each bit and ending with false, a literal is encoded as its sign bit followed by its framed name, a clause as the concatenation of its three literals, and a formula as its clauses each preceded by true and terminated by false. A MinUncut Output is a simple undirected graph on n vertices, given by a symmetric, loopless Boolean adjacency matrix, together with a positive natural threshold. For a 2-coloring cut of the vertices, uncut counts the edges whose endpoints receive the same color, and opt is the minimum of this count over all colorings. The graph is serialized as the encoded vertex count, the full adjacency matrix row by row, and the encoded threshold, while an input pair (K, formula) is encoded as the encoded K followed by the encoded formula. A Reduction consists of a map sending K and a formula to such an output, computed by a Turing machine (TM2) with finite tape alphabets, running in time bounded by a polynomial in the encoded formula length (for each K) and producing output whose vertex count plus bit length is polynomially bounded in that length. Its correctness fields say that for every K ≥ 2, a satisfiable formula yields opt ≤ threshold, while an unsatisfiable formula yields K · threshold < opt, a gap of multiplicative factor K.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MinUncut.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MinUncut.lean; bytes 16..4709
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

   
                                                                         
                                                                

                                                                          
                                                                         
                                                                        
                                                                      
  
namespace MinUncutGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end MinUncutGames.BinaryFormula

namespace MinUncutGames.BinaryEncoding
open BinaryFormula

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def nameBits (name : Nat) : List Bool := frame name.bits

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

end MinUncutGames.BinaryEncoding

namespace MinUncut
open MinUncutGames.BinaryFormula MinUncutGames.BinaryEncoding

                                                                        
                                                                           
structure Output where
  vertices : ℕ
  adjacent : Fin vertices → Fin vertices → Bool
  symmetric : ∀ u v, adjacent u v = adjacent v u
  loopless : ∀ u, adjacent u u = false
  threshold : ℕ
  threshold_pos : 1 ≤ threshold

                                                                              
                                                           
def Output.uncut (G : Output) (cut : Fin G.vertices → Bool) : ℕ :=
  (Finset.univ.filter fun uv : Fin G.vertices × Fin G.vertices =>
    uv.1 < uv.2 ∧ G.adjacent uv.1 uv.2 = true ∧ cut uv.1 = cut uv.2).card

                                                                             
                                     
noncomputable def Output.opt (G : Output) : ℕ :=
  (Finset.univ.image G.uncut).min' (by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)

                                                                        
                                                                           
def Output.bits (G : Output) : List Bool :=
  nameBits G.vertices ++
    ((List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => G.adjacent u v) ++
    nameBits G.threshold

                                                                               
                                                             
def inputBits (input : ℕ × Formula) : List Bool :=
  nameBits input.1 ++ formulaBits input.2

                                                                            
                                                                         
                                                                       
                                                                 
structure Reduction where
  reduce : ℕ → Formula → Output
  machine : Turing.TM2Computable inputBits Output.bits (fun p => reduce p.1 p.2)
  finiteAlphabet : ∀ k : machine.tm.K, Finite (machine.tm.Γ k)
  time : ℕ → Polynomial ℕ
  runtime : ∀ K φ,
    Turing.TM2OutputsInTime machine.tm
      ((inputBits (K, φ)).map machine.inputAlphabet.symm)
      (some (((reduce K φ).bits).map machine.outputAlphabet.symm))
      ((time K).eval (formulaBits φ).length)
  size : ℕ → Polynomial ℕ
  output_size : ∀ K φ,
    (reduce K φ).vertices + (reduce K φ).bits.length ≤
      (size K).eval (formulaBits φ).length
  yes : ∀ K, 2 ≤ K → ∀ φ, φ.Satisfiable →
    (reduce K φ).opt ≤ (reduce K φ).threshold
  no : ∀ K, 2 ≤ K → ∀ φ, ¬ φ.Satisfiable →
    K * (reduce K φ).threshold < (reduce K φ).opt

end MinUncut

namespace MinUncut



end MinUncut
end OAI


