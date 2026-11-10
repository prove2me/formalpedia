-- Prove2me | Definitions.Def_ArrighiStarFree_HalfLevel_Intersection
-- name    : ArrighiStarFree_HalfLevel_Intersection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:07:09.432193+00:00
-- url     : https://prove2.me/theorems/87fd1889-a905-4352-abe4-8fddc7688746
-- title:
--   Encoded promised half-level intersection nonemptiness
-- statement:
--   An instance consists of a nonempty finite list of finite NFAs sharing one finite alphabet. Alphabet size, list length and state counts are arbitrary input data. Its binary code gives the alphabet size and list length as zero-terminated unary fields, followed by the automaton records. Input length counts this entire code.
--
--   The semantic promise requires every accepted language to be a finite union of first-half-level monomials. Optional restrictions require each automaton to be a complete DFA, or the alphabet to have exactly one letter. Legal strings are exactly encodings satisfying the selected restrictions and the semantic promise. On these strings the answer is
--   $$\exists w\in\Sigma^*\quad\forall i<m,\quad w\in L(A_i).$$
--   The empty word is allowed. Strings outside the legal domain impose no correctness requirement on a decision machine. All tables may contain cycles and arbitrary nondeterministic branching.
--
--   The two Boolean parameters of intersectionProblem select DFA input and unary alphabets, respectively. Neither shortest words, reachability answers, shuffle generators nor certificates of complexity are included in the input.
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), §2–3, printed pp. 23:4–23:7, PDF pp. 4–7

import Definitions.Def_ArrighiStarFree_HalfLevel_Automata
import Definitions.Def_ArrighiStarFree_HalfLevel_Reductions

namespace ArrighiStarFree.HalfLevel

/-- Nonempty, unbounded list over one arbitrary finite alphabet. No semantic promise,
acyclicity, witness or resource certificate is stored in the input data. -/
structure IntersectionInput where
  alphabetSize : ℕ
  count : ℕ
  positive : 0 < count
  automata : Fin count → FiniteNFA alphabetSize

/-- Unary alphabet and list counts delimit the following dense automaton records.
There is no product automaton or extra padding in an input encoding. -/
def IntersectionInput.encode (I : IntersectionInput) : List Bool :=
  unaryCode I.alphabetSize ++ unaryCode I.count ++
    (List.finRange I.count).flatMap (fun i => (I.automata i).encode)

def IntersectionInput.Promised (I : IntersectionInput) : Prop :=
  ∀ i, FirstHalfLevel (I.automata i).language

def IntersectionInput.PositiveAnswer (I : IntersectionInput) : Prop :=
  ∃ w : List (Fin I.alphabetSize), ∀ i, w ∈ (I.automata i).language

def IntersectionInput.Legal (I : IntersectionInput) (dfa unary : Bool) : Prop :=
  I.Promised ∧ (dfa = true → ∀ i, (I.automata i).IsDFA) ∧
    (unary = true → I.alphabetSize = 1)

/-- Malformed and off-promise strings are outside the domain, not additional NO cases. -/
def intersectionProblem (dfa unary : Bool) : PromiseProblem where
  domain := {x | ∃ I : IntersectionInput, x = I.encode ∧ I.Legal dfa unary}
  answer := fun x => ∃ I : IntersectionInput, x = I.encode ∧ I.PositiveAnswer

end ArrighiStarFree.HalfLevel


