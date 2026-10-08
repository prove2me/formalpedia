-- Prove2me | Definitions.Def_GeneralizedStarHeight
-- name    : GeneralizedStarHeight
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.119542+00:00
-- url     : https://prove2.me/theorems/2f536955-b2c0-4667-acc4-c36b5c170b1c
-- statement:
--   Expression(Alphabet) is the type of generalized regular expressions over an alphabet, built from the constants zero and one, a single letter a, binary union, binary concatenation, complement, and Kleene star. Its language semantics assigns to each expression a formal language: zero gives the empty language, one gives the language containing only the empty word, a letter a gives the singleton {[a]}, union gives the sum (set union) of the two languages, concat gives their product (concatenation of languages), compl gives the complement of the language in the set of all words, and star gives the Kleene star of the language. The generalized star height of an expression is defined recursively: constants and letters have height 0, union and concatenation take the maximum of the heights of the two parts, complement leaves the height unchanged, and star adds 1 to the height of its argument. Complement is therefore free and does not count toward height. Finally, HasHeightAtMost(L,n) is the property that a language L is denoted by some expression P with language(P)=L and height(P)≤n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GeneralizedStarHeight.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GeneralizedStarHeight.lean; bytes 16..1198
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace GeneralizedStarHeight

universe u

inductive Expression (Alphabet : Type u) : Type u
  | zero : Expression Alphabet
  | one : Expression Alphabet
  | letter : Alphabet → Expression Alphabet
  | union : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | concat : Expression Alphabet → Expression Alphabet → Expression Alphabet
  | compl : Expression Alphabet → Expression Alphabet
  | star : Expression Alphabet → Expression Alphabet

namespace Expression

open scoped Computability

def language {Alphabet : Type u} : Expression Alphabet → Language Alphabet
  | .zero => 0
  | .one => 1
  | .letter a => {[a]}
  | .union P Q => P.language + Q.language
  | .concat P Q => P.language * Q.language
  | .compl P => P.languageᶜ
  | .star P => P.language∗

def height {Alphabet : Type u} : Expression Alphabet → ℕ
  | .zero | .one | .letter _ => 0
  | .union P Q | .concat P Q => max P.height Q.height
  | .compl P => P.height
  | .star P => 1 + P.height

end Expression

def HasHeightAtMost {Alphabet : Type u} (L : Language Alphabet) (n : ℕ) : Prop :=
  ∃ P : Expression Alphabet, P.language = L ∧ P.height ≤ n



end GeneralizedStarHeight
end OAI


