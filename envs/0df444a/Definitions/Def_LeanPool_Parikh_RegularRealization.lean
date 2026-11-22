-- Prove2me | Definitions.Def_LeanPool_Parikh_RegularRealization
-- name    : LeanPool_Parikh_RegularRealization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:50:30.593398+00:00
-- url     : https://prove2.me/theorems/e580efe0-3b5e-49dc-80aa-3ff868c90cf3
-- title:
--   Regular Realization
-- statement:
--   Definitions and structural lemmas for Regular Realization, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/RegularRealization.lean

module
public import Definitions.Def_LeanPool_Parikh_Counting
public import Mathlib.Computability.RegularExpressions
public import Mathlib.Computability.DFA
public import Definitions.Def_LeanPool_Parikh_DFAGrammar
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_WordBlockAutomata
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped Computability Pointwise
namespace Parikh
section
variable {T : Type*}
structure AlphabetOrder (T : Type*) where
  /-- Enumeration of the finite alphabet in the chosen order. -/
  letters : List T
  nodup : letters.Nodup
  complete : ∀ a : T, a ∈ letters
@[expose] def representative (alphabet : AlphabetOrder T) (v : Vector T) : List T :=
  (alphabet.letters.map fun a => List.replicate (v a) a).flatten
@[expose] def wordExpression (w : List T) : RegularExpression T :=
  w.foldr (fun a rest => .comp (.char a) rest) .epsilon
@[expose] def componentExpression (alphabet : AlphabetOrder T) (c : Component T) :
  RegularExpression T :=
  .comp (wordExpression (representative alphabet c.base))
    (c.periods.foldr (fun p rest =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon)
@[expose] def witnessExpression (alphabet : AlphabetOrder T) (W : Witness T) :
  RegularExpression T :=
  W.foldr (fun c rest => .plus (componentExpression alphabet c) rest) .zero
end
section
variable {T : Type*}
end
end Parikh


