-- Prove2me | Definitions.Def_set_formula
-- name    : set_formula
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T22:32:39.817949+00:00
-- url     : https://prove2.me/theorems/d78138a6-8660-460f-bed3-20a86a1fdea6
-- title:
--   De Bruijn set-theory formula syntax
-- statement:
--   Eight-constructor de Bruijn syntax for the language of set theory, with shift, substitution, renaming and free-index bound operations. Transcribed from `pa-mm0/source_constructors.mm0`, `source_syntax.mm0`, `source_shift.mm0`, `source_substitution.mm0`, `source_renaming.mm0`, `source_bounds.mm0`.
-- source:
--   https://github.com/elliotglazer/k215-pa (pa-mm0/source_syntax.mm0)

namespace K215

inductive SFormula where
  | bot : SFormula
  | mem : Nat → Nat → SFormula
  | eq : Nat → Nat → SFormula
  | and : SFormula → SFormula → SFormula
  | or : SFormula → SFormula → SFormula
  | imp : SFormula → SFormula → SFormula
  | all : SFormula → SFormula
  | ex : SFormula → SFormula
  deriving DecidableEq

def shiftIndex (d i : Nat) : Nat := if i < d then i else i + 1

def shift : Nat → SFormula → SFormula
  | _, .bot => .bot
  | d, .mem a b => .mem (shiftIndex d a) (shiftIndex d b)
  | d, .eq a b => .eq (shiftIndex d a) (shiftIndex d b)
  | d, .and a b => .and (shift d a) (shift d b)
  | d, .or a b => .or (shift d a) (shift d b)
  | d, .imp a b => .imp (shift d a) (shift d b)
  | d, .all a => .all (shift (d + 1) a)
  | d, .ex a => .ex (shift (d + 1) a)

def substIndex (d t i : Nat) : Nat := if i < d then i else if i = d then t + d else i - 1

def subst : Nat → Nat → SFormula → SFormula
  | _, _, .bot => .bot
  | d, t, .mem a b => .mem (substIndex d t a) (substIndex d t b)
  | d, t, .eq a b => .eq (substIndex d t a) (substIndex d t b)
  | d, t, .and a b => .and (subst d t a) (subst d t b)
  | d, t, .or a b => .or (subst d t a) (subst d t b)
  | d, t, .imp a b => .imp (subst d t a) (subst d t b)
  | d, t, .all a => .all (subst (d + 1) t a)
  | d, t, .ex a => .ex (subst (d + 1) t a)

def renameIndex (R : Nat → Nat) (d i : Nat) : Nat := if i < d then i else d + R (i - d)

def rename (R : Nat → Nat) : Nat → SFormula → SFormula
  | _, .bot => .bot
  | d, .mem a b => .mem (renameIndex R d a) (renameIndex R d b)
  | d, .eq a b => .eq (renameIndex R d a) (renameIndex R d b)
  | d, .and a b => .and (rename R d a) (rename R d b)
  | d, .or a b => .or (rename R d a) (rename R d b)
  | d, .imp a b => .imp (rename R d a) (rename R d b)
  | d, .all a => .all (rename R (d + 1) a)
  | d, .ex a => .ex (rename R (d + 1) a)

def bound : Nat → SFormula → Prop
  | _, .bot => True
  | n, .mem a b => a < n ∧ b < n
  | n, .eq a b => a < n ∧ b < n
  | n, .and a b => bound n a ∧ bound n b
  | n, .or a b => bound n a ∧ bound n b
  | n, .imp a b => bound n a ∧ bound n b
  | n, .all a => bound (n + 1) a
  | n, .ex a => bound (n + 1) a

def contextShift (G : List SFormula) : List SFormula := G.map (shift 0)

end K215


