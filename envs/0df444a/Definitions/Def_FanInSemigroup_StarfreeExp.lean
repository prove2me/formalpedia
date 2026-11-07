-- Prove2me | Definitions.Def_FanInSemigroup_StarfreeExp
-- name    : FanInSemigroup_StarfreeExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:09.962435+00:00
-- url     : https://prove2.me/theorems/0e5aabf4-59ae-44b1-a244-dad278517fe5
-- title:
--   Starfree regular expressions and starfree languages
-- statement:
--   A **starfree regular expression** over an alphabet is built from the symbol $\varphi$, denoting the empty set, the symbol $\lambda$, denoting the empty word, and the symbols of the alphabet, using set union, set intersection, set concatenation and set complement with respect to $\Sigma^*$. There is no Kleene star.
--
--   A language is **starfree** if some such expression denotes it. For example, $(\neg\varphi)0$ denotes the set of all words ending in $0$.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, p.55

import Mathlib

set_option autoImplicit false

namespace FanInSemigroup

/-- Starfree regular expressions. Chandra, Fortune, Lipton, STOC 1983, §2, p.55: "A regular
expression is starfree if it can be constructed from the symbol φ (denoting the empty set), the
symbol λ (denoting the empty word) and the symbols of the alphabet using the operations set union,
set intersection, set concatenation and set complement (with respect to Σ*)". -/
inductive StarfreeExp (α : Type*) where
  /-- The symbol `φ`. -/
  | empty : StarfreeExp α
  /-- The symbol `λ`. -/
  | eps : StarfreeExp α
  /-- A symbol of the alphabet. -/
  | sym : α → StarfreeExp α
  /-- Set union. -/
  | union : StarfreeExp α → StarfreeExp α → StarfreeExp α
  /-- Set intersection. -/
  | inter : StarfreeExp α → StarfreeExp α → StarfreeExp α
  /-- Set concatenation. -/
  | concat : StarfreeExp α → StarfreeExp α → StarfreeExp α
  /-- Set complement with respect to `Σ*`. -/
  | compl : StarfreeExp α → StarfreeExp α

/-- The language denoted by a starfree expression. -/
def StarfreeExp.denote {α : Type*} : StarfreeExp α → Language α
  | .empty => 0
  | .eps => 1
  | .sym a => {[a]}
  | .union p q => p.denote + q.denote
  | .inter p q => p.denote ⊓ q.denote
  | .concat p q => p.denote * q.denote
  | .compl p => p.denoteᶜ

/-- A language is starfree if some starfree expression denotes it. -/
def IsStarfree {α : Type*} (L : Language α) : Prop :=
  ∃ p : StarfreeExp α, p.denote = L

end FanInSemigroup


