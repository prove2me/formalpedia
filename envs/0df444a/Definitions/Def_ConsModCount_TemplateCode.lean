-- Prove2me | Definitions.Def_ConsModCount_TemplateCode
-- name    : ConsModCount_TemplateCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:24.451986+00:00
-- url     : https://prove2.me/theorems/22061ab8-c410-40da-88ea-99bb8b6b1562
-- title:
--   Finite codes of templates for the decision procedures
-- statement:
--   A **template code** is a pair $(n,L)$: a domain size $n$ and, for each relation, its arity together with the list of its tuples (lists of naturals). It is **valid** if $n\ge1$ and every listed tuple has the stated arity and entries below $n$. A valid code describes the template on $\{0,\dots,n-1\}$ whose $i$-th relation consists of the listed tuples.
--
--   Codes are the inputs of the finite tests of Section 13; every finite template is isomorphic to the template of a valid code.
--
--   **Formalization Note** Codes are `Primcodable`, so Mathlib's `ComputablePred` expresses decidability by an algorithm.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §13, pp.23–24 (PDF pp.24–25): finite decidability of the structural criteria

import Mathlib
import Definitions.Def_ConsModCount_Template

set_option autoImplicit false

namespace ConsModCount

/-- A finite description of a template on the domain `{0, …, n-1}`: the domain size `n` and, for
each relation, its arity together with the list of its tuples (each tuple a list of naturals). This
is the input of the finite tests of Xie, §13, pp.23–24 (PDF pp.24–25). It is `Primcodable`, so
Mathlib's `ComputablePred` applies to predicates on it. -/
abbrev TemplateCode : Type := ℕ × List (ℕ × List (List ℕ))

/-- A code is **valid** when the domain is nonempty and every listed tuple of a relation of arity
`a` has length `a` and entries below the domain size. -/
def TemplateCode.Valid (c : TemplateCode) : Prop :=
  1 ≤ c.1 ∧ ∀ r ∈ c.2, ∀ l ∈ r.2, l.length = r.1 ∧ ∀ e ∈ l, e < c.1

/-- The template on `Fin c.1` described by a code: the `i`-th relation has arity `(c.2.get i).1` and
consists of the tuples whose list of values occurs in `(c.2.get i).2`. -/
def TemplateCode.toTemplate (c : TemplateCode) : Template (Fin c.1) where
  s := c.2.length
  arity i := (c.2.get i).1
  rel i := {t | List.ofFn (fun j => (t j).val) ∈ (c.2.get i).2}

end ConsModCount


