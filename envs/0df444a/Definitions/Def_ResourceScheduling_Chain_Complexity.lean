-- Prove2me | Definitions.Def_ResourceScheduling_Chain_Complexity
-- name    : ResourceScheduling_Chain_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:23:25.482667+00:00
-- url     : https://prove2.me/theorems/df10dd8a-e843-4881-8c94-b32ecda93a96
-- title:
--   NP-hardness and NP-hardness in the strong sense (unary encoding)
-- statement:
--   This file defines NP-hardness and NP-hardness in the strong sense on top of Cook's Turing-machine formalization of $\mathrm{P}$, $\mathrm{NP}$ and polynomial-time many-one reducibility $\le_p$ (the platform definition `CookPvsNP_defs`).
--
--   1. A language $L$ is **NP-hard** if every language $L'$ in $\mathrm{NP}$, over any finite nonempty alphabet, satisfies $L' \le_p L$. This is the second half of Cook's definition of NP-completeness.
--   2. A natural number $k$ is written in **unary** as $k$ strokes followed by a separator, over the two-letter alphabet $\{1, \#\}$; a finite list of natural numbers is written as the concatenation of the unary codes of its entries. This code is unambiguous.
--   3. A decision problem whose instances $x$ are described by a list of natural numbers $\mathrm{code}(x)$, with yes-instances $\mathrm{Yes}$, has the **unary language**
--   $$L_{\mathrm{unary}} = \{\, \mathrm{unary}(\mathrm{code}(x)) : \mathrm{Yes}(x) \,\}.$$
--   4. The problem is **NP-hard in the strong sense** if its unary language is NP-hard.
--
--   Garey and Johnson (*Computers and Intractability*, 1979, §4.2) call a problem NP-hard in the strong sense when it remains NP-hard restricted to instances whose largest number is bounded by a polynomial in the instance length. With every number written in unary the largest number is at most the length of the code, and the two notions coincide; the unary formulation is the one used here.
--
--   **Formalization Note.** The code of a problem must list every number of the instance and determine the instance; each problem of this mission supplies such a code. No pairing function (`Encodable`, `Nat.pair`) is used, so code lengths are the unary lengths of the numbers.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, Theorem 4 and p. 18, Theorem 7 ('NP-hard in the strong sense'), with reference [5] (Garey & Johnson 1979, §4.2)

import Mathlib
import Definitions.Def_CookPvsNP_defs

/-!
# NP-hardness and NP-hardness in the strong sense

NP-hardness is the second conjunct of `CookPvsNP.NPComplete`. A decision problem whose instances
are described by a finite list of natural numbers is NP-hard in the strong sense (Garey & Johnson,
*Computers and Intractability*, 1979, §4.2) iff its language with every number written in unary is
NP-hard: in unary, the largest number of an instance is at most the length of its code.
-/

namespace ResourceScheduling.Chain

open CookPvsNP

/-- The two-letter alphabet of unary codes: a stroke and a separator. -/
inductive USym where
  | one
  | sep
  deriving DecidableEq

instance : Fintype USym where
  elems := {USym.one, USym.sep}
  complete := by intro x; cases x <;> simp

instance : Nonempty USym := ⟨USym.one⟩

/-- A natural number `k` in unary: `k` strokes followed by a separator. -/
def encNat (k : ℕ) : List USym := List.replicate k USym.one ++ [USym.sep]

/-- A list of natural numbers in unary, one after the other. -/
def encNats (xs : List ℕ) : List USym := xs.flatMap encNat

/-- The unary language of a decision problem with instances `α`, numeric description `code` and
yes-instances `Yes`: the unary codes of its yes-instances. -/
def unaryLang {α : Type} (code : α → List ℕ) (Yes : α → Prop) : Lang USym :=
  { w | ∃ x, Yes x ∧ w = encNats (code x) }

/-- `L` is NP-hard: every NP language over a finite nonempty alphabet reduces to `L` in polynomial
time. -/
def NPHard {Sym : Type} (L : Lang Sym) : Prop :=
  ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : Lang Sym'),
    L' ∈ NP Sym' → PolyReducible L' L

/-- The decision problem `(code, Yes)` is NP-hard in the strong sense: its unary language is
NP-hard. -/
def StronglyNPHard {α : Type} (code : α → List ℕ) (Yes : α → Prop) : Prop :=
  NPHard (unaryLang code Yes)

end ResourceScheduling.Chain


