-- Prove2me | Definitions.Def_ResourceScheduling_Graph_Complexity
-- name    : ResourceScheduling_Graph_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:21:08.72458+00:00
-- url     : https://prove2.me/theorems/9bdfe37d-595a-49de-b8ad-2b5f83af2fdc
-- title:
--   NP-hardness and NP-hardness in the strong sense (unary encodings)
-- statement:
--   This module adds NP-hardness on top of Cook's definitions of $\mathrm{P}$, $\mathrm{NP}$ and polynomial-time many-one reducibility $\le_p$ (the published module `CookPvsNP_defs`).
--
--   A language $L$ is *NP-hard* when every language $L'$ in $\mathrm{NP}$, over any finite nonempty alphabet, satisfies $L'\le_p L$; this is the second half of Cook's definition of NP-completeness.
--
--   Decision problems are presented by a predicate $\mathrm{Yes}$ on their instances and an encoding $\mathrm{enc}$ of instances as strings over the two-letter alphabet $\{\mathtt{1},\mathtt{\#}\}$; a natural number $k$ is written in unary as $\mathtt{1}^k\mathtt{\#}$. The language of the problem is the set of codes of its yes-instances,
--   $$L(\mathrm{Yes},\mathrm{enc})=\{\,\mathrm{enc}(x) : \mathrm{Yes}(x)\,\},$$
--   which contains only well-formed codes. The problem is *NP-hard in the strong sense* when this language is NP-hard for a unary encoding $\mathrm{enc}$.
--
--   In Garey and Johnson's definition (*Computers and Intractability*, 1979, §4.2) a problem is NP-hard in the strong sense when it remains NP-hard when restricted to instances whose largest number $\mathrm{Max}(I)$ is bounded by a polynomial in the instance length. When every number is written in unary, $\mathrm{Max}(I)\le\mathrm{Length}(I)$, so the restriction is the whole problem and the two notions coincide; this is the reading used throughout the mission.
--
--   **Formalization Note.** `StronglyNPHard Yes enc` is `NPHard` of the code language; it has the meaning above only for unary encodings, and every encoding this mission applies it to writes each number in unary.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, Theorems 2–3 ("NP-hard in the strong sense", after Garey & Johnson [5], Computers and Intractability, 1979, §4.2)

import Mathlib
import Definitions.Def_CookPvsNP_defs

/-!
# NP-hardness and NP-hardness in the strong sense

On top of Cook's P/NP layer (`CookPvsNP`). A language is NP-hard when every NP language over a
finite nonempty alphabet reduces to it in polynomial time (the second conjunct of
`CookPvsNP.NPComplete`). A decision problem, given by a predicate `Yes` on its instances and a
**unary** encoding `enc` over the two-letter alphabet `Letter`, is NP-hard in the strong sense
(Garey & Johnson, *Computers and Intractability*, 1979, §4.2) when the language of codes of its
yes-instances is NP-hard: with every number written in unary, `Max(I) ≤ Length(I)`, so the
restriction to instances whose numbers are polynomially bounded in the instance length is the
whole problem.
-/

namespace ResourceScheduling.Graph

open CookPvsNP

/-- NP-hardness: every language in `NP`, over any finite nonempty alphabet, is polynomial-time
many-one reducible to `L`. -/
def NPHard {S : Type} (L : Lang S) : Prop :=
  ∀ (S' : Type) [Fintype S'] [Nonempty S'] (L' : Lang S'), L' ∈ NP S' → PolyReducible L' L

/-- The two-letter alphabet of the unary encodings: `one` is a unary digit (or a 1-bit),
`sep` closes a number (or is a 0-bit). -/
inductive Letter where
  | one
  | sep
  deriving DecidableEq

instance : Fintype Letter where
  elems := {Letter.one, Letter.sep}
  complete := by intro x; cases x <;> simp

instance : Nonempty Letter := ⟨Letter.one⟩

/-- The unary code of a natural number `k`: `k` copies of `one` followed by `sep`. -/
def unary (k : ℕ) : List Letter :=
  List.replicate k Letter.one ++ [Letter.sep]

/-- The language of codes of the yes-instances of a decision problem. It contains only
well-formed codes. -/
def codeLang {α : Type} (Yes : α → Prop) (enc : α → List Letter) : Lang Letter :=
  { w | ∃ x, Yes x ∧ w = enc x }

/-- NP-hardness in the strong sense of the decision problem `Yes`, encoded by the unary
encoding `enc`: the language of codes of yes-instances is NP-hard. It is Garey–Johnson's strong
NP-hardness only when `enc` writes every number in unary, which is the case for every encoding
this development applies it to. -/
def StronglyNPHard {α : Type} (Yes : α → Prop) (enc : α → List Letter) : Prop :=
  NPHard (codeLang Yes enc)

end ResourceScheduling.Graph


