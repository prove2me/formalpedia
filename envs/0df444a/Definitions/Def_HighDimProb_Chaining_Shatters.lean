-- Prove2me | Definitions.Def_HighDimProb_Chaining_Shatters
-- name    : HighDimProb_Chaining_Shatters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:00.994924+00:00
-- url     : https://prove2.me/theorems/5b5def07-e1a2-407b-b1cd-a6243a060edd
-- title:
--   A class of Boolean functions shattering a subset
-- statement:
--   A class $F$ of Boolean functions $f : \Omega \to \{0,1\}$ on a common domain $\Omega$
--   **shatters** a subset $\Lambda \subseteq \Omega$ if every possible function $g : \Lambda \to
--   \{0,1\}$ arises as the restriction to $\Lambda$ of some $f \in F$. This is the combinatorial
--   notion the VC dimension (`VcDim`) is built from.
--
--   **Formalization Note** `Bool` stands for the book's $\{0,1\}$; a function $\Lambda \to
--   \text{Bool}$, for $\Lambda$ a `Set Ω` coerced to a subtype, is exactly a function $g : \Lambda
--   \to \{0,1\}$ on the subset.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 200, Definition 8.3.1 (part 1)

import Mathlib

namespace HighDimProb.Chaining

/-- **`Shatters F Λ`**: the class `F` of Boolean functions on `Ω` shatters the subset `Λ ⊆ Ω` if
every function `g : Λ → Bool` arises as the restriction to `Λ` of some `f ∈ F`. Vershynin,
*High-Dimensional Probability* (2018), Definition 8.3.1, p. 200 (PDF p. 208): "We say that a
subset `Λ ⊆ Ω` is shattered by `F` if any function `g : Λ → {0, 1}` can be obtained by
restricting some function `f ∈ F` onto `Λ`." `Bool` stands for the book's `{0, 1}`. -/
def Shatters {Ω : Type} (F : Set (Ω → Bool)) (Λ : Set Ω) : Prop :=
  ∀ g : Λ → Bool, ∃ f ∈ F, ∀ x : Λ, f x.1 = g x

end HighDimProb.Chaining


