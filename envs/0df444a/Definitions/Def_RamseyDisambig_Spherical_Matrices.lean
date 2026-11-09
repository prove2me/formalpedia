-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Matrices
-- name    : RamseyDisambig_Spherical_Matrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:21:45.569357+00:00
-- url     : https://prove2.me/theorems/aad992eb-5a0c-427c-a2f6-5cb0b9c78f4b
-- title:
--   Partial matrices, disambiguation, containment and universality
-- statement:
--   Let $A$ and $B$ be row and column sets. A partial binary matrix is a function $M:A\times B\to\{0,1,\star\}$. A disambiguation is a binary matrix $c$ preserving each specified entry of $M$.
--
--   For $F:\{0,\ldots,a-1\}\times\{0,\ldots,b-1\}\to\{0,1\}$, containment means
--   $$\exists\rho,\kappa\text{ injective},\quad c(\rho(i),\kappa(j))=F(i,j)\quad\text{for all }i,j.$$
--   The row and column maps are independent. No disjointness between their images is required, even when the ambient carriers agree.
--
--   For a family $(M_t)_{t\in I}$ with possibly varying row and column sets, disambiguation-universality means
--   $$\forall a,b,F,\ \exists t\in I,\ \forall c\text{ disambiguating }M_t,\quad c\text{ contains }F.$$
--   This interface separates ordinary binary containment from the constraints on partial entries. It permits repeated rows in $F$ and empty finite row or column sets.
--
--   **Formalization Note** Binary labels are `Bool`, unspecified entries are `none`, and specified entries are `some false` or `some true`. Finite index sets use `Fin`.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §1, pp. 1 and 3 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Mathlib

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- A binary partial matrix; `none` is the unspecified entry. Source pp. 1, 3. -/
abbrev PartialMatrix (Row Col : Type*) := Row → Col → Option Bool

/-- Entries already specified must be preserved, independently at every position. -/
def IsDisambiguation {Row Col : Type*} (M : PartialMatrix Row Col)
    (c : Row → Col → Bool) : Prop :=
  ∀ x y b, M x y = some b → c x y = b

/-- Containment permits independent injective choices of rows and columns (p. 3). -/
def Contains {Row Col : Type*} (c : Row → Col → Bool)
    {a b : ℕ} (F : Fin a → Fin b → Bool) : Prop :=
  ∃ (ρ : Fin a → Row) (κ : Fin b → Col),
    Function.Injective ρ ∧ Function.Injective κ ∧ ∀ i j, c (ρ i) (κ j) = F i j

/-- A family forces every finite binary matrix in every completion of some member. -/
def DisambiguationUniversal {ι : Type*} (Row Col : ι → Type*)
    (M : ∀ i, PartialMatrix (Row i) (Col i)) : Prop :=
  ∀ (a b : ℕ) (F : Fin a → Fin b → Bool),
    ∃ i, ∀ c : Row i → Col i → Bool, IsDisambiguation (M i) c → Contains c F

end RamseyDisambig.Spherical


