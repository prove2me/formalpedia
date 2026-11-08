-- Prove2me | Definitions.Def_QuadraticRE_Desc
-- name    : QuadraticRE_Desc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:03:44.264969+00:00
-- url     : https://prove2.me/theorems/d0d51139-37d3-4d67-a6c6-8f6dba1b4c7b
-- title:
--   Explicit polynomial maps as lists of monomials
-- statement:
--   A **description** of a polynomial map $\mathbb F_2^N\times\mathbb F_2^\rho\to\mathbb F_2^\ell$ lists, for each of the $\ell$ output coordinates, a list of monomials, each monomial a list of variables among the $N$ input variables $x_i$ and the $\rho$ tape variables $r_i$. A coordinate evaluates to the sum over $\mathbb F_2$ of the products of its monomials. The description has **degree at most $d$** if every monomial has at most $d$ variables; this is degree jointly in the input and the tape bits (Definition 3.2). The **number of terms** $M$ of Lemma 4.11 counts the monomials, a coordinate with no monomials (a zero coordinate) counting as one zero term.
--
--   This is the "expanded polynomial description" whose size the main theorem bounds.
--
--   **Formalization Note** The empty monomial is $1$, the empty list is $0$, multiplicities are kept, and a variable may repeat inside a monomial (harmless over $\mathbb F_2$, where $x^2=x$).
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13; Definition 3.2, p.14; Lemma 4.11, p.29

import Mathlib
import Definitions.Def_QuadraticRE_SD

namespace QuadraticRE

/-- An explicit polynomial map `F₂^N × F₂^ρ → F₂^ℓ` given by lists of monomials
(Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13: "Polynomial maps may be specified … by lists of monomials"). A monomial
is a list of variables in `Fin N ⊕ Fin ρ`, input variables first by `Sum.inl`, tape variables by
`Sum.inr`.

**Formalization Note.** The empty monomial is `1`, the empty list of monomials is `0`, multiplicities
are kept, and a variable may repeat inside a monomial (harmless over `F₂`, where `x² = x`). -/
structure Desc (N ρ ℓ : ℕ) where
  coords : Fin ℓ → List (List (Fin N ⊕ Fin ρ))

/-- The value of a description: each coordinate is the sum in `F₂` of the products of its monomials. -/
def Desc.eval {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) (x : Fin N → F2) (r : Fin ρ → F2) (i : Fin ℓ) : F2 :=
  ((D.coords i).map (fun m => (m.map (Sum.elim x r)).prod)).sum

/-- Degree at most `d` jointly in the input and the tape variables (Definition 3.2, p.14): every
monomial has at most `d` variables. -/
def Desc.DegLE {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) (d : ℕ) : Prop :=
  ∀ i, ∀ m ∈ D.coords i, m.length ≤ d

/-- The total number of monomials of a description. -/
def Desc.numMonomials {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) : ℕ :=
  ∑ i, (D.coords i).length

/-- The number `M` of terms of Lemma 4.11, p.29, "where each zero coordinate is represented by one
zero term": a coordinate with an empty list counts once. -/
def Desc.numTerms {N ρ ℓ : ℕ} (D : Desc N ρ ℓ) : ℕ :=
  ∑ i, max 1 (D.coords i).length

end QuadraticRE


