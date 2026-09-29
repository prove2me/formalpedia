-- Prove2me | Definitions.Def_MTT_HeckeEquivalence
-- name    : MTT_HeckeEquivalence
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-26T19:41:45.926625+00:00
-- url     : https://prove2.me/theorems/ac3a0824-b066-4941-ab63-d0bc1cf9a256
-- title:
--   Equality of almost all Hecke Euler factors and minimal eigenform level
-- statement:
--   Fix a weight and a complex embedding of the algebraic coefficients. Two normalized cuspidal eigenforms have the same Hecke system if there is a positive integer $B$ such that, for every prime $p$ not dividing $B$,
--
--   $$a_p(f)=a_p(g),\qquad \varepsilon_f(p)=\varepsilon_g(p).$$
--
--   Thus their unramified Euler polynomials agree outside a finite set. An eigenform of positive level $N$ has minimal level in its Hecke system if every equivalent eigenform at a positive level $M$ satisfies $N\le M$. These predicates express the minimal-level interface used in newform theory, at the actual weight of the forms and with arbitrary nebentype.
--
--   **Formalization Note.** Positivity of the form's own level is supplied by the theorems that use these predicates. This file defines the predicates only; it does not assume nonvanishing or newform-existence results.
-- source:
--   Atkin--Lehner--Li newform theory: William Stein, Modular Forms: A Computational Approach, Chapter 9, Theorem 9.4, https://wstein.org/books/modform/modform/newforms.html; Ribet--Stein, Lectures on Modular Forms and Hecke Operators, Section 9.1, printed p.74, multiplicity-one discussion following Theorem 9.1.9, https://wstein.org/books/ribet-stein/main.pdf. The minimal-level predicate is the least-positive-level formulation of that Hecke-system interface.

import Definitions.Def_MTT_Arithmetic

set_option autoImplicit false

namespace MTT.Eigenform

/-- Two eigenforms have the same prime Hecke eigenvalues and nebentypus values outside a
finite set of primes. -/
def SameHeckeSystem {N M k : ℕ} {ι : Qbar →+* ℂ}
    (f : Eigenform N k ι) (g : Eigenform M k ι) : Prop :=
  ∃ B : ℕ, 0 < B ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ B →
    f.coeff p = g.coeff p ∧ f.epsilon p = g.epsilon p

/-- An eigenform has least positive level among forms with the same Hecke system. -/
def HasMinimalLevel {N k : ℕ} {ι : Qbar →+* ℂ} (f : Eigenform N k ι) : Prop :=
  ∀ M : ℕ, 0 < M → ∀ g : Eigenform M k ι, SameHeckeSystem f g → N ≤ M

end MTT.Eigenform


