-- Prove2me | Definitions.Def_BQC_alg
-- name    : BQC_alg
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T23:11:17.422055+00:00
-- url     : https://prove2.me/theorems/f01a2adf-ad6b-4cdf-93a5-c7cd320e3ae2
-- title:
--   The algebraic layer: crystallographic groups and finite-order elements
-- statement:
--   The algebraic interface of the braid quotient problem. The definition carries: the crystallographic group in the sense of the characterization of Lemma 8 of the source paper - a group with a short exact sequence from the standard integer lattice of rank d onto a finite group, with the covering injection, the projection, the exactness (the kernel of the projection is the image of the lattice), and the faithful holonomy representation recording the conjugation action on the lattice; the finite-order predicate - some positive power of an element is the identity; the no-even-torsion predicate - every element of finite order has some odd positive power equal to the identity; and the exact-order predicate - the r-th power of an element is the identity and no smaller positive power is - through which the torsion analysis of Theorem 2 and the realization results of Corollary 4, Theorem 3, and Theorem 6 are expressed.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Section 2 (the characterization of crystallographic groups, Lemma 8).

import Mathlib

/-!
# The algebraic layer: crystallographic groups and finite-order elements

The algebraic layer of the BQC mission, carrying the interface of Daciberg
Lima Goncalves, John Guaschi, and Oscar Ocampo, "A quotient of the Artin braid
groups related to crystallographic groups" (Journal of Algebra 474 (2017),
393-423): a crystallographic group in the sense of the characterization of
Lemma 8 - a group with a short exact sequence from the standard integer
lattice onto a finite quotient group whose holonomy representation, the
conjugation action on the lattice, is faithful - together with the
finite-order, exact-order, and no-even-torsion predicates for the torsion
analysis of Theorem 2 and the realization results.
-/

namespace BQC

/-- A crystallographic group in the sense of Lemma 8: a group Cry with a short
exact sequence from the standard integer lattice of rank d onto the finite
group Ph, with the covering injection and the projection, and the faithful
holonomy representation hol of Ph into the automorphisms of the lattice, which
records the conjugation action of the elements of Cry on the lattice. -/
structure CryWorld (d : Nat) (Cry Ph : Type*) [Group Cry] [Group Ph] [Fintype Ph] where
  inj : Multiplicative (Fin d → Int) →* Cry
  proj : Cry →* Ph
  inj_inj : ∀ x y : Multiplicative (Fin d → Int), inj x = inj y → x = y
  proj_surj : ∀ f : Ph, ∃ p : Cry, proj p = f
  ex : ∀ p : Cry, proj p = 1 ↔ ∃ z : Fin d → Int, inj (Multiplicative.ofAdd z) = p
  hol : Ph →* MulAut (Multiplicative (Fin d → Int))
  hol_conj : ∀ (p : Cry) (z : Fin d → Int), ∃ w : Fin d → Int,
    inj (Multiplicative.ofAdd w) = p * inj (Multiplicative.ofAdd z) * p⁻¹ ∧
      (hol (proj p)) (Multiplicative.ofAdd z) = Multiplicative.ofAdd w
  hol_inj : ∀ f1 f2 : Ph, hol f1 = hol f2 → f1 = f2

/-- The element g has finite order: some positive power of g is the identity. -/
def HasFinOrder {G : Type*} [Group G] (g : G) : Prop :=
  ∃ k : Nat, 0 < k ∧ g ^ k = 1

/-- The group has no elements of even order: every element of finite order
has some odd positive power equal to the identity. -/
def NoEvenTorsion (G : Type*) [Group G] : Prop :=
  ∀ g : G, HasFinOrder g → ∃ k : Nat, 0 < k ∧ Odd k ∧ g ^ k = 1

/-- The element g has exact order r: the r-th power of g is the identity, and
no smaller positive power is. -/
def ExactOrder {G : Type*} [Group G] (r : Nat) (g : G) : Prop :=
  g ^ r = 1 ∧ ∀ k : Nat, 0 < k → k < r → g ^ k ≠ 1

end BQC


