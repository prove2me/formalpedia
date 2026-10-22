-- Prove2me | Definitions.Def_BUP_alg
-- name    : BUP_alg
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T23:08:59.434421+00:00
-- url     : https://prove2.me/theorems/8b43a268-5105-463b-a1fe-0c50f46e0380
-- title:
--   The algebraic layer: involution extensions, braid data, and the Borsuk-Ulam diagram condition
-- statement:
--   The algebraic interface of the Borsuk-Ulam problem for homotopy classes of selfmaps. The definition carries: the two-element deck group of a double covering, in multiplicative form; the short exact sequence induced by a free involution of a surface - the covering injection of the fundamental group into the fundamental group of the orbit space, and the projection onto the deck group, with the exactness properties of the sequence (5) of the paper; the braid data of a surface - the pure and full two-string braid groups with the inclusion and the projection of the sequence (8), the Fadell-Neuwirth projection of the pure braid group onto the fundamental group, and the designated half-twist with its conjugation action on the pure braid group and its full-twist square; the conjugation equivalence of homomorphisms of Section 2; and the diagram condition of Proposition 6, under which a homotopy class of selfmaps admits a coincidence-free representative and so does not have the Borsuk-Ulam property with respect to the given free involution.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 2 (the short exact sequence (5), the braid sequence (8), and the diagram of Proposition 6).

import Mathlib

/-!
# The algebraic layer: involution extensions, braid data, and the Borsuk-Ulam
diagram condition

The algebraic layer of the BUP mission, carrying the interface of Daciberg Lima
Goncalves, John Guaschi, and Vinicius Casteluber Laass, "The Borsuk-Ulam
property for homotopy classes of selfmaps of surfaces of Euler characteristic
zero" (arXiv:1608.00397, 2016): the two-element group in multiplicative form;
the short exact sequences induced by free involutions of Section 2; the braid
data of a surface - the pure and full two-string braid groups of the sequence
(8), the Fadell-Neuwirth projection onto the fundamental group, and the
designated half-twist with its conjugation action on the pure braid group; the
conjugation equivalence of homomorphisms of Section 2; and the diagram
condition of Proposition 6 under which a homotopy class admits a
coincidence-free representative and so does not have the Borsuk-Ulam property.
-/

namespace BUP

/-- The two-element deck group of a double covering, in multiplicative form. -/
abbrev Z2 := Multiplicative (ZMod 2)

/-- The short exact sequence 1 -> A -> B -> Z2 -> 1 induced by a free
involution of a surface with fundamental group A: the covering injection of the
fundamental group A into the fundamental group B of the orbit space, and the
projection of B onto the deck group. -/
structure InvSES (A B : Type*) [Group A] [Group B] where
  inj : A →* B
  proj : B →* Z2
  inj_inj : ∀ x y : A, inj x = inj y → x = y
  proj_surj : ∀ z : Z2, ∃ b : B, proj b = z
  ex : ∀ b : B, proj b = 1 ↔ ∃ a : A, inj a = b

/-- The braid data of a surface with fundamental group A: the pure two-string
braid group P, the full two-string braid group Bg, the inclusion iota and the
projection piBr of the sequence (8), the projection p1 of the Fadell-Neuwirth
fibration onto the fundamental group, and the designated half-twist sigma with
its conjugation automorphism lsigma of the pure braid group and the full-twist
square sigmaSq, which projects trivially to the fundamental group. -/
structure BraidData (A P Bg : Type*) [Group A] [Group P] [Group Bg] where
  iota : P →* Bg
  piBr : Bg →* Z2
  p1 : P →* A
  iota_inj : ∀ x y : P, iota x = iota y → x = y
  piBr_surj : ∀ z : Z2, ∃ g : Bg, piBr g = z
  ex : ∀ g : Bg, piBr g = 1 ↔ ∃ p : P, iota p = g
  p1_surj : ∀ a : A, ∃ p : P, p1 p = a
  sigma : Bg
  sigma_ne : piBr sigma ≠ 1
  lsigma : P ≃* P
  lsigma_conj : ∀ p : P, iota (lsigma p) = sigma * iota p * sigma⁻¹
  sigmaSq : P
  sigmaSq_eq : iota sigmaSq = sigma * sigma
  sigmaSq_triv : p1 sigmaSq = 1

/-- Conjugation equivalence of homomorphisms of Section 2: two induced
homomorphisms are equivalent if one is obtained from the other by conjugation
with a loop. -/
def homEquiv {A : Type*} [Group A] (h1 h2 : A →* A) : Prop :=
  ∃ w : A, ∀ v : A, h1 v = w * h2 v * w⁻¹

/-- The diagram condition of Proposition 6: the homotopy class with induced
homomorphism h does not have the Borsuk-Ulam property with respect to the free
involution inducing C if and only if there are homomorphisms phi and psi making
the diagram (9) commute: the Fadell-Neuwirth projection of phi is h, psi
composed with the covering injection is the braid inclusion of phi, and the
braid projection of psi is the deck projection. -/
def NoBUP {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (C : InvSES A B) (D : BraidData A P Bg) (h : A →* A) : Prop :=
  ∃ phi : A →* P, ∃ psi : B →* Bg,
    (∀ a : A, D.p1 (phi a) = h a) ∧
    (∀ a : A, psi (C.inj a) = D.iota (phi a)) ∧
    (∀ b : B, D.piBr (psi b) = C.proj b)

end BUP


