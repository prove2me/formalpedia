-- Prove2me | Definitions.Def_BUP_tor
-- name    : BUP_tor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T23:09:32.208281+00:00
-- url     : https://prove2.me/theorems/9aeeedd1-f4a7-4d31-80d8-2f1745473412
-- title:
--   The world layer: the idealized torus and Klein bottle with their free involutions
-- statement:
--   The idealized geometric worlds in which the three classification theorems of the paper are stated. The torus world bundles the involution extension and the braid data of the two-torus, the integral coordinates identifying its fundamental group with the integer lattice of rank two, the designated deck element with its conjugation action on the fundamental group and the designated preimage of its square, and the generation of the orbit group; the orientation predicates record whether the deck transformation preserves orientation - acting trivially on the fundamental group - or reverses it - fixing the first integral coordinate and flipping the second, the two classes of free involutions of the torus of Proposition 25; the four entries of the integral matrix of an induced homomorphism are read off from the coordinates of the images of the two coordinate loops. The Klein bottle world bundles the corresponding deck data together with the double covering of the Klein bottle by the torus, given by the covering injection and the deck projection of the covering sequence, and the lifting predicate records when every value of a homomorphism of the fundamental group of the Klein bottle lies in the image of the covering injection - the lifting condition through which Theorem 3 classifies the Borsuk-Ulam property.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Sections 3-6 (Propositions 25 and 27, Lemma 26, and Theorems 1-3; the double covering of the Klein bottle by the torus).

import Mathlib
import Definitions.Def_BUP_alg

/-!
# The world layer: the idealized torus and Klein bottle with their free
involutions

The world layer of the BUP mission: the idealized two-torus with a free
involution - the involution extension, the braid data of the torus, integral
coordinates on the fundamental group, and the designated deck transformation
with its lift data - together with the orientation predicates of Proposition
25 and the four entries of the integral matrix of an induced homomorphism; and
the idealized Klein bottle with its free involution, its deck data, and the
double covering of the Klein bottle by the torus, through which Theorem 3
formulates the lifting condition.
-/

namespace BUP

/-- The idealized world of the two-torus with a free involution: the
involution extension C, the braid data D of the torus, integral coordinates on
the fundamental group, the deck transformation act on the fundamental group,
and the designated deck element deckElem lifting the nontrivial deck class,
with a designated preimage deckSq of its square; every element of the orbit
group is a product of a covered element with a power of the deck element. -/
structure TorusWorld (A B P Bg : Type*) [Group A] [Group B] [Group P] [Group Bg] where
  C : InvSES A B
  D : BraidData A P Bg
  coord : A ≃* Multiplicative (Int × Int)
  act : A ≃* A
  deckElem : B
  deckElem_ne : C.proj deckElem ≠ 1
  deck_act : ∀ a : A, deckElem * C.inj a * deckElem⁻¹ = C.inj (act a)
  deckSq : A
  deckSq_eq : C.inj deckSq = deckElem * deckElem
  gen : ∀ b : B, ∃ (a : A) (k : Int), b = C.inj a * deckElem ^ k

/-- The integral coordinates of a loop of the torus. -/
def TorusWorld.coordsOf {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (a : A) : Int × Int :=
  Multiplicative.toAdd (W.coord a)

/-- The first coordinate loop of the torus. -/
def TorusWorld.e1 {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) : A :=
  W.coord.symm (Multiplicative.ofAdd ((1, 0) : Int × Int))

/-- The second coordinate loop of the torus. -/
def TorusWorld.e2 {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) : A :=
  W.coord.symm (Multiplicative.ofAdd ((0, 1) : Int × Int))

/-- The deck transformation preserves orientation: it acts trivially on the
fundamental group of the torus. -/
def TorusPres {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) : Prop :=
  ∀ a : A, W.act a = a

/-- The deck transformation reverses orientation: in the integral coordinates
it fixes the first coordinate and flips the second. -/
def TorusRev {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) : Prop :=
  ∀ a : A,
    (W.coordsOf (W.act a)).1 = (W.coordsOf a).1 ∧ (W.coordsOf (W.act a)).2 = -(W.coordsOf a).2

/-- The (1,1) entry of the integral matrix of the homomorphism induced on the
fundamental group of the torus by the class h. -/
def TorusWorld.beta11 {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (h : A →* A) : Int :=
  (W.coordsOf (h (W.e1))).1

/-- The (2,1) entry of the integral matrix. -/
def TorusWorld.beta21 {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (h : A →* A) : Int :=
  (W.coordsOf (h (W.e1))).2

/-- The (1,2) entry of the integral matrix. -/
def TorusWorld.beta12 {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (h : A →* A) : Int :=
  (W.coordsOf (h (W.e2))).1

/-- The (2,2) entry of the integral matrix. -/
def TorusWorld.beta22 {A B P Bg : Type*} [Group A] [Group B] [Group P] [Group Bg]
    (W : TorusWorld A B P Bg) (h : A →* A) : Int :=
  (W.coordsOf (h (W.e2))).2

/-- The idealized world of the Klein bottle with its free involution: the
involution extension C, the braid data D of the Klein bottle, the deck
transformation data, and the double covering of the Klein bottle by the torus
with fundamental group T, given by the covering injection and the deck
projection of the covering sequence. -/
structure KleinWorld (A B P Bg T : Type*) [Group A] [Group B] [Group P] [Group Bg] [Group T] where
  C : InvSES A B
  D : BraidData A P Bg
  act : A ≃* A
  deckElem : B
  deckElem_ne : C.proj deckElem ≠ 1
  deck_act : ∀ a : A, deckElem * C.inj a * deckElem⁻¹ = C.inj (act a)
  gen : ∀ b : B, ∃ (a : A) (k : Int), b = C.inj a * deckElem ^ k
  torInj : T →* A
  torPar : A →* Z2
  torInj_inj : ∀ x y : T, torInj x = torInj y → x = y
  torPar_surj : ∀ z : Z2, ∃ a : A, torPar a = z
  tor_ex : ∀ a : A, torPar a = 1 ↔ ∃ t : T, torInj t = a

/-- The homomorphism h on the fundamental group of the Klein bottle lifts
through the double covering by the torus: every value of h lies in the image of
the covering injection. -/
def KleinWorld.LiftsTor {A B P Bg T : Type*} [Group A] [Group B] [Group P] [Group Bg] [Group T]
    (W : KleinWorld A B P Bg T) (h : A →* A) : Prop :=
  ∀ v : A, ∃ t : T, W.torInj t = h v

end BUP


