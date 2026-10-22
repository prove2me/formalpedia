-- Prove2me | Definitions.Def_ESL_alg
-- name    : ESL_alg
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T02:07:54.335395+00:00
-- url     : https://prove2.me/theorems/0431cd03-7eca-4ac5-bb08-5b119b4b6b01
-- title:
--   The algebraic layer: normal exactness and descent along quotient maps
-- statement:
--   The algebraic interface of the exact sequence for generalized string links over surfaces. The definition carries: the normal-exactness predicate for a pair of homomorphisms - the kernel of the second is exactly the normal closure of the image of the first, the exactness assertion of Theorem 3.1 of the paper, in the form appropriate to non-Abelian groups where the image of the first map need not be normal - and the two descent predicates recording that a homomorphism between quotient groups is compatible with the quotient maps: a two-sided descent commutes with the quotient maps on both sides, and a single-sided descent commutes with the quotient map of its source. The descent predicates are the interface through which the induced maps of the exact sequence - the descended inclusion of the disk classes and the descended loop-reading map - are handled.
-- source:
--   J. R. T. Theodoro de Lima, An exact sequence for generalized string links over surfaces, LAJM - Latin-American Journal of Mathematics 2 (2023) no. 1, Section 3 (the exactness shape of Theorem 3.1 and the induced maps between quotients).

import Mathlib

/-!
# The algebraic layer: normal exactness and descent

The algebraic layer of the ESL mission, carrying the interface of Juliana
R. T. Theodoro de Lima, "An exact sequence for generalized string links
over surfaces" (LAJM - Latin-American Journal of Mathematics 2 (2023),
no. 1, 31-43): the normal-exactness shape of Theorem 3.1 - the kernel of
the second map of a pair of homomorphisms is the normal closure of the
image of the first - together with the descent predicates recording that a
homomorphism between quotient groups is compatible with the quotient maps,
through which the induced maps of the exact sequence are expressed.
-/

namespace ESL

/-- The pair (f, theta) is normally exact at the middle: the kernel of
theta is the normal closure of the image of f. This is the exactness
assertion of Theorem 3.1 of the source paper. -/
def NormalExact {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (theta : B →* C) : Prop :=
  MonoidHom.ker theta = Subgroup.normalClosure (Set.range f)

/-- The homomorphism fhat is a descent of f along the quotient maps qA and
qB: the square commutes, fhat carries the class of x to the class of
f x. -/
def DescendsAlong {A A' B B' : Type*} [Group A] [Group A'] [Group B] [Group B']
    (f : A →* B) (qA : A →* A') (qB : B →* B') (fhat : A' →* B') : Prop :=
  ∀ x : A, fhat (qA x) = qB (f x)

/-- The homomorphism thetahat is a descent of theta along the quotient map
qB: thetahat carries the class of x to theta x. -/
def DescendsAlongSingle {B B' C : Type*} [Group B] [Group B'] [Group C]
    (theta : B →* C) (qB : B →* B') (thetahat : B' →* C) : Prop :=
  ∀ x : B, thetahat (qB x) = theta x

end ESL


