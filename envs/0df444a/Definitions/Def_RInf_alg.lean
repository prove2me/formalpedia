-- Prove2me | Definitions.Def_RInf_alg
-- name    : RInf_alg
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T23:10:15.189436+00:00
-- url     : https://prove2.me/theorems/88e7b134-42ef-404d-bd81-d39d0869f169
-- title:
--   The algebraic layer: twisted conjugacy, Reidemeister numbers, and the R-infinity property
-- statement:
--   The algebraic interface of the R-infinity problem for pure Artin braid groups. The definition carries: the twisted conjugacy relation of the introduction - two elements of a group are twisted conjugate via an endomorphism if one is obtained from the other by conjugation corrected by the endomorphism; the infinitude of the Reidemeister number, recorded as the existence of an infinite sequence of pairwise non-twisted-conjugate elements; the R-infinity property of a group - every automorphism has infinite Reidemeister number; and the additive twin of the relation for an automorphism of a free abelian layer, written additively, together with the twin of the infinitude and the eigenvalue-one property of such an automorphism - a nonzero vector fixed by it - through which the representation-theoretic analysis of the paper enters.
-- source:
--   K. Dekimpe, D. L. Goncalves, O. Ocampo, The R-infinity property for pure Artin braid groups, Monatshefte fur Mathematik 195 (2021) 15-33, Sections 1-2 (the twisted conjugacy relation, the Reidemeister number, and Remark 1).

import Mathlib

/-!
# The algebraic layer: twisted conjugacy, Reidemeister numbers, and the
R-infinity property

The algebraic layer of the RInf mission, carrying the interface of Karel
Dekimpe, Daciberg Lima Goncalves, and Oscar Ocampo, "The R-infinity property
for pure Artin braid groups" (Monatshefte fur Mathematik 195 (2021), 15-33):
the twisted conjugacy relation of the introduction and the infinitude of the
Reidemeister number as an infinite sequence of pairwise non-twisted-conjugate
elements; the R-infinity property of a group; and the additive twin of the
relation for an automorphism of a free abelian layer, with the eigenvalue-one
property of such an automorphism.
-/

namespace RInf

/-- Twisted conjugacy via the endomorphism α: x and y are twisted conjugate if
x = z y α(z)⁻¹ for some z. -/
def TwistedConj {G : Type*} [Group G] (α : G →* G) (x y : G) : Prop :=
  ∃ z : G, x = z * y * (α z)⁻¹

/-- The Reidemeister number of α is infinite: there is an infinite sequence of
pairwise non-twisted-conjugate elements. -/
def ReidInf {G : Type*} [Group G] (α : G →* G) : Prop :=
  ∃ f : Nat → G, ∀ m n : Nat, m ≠ n → ¬ TwistedConj α (f m) (f n)

/-- The R-infinity property: every automorphism of G has infinite Reidemeister
number. -/
def RInfinity (G : Type*) [Group G] : Prop :=
  ∀ α : G ≃* G, ReidInf α.toMonoidHom

/-- Twisted conjugacy for an automorphism m of a free abelian layer, written
additively: x = z + y - m z. -/
def TwistedConjAdd {A : Type*} [AddCommGroup A] (m : A ≃+ A) (x y : A) : Prop :=
  ∃ z : A, x = z + y - m z

/-- The Reidemeister number of the automorphism m of the free abelian layer is
infinite. -/
def ReidInfAdd {A : Type*} [AddCommGroup A] (m : A ≃+ A) : Prop :=
  ∃ f : Nat → A, ∀ i j : Nat, i ≠ j → ¬ TwistedConjAdd m (f i) (f j)

/-- The automorphism m of the free abelian layer has the eigenvalue one: a
nonzero vector fixed by m. -/
def HasEigenOne {A : Type*} [AddCommGroup A] (m : A ≃+ A) : Prop :=
  ∃ v : A, v ≠ 0 ∧ m v = v

end RInf


