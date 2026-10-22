-- Prove2me | Definitions.Def_BQC_tor
-- name    : BQC_tor
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T23:11:51.780504+00:00
-- url     : https://prove2.me/theorems/f5ea5726-445a-43d7-9aa9-68d4afdc6d43
-- title:
--   The world layer: the idealized braid quotient as a crystallographic group
-- statement:
--   The world layer of the braid quotient problem. The definition carries: the idealized quotient of the Artin braid group on n strings by the commutator subgroup of its pure braid group, which by Proposition 1 is a crystallographic group of dimension n(n-1)/2 - the rank of the abelianization of the pure braid group - whose holonomy group is the permutation layer, carried as an abstract crystallographic world of that dimension; and the realization predicate for an abstract finite group over the permutation layer - given by an embedding into it - recording when the group is realized by a subgroup of the quotient, that is, when the embedding lifts to a homomorphism into the quotient that commutes with the projections and is injective, as in Corollary 4 and Theorem 6.
-- source:
--   D. L. Goncalves, J. Guaschi, O. Ocampo, A quotient of the Artin braid groups related to crystallographic groups, Journal of Algebra 474 (2017) 393-423, Section 3 (Proposition 1).

import Mathlib
import Definitions.Def_BQC_alg

/-!
# The world layer: the idealized braid quotient as a crystallographic group

The world layer of the BQC mission: the idealized quotient of the Artin
braid group on n strings by the commutator subgroup of its pure braid group,
which by Proposition 1 is a crystallographic group of dimension n(n - 1)/2
whose holonomy group is the permutation layer; and the realization predicate
for an abstract finite group over the permutation layer, recording when a
finite subgroup of the permutation layer is realized by a subgroup of the
quotient, as in Corollary 4 and Theorem 6.
-/

namespace BQC

/-- The idealized world of the quotient of the Artin braid group on n strings
by the commutator subgroup of its pure braid group: by Proposition 1 it is a
crystallographic group of dimension n(n - 1)/2 - the rank of the abelianization
of the pure braid group - whose holonomy group is the permutation layer S. -/
abbrev BraidQuotient (n : Nat) (Q S : Type*) [Group Q] [Group S] [Fintype S] :=
  CryWorld (Nat.choose n 2) Q S

/-- The abstract finite group H over the permutation layer - given by an
embedding into S - is realized by a subgroup of the braid quotient: there is a
lift of the embedding to Q that commutes with the projections. This is the
realization of isomorphism classes of subgroups of the permutation layer by
subgroups of the quotient, as in Corollary 4 and Theorem 6. -/
def LiftsOver {n : Nat} {Q S : Type*} [Group Q] [Group S] [Fintype S]
    {H : Type} [Group H] [Fintype H]
    (W : BraidQuotient n Q S) (i : H →* S) : Prop :=
  ∃ f : H →* Q, (∀ h : H, W.proj (f h) = i h) ∧ (∀ x y : H, f x = f y → x = y)

end BQC


