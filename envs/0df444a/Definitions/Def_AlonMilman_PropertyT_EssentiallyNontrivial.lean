-- Prove2me | Definitions.Def_AlonMilman_PropertyT_EssentiallyNontrivial
-- name    : AlonMilman_PropertyT_EssentiallyNontrivial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:31:31.471885+00:00
-- url     : https://prove2.me/theorems/e140a0ef-5cd6-4065-a5e2-c7aeac089924
-- title:
--   Definition 4.5 — essentially nontrivial unitary representation
-- statement:
--   Let $H$ be a group and $V$ a complex Hilbert space. A unitary representation $\pi$ of $H$ in $V$ (a homomorphism from $H$ into the group of unitary operators on $V$) is **essentially nontrivial** if
--
--   $$\forall\, v \in V \setminus \{0\} \;\; \exists\, h \in H : \quad \pi(h) v \ne v,$$
--
--   that is, no nonzero vector is fixed by all of $\pi(H)$; equivalently, the trivial one-dimensional representation is not a subrepresentation of $\pi$.
--
--   This is the class of representations quantified over in the definition of property (T) (Definition 4.6).
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 84, Definition 4.5

import Mathlib

namespace AlonMilman.PropertyT

/-- Definition 4.5 (Alon–Milman 1985, p. 84): a unitary representation `π` of a group `H` in a
complex Hilbert space `V` is *essentially nontrivial* if for every vector `v ≠ 0` there is an
`h ∈ H` with `π(h) v ≠ v`.  A unitary representation is a group homomorphism from `H` into the
unitary group of the C⋆-algebra of bounded operators on `V`. -/
def EssentiallyNontrivial {H : Type} [Group H] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : H →* unitary (V →L[ℂ] V)) : Prop :=
  ∀ v : V, v ≠ 0 → ∃ h : H, (π h : V →L[ℂ] V) v ≠ v

end AlonMilman.PropertyT


