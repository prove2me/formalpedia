-- Prove2me | Definitions.Def_QuantumHMMR_IsCliffordGenSet
-- name    : QuantumHMMR_IsCliffordGenSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:48.087305+00:00
-- url     : https://prove2.me/theorems/2f7745b5-f951-4e18-ba86-60c85a300c43
-- title:
--   Finite inverse-closed generating set $G \subseteq \mathcal C_2$ containing the identity
-- statement:
--   Let $\mathcal C_2$ be the two-qubit Clifford group modulo global phase: the unitary normalizer of the two-qubit Pauli group, with two unitaries identified when they differ by a scalar phase. A finite set $G \subseteq \mathcal C_2$ is an **admissible generating set** when
--
--   1. the class of the identity lies in $G$;
--   2. $G$ is inverse-closed: for every $g \in G$ the class of $g^{-1}$ lies in $G$;
--   3. $G$ generates: every element of $\mathcal C_2$ is a finite product of elements of $G$.
--
--   Such a set is fixed once and for all in Section 4; the local Clifford updates of the walk are drawn uniformly from it.
--
--   **Formalization Note** $G$ is a `Finset` of classes in the published `Clifford.ProjectiveGroup 2`. Inverse-closure and generation are stated on classes through the published representatives, so a set whose matrix representatives close only up to a phase qualifies. The class of $U^{-1}$ does not depend on the phase of the representative $U$.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 4, p.11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords

namespace QuantumHMMR

open QAlgorithms

/-- A finite inverse-closed generating set `G ⊆ C₂` of the two-qubit Clifford group modulo global
phase, containing the identity (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §4, p.11: "Fix a finite inverse-closed generating set
`G ⊆ C₂` containing the identity").

The three clauses: the class of the identity lies in `G`; for every `g ∈ G` the class of the
inverse of (a representative of) `g` lies in `G`; every class of `C₂` is the class of a finite
product of representatives of elements of `G`.

**Formalization Note** `C₂` is the published `Clifford.ProjectiveGroup 2`: the unitary normalizer
of the Pauli group modulo every scalar phase. `G` is a `Finset` of classes, as printed ("modulo
global phase"); inverse-closure and generation are stated on classes, so a generating set whose
matrix representatives close only up to a phase is allowed. The class of `U⁻¹` does not depend
on the phase of the representative `U`. -/
def IsCliffordGenSet (G : Finset (Clifford.ProjectiveGroup 2)) : Prop :=
  Quotient.mk (Clifford.phaseSetoid 2) 1 ∈ G ∧
  (∀ g ∈ G, Quotient.mk (Clifford.phaseSetoid 2) (Clifford.representative g)⁻¹ ∈ G) ∧
  ∀ c : Clifford.ProjectiveGroup 2, ∃ l : List (Clifford.ProjectiveGroup 2), (∀ x ∈ l, x ∈ G) ∧
    c = Quotient.mk (Clifford.phaseSetoid 2) (l.map Clifford.representative).prod

end QuantumHMMR


