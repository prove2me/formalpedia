-- Prove2me | Definitions.Def_PoAIndep_Topology_Supplement_Inhomogeneous
-- name    : PoAIndep_Topology_Supplement_Inhomogeneous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:06:51.178009+00:00
-- url     : https://prove2.me/theorems/6560df75-fc2b-45a6-bd8e-d80dbbf07fac
-- title:
--   Definition 4.7, p. 16 — homogeneous and inhomogeneous classes of latency functions
-- statement:
--   Let $\mathcal L$ be a class of latency functions. It is **homogeneous** when every member vanishes at zero, and **inhomogeneous** otherwise:
--
--   $$\operatorname{Homogeneous}(\mathcal L)\iff \forall\ell\in\mathcal L,\ \ell(0)=0,
--   \qquad
--   \operatorname{Inhomogeneous}(\mathcal L)\iff \exists\ell\in\mathcal L,\ \ell(0)\ne0.$$
--
--   For nonnegative latency functions, inhomogeneity is equivalent to the existence of a member with positive latency at zero congestion. This is the class hypothesis of Lemma 4.8 and Theorem 4.9; it does not require diversity or closure under positive scaling.
--
--   **Formalization Note** These predicates are defined on arbitrary sets of real functions and used with the published `IsStandardClass` predicate. No regularity or positivity condition is added by this definition.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 16, Definition 4.7

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology.Supplement

/-- Definition 4.7 (p. 16): a class `L` of latency functions is *homogeneous* if `ℓ(0) = 0` for
every `ℓ ∈ L`, and *inhomogeneous* otherwise, i.e. some `ℓ ∈ L` has `ℓ(0) ≠ 0`. -/
def IsHomogeneous (L : Set (ℝ → ℝ)) : Prop :=
  ∀ ℓ ∈ L, ℓ 0 = 0

/-- Definition 4.7 (p. 16): `L` is inhomogeneous, i.e. not homogeneous: some `ℓ ∈ L` has
`ℓ(0) ≠ 0`. -/
def IsInhomogeneous (L : Set (ℝ → ℝ)) : Prop :=
  ∃ ℓ ∈ L, ℓ 0 ≠ 0

end PoAIndep.Topology.Supplement


