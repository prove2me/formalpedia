-- Prove2me | Definitions.Def_LocalConjugacy_Groups
-- name    : LocalConjugacy_Groups
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T03:16:50.105602+00:00
-- url     : https://prove2.me/theorems/9aed5385-8bc8-4ae7-a9cc-8cce041c8683
-- title:
--   Profinite groups and local subgroup conditions
-- statement:
--   Shared group-theoretic definitions for the paper: pronilpotence, prosupersolvability, prosolvability, pro-$p$ groups, profinite Hall and Sylow subgroups, conjugacy, local conjugacy, local containment, supplements, internal semidirect products, normal intersections, and fixed points. Mathlib supplies the underlying groups, topology, subgroups, quotients, complements, normality, and actions.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1, https://arxiv.org/pdf/2609.37678v1, §§1–4, pp. 1–8. Adapted in part from the author’s local Apache-2.0 Lean development.

import Mathlib

/-!
# Profinite local conjugacy: the common language

This module reuses Mathlib's `ProfiniteGrp`, `Subgroup`, quotient groups,
`OpenNormalSubgroup`, `Group.IsNilpotent`, `Group.IsSolvable`, `IsPGroup`,
`MulAut.conj`, `Subgroup.IsComplement'`, `Subgroup.Normal`, and action fixed points.
Only concepts without an appropriate interface at the pinned revision are added.
All subgroups inherit their topology. Every source occurrence of a closed subgroup
is accompanied by a closedness hypothesis in the theorem using it.

Conjugation is on the left: `conjugate g H = g H g⁻¹`; the paper writes this as
`H^(g⁻¹)`. Existential conjugacy and local inclusion do not depend on this choice.
The finite cyclic-factor series below is equivalent to finite supersolvability:
normality is required in the whole group, and repeated terms are harmless.
-/

namespace LocalConjugacy

/-- Every finite set generates a finite subgroup. This is an algebraic
condition, separate from the topology on the group. -/
def LocallyFiniteGroup (G : Type*) [Group G] : Prop :=
  ∀ s : Set G, s.Finite → (Subgroup.closure s : Set G).Finite

/-- A finite invariant series with cyclic factors (supersolvability). -/
def Supersolvable (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (s : ℕ → Subgroup G), s 0 = ⊥ ∧ s n = ⊤ ∧ Monotone s ∧
    (∀ i, (s i).Normal) ∧ ∀ i < n, ∃ g : G, s (i + 1) = s i ⊔ Subgroup.zpowers g

/-- Every continuous finite quotient is nilpotent. For profinite groups this
is the standard definition of pronilpotence. -/
def Pronilpotent (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, Group.IsNilpotent (G ⧸ U.toSubgroup)

/-- Every open-normal quotient is supersolvable. This is used only for profinite
groups, where these quotients are finite. -/
def Prosupersolvable (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, Supersolvable (G ⧸ U.toSubgroup)

/-- Every continuous finite quotient is solvable. -/
def Prosolvable (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, Group.IsSolvable (G ⧸ U.toSubgroup)

/-- A pro-`p` group; this does not assert that elements have finite order. -/
def IsProP (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup)

/-- The prime divisors of a finite group's order belong to `π`. -/
def HasPrimes (π : Set ℕ) (G : Type*) [Group G] : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p ∈ π

/-- A finite Hall subgroup: its order has primes in `π`, its index outside `π`. -/
def IsHall {G : Type*} [Group G] (π : Set ℕ) (H : Subgroup G) : Prop :=
  HasPrimes π H ∧ ∀ p : ℕ, p.Prime → p ∣ H.index → p ∉ π

/-- A closed Hall subgroup of a profinite group, tested in every finite quotient. -/
def IsHallPro {G : Type*} [Group G] [TopologicalSpace G]
    (π : Set ℕ) (H : Subgroup G) : Prop :=
  IsClosed (H : Set G) ∧ ∀ U : OpenNormalSubgroup G,
    IsHall π (H.map (QuotientGroup.mk' U.toSubgroup))

/-- A closed subgroup of `H` that is maximal among its closed pro-`p`
subgroups. `P` and `H` are both represented as subgroups of the ambient group. -/
def IsSylowPro (p : ℕ) {G : Type*} [Group G] [TopologicalSpace G]
    (H P : Subgroup G) : Prop :=
  P ≤ H ∧ IsClosed (P : Set G) ∧ IsProP p P ∧
    ∀ Q : Subgroup G, Q ≤ H → IsClosed (Q : Set G) → IsProP p Q → P ≤ Q → Q = P

/-- Left conjugation of a subgroup. -/
def conjugate {G : Type*} [Group G] (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g)

/-- Conjugacy in the ambient group. -/
def Conjugate {G : Type*} [Group G] (H K : Subgroup G) : Prop :=
  ∃ g : G, conjugate g H = K

/-- For each prime, a Sylow subgroup of `H` is conjugate to one of `K`. -/
def LocallyConjugate {G : Type*} [Group G] [TopologicalSpace G]
    (H K : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ P Q : Subgroup G,
    IsSylowPro p H P ∧ IsSylowPro p K Q ∧ Conjugate P Q

/-- `H` contains a conjugate of a Sylow subgroup of `J` for every prime. -/
def LocallyContains {G : Type*} [Group G] [TopologicalSpace G]
    (H J : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ P : Subgroup G, IsSylowPro p J P ∧
    ∃ g : G, conjugate g P ≤ H

/-- Setwise supplement; with `N` normal this is equivalent to `N ⊔ H = ⊤`. -/
def Supplements {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  ∀ g : G, ∃ n ∈ N, ∃ h ∈ H, n * h = g

/-- Internal semidirect product, with `N` the normal factor. -/
def Splits {G : Type*} [Group G] (N J : Subgroup G) : Prop :=
  N.Normal ∧ N.IsComplement' J

/-- `N ∩ H` is normal in `N`, not just normal in `H`. -/
def IntersectionNormal {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  ((N ⊓ H).subgroupOf N).Normal

/-- A subgroup fixes at least one common point. -/
def HasFixedPoint {G Ω : Type*} [Group G] [MulAction G Ω] (H : Subgroup G) : Prop :=
  (MulAction.fixedPoints H Ω).Nonempty

/-- Local fixed points, allowing a different point for each prime. -/
def SylowFixedPoints {G Ω : Type*} [Group G] [TopologicalSpace G]
    [MulAction G Ω] (H : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ P : Subgroup G,
    IsSylowPro p H P ∧ HasFixedPoint (Ω := Ω) P

/-- The finite quotients have cyclic image of a single topological generator. -/
def Procyclic (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ g : G, Dense (Subgroup.zpowers g : Set G)


end LocalConjugacy


