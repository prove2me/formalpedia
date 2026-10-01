-- Prove2me | Definitions.Def_LocalConjugacy_Proof_Definitions
-- name    : LocalConjugacy_Proof_Definitions
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T13:40:32.201714+00:00
-- url     : https://prove2.me/theorems/64bc81f0-8e3f-4136-9cbf-c8a608c711a4
-- title:
--   Proof interfaces for profinite groups
-- statement:
--   Auxiliary interfaces for profinite groups, prime sets, Hall and Sylow subgroups, normal supplements, continuous cocycles, and local conjugacy. These connect the supporting proofs to the canonical mission definitions.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

/-!
Definitions for Michael C. Burkhart, *Local conjugacy in prosolvable groups*.
Conjugation is on the left: `conjugate g H = g H g⁻¹`. Thus the paper's `H^g`
is `conjugate g⁻¹ H`. The cohomology convention uses a left action, so the
paper's `n^(j⁻¹)` is `j • n`.
-/

namespace LocalConjugacy

/-- Every finite set generates a finite subgroup. This is an algebraic
condition, separate from the topology on the group. -/
def LocallyFiniteGroup (G : Type*) [Group G] : Prop :=
  ∀ s : Set G, s.Finite → (Subgroup.closure s : Set G).Finite

/-- The usual topological hypotheses on a profinite group. -/
class Profinite (G : Type*) [Group G] [TopologicalSpace G] : Prop extends
  IsTopologicalGroup G, CompactSpace G, T2Space G, TotallyDisconnectedSpace G

/-- A finite invariant series with cyclic factors (supersolvability). -/
def Supersolvable (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (s : ℕ → Subgroup G), s 0 = ⊥ ∧ s n = ⊤ ∧ Monotone s ∧
    (∀ i, (s i).Normal) ∧ ∀ i < n, ∃ g : G, s (i + 1) = s i ⊔ Subgroup.zpowers g

/-- Every continuous finite quotient is nilpotent. For profinite groups this
is the standard definition of pronilpotence. -/
def Pronilpotent (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, Group.IsNilpotent (G ⧸ U.toSubgroup)

/-- Every continuous finite quotient is supersolvable. -/
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
  N.Normal ∧ Supplements N J ∧ N ⊓ J = ⊥

/-- `N ∩ H` is normal in `N`, not just normal in `H`. -/
def IntersectionNormal {G : Type*} [Group G] (N H : Subgroup G) : Prop :=
  ∀ n ∈ N, ∀ d ∈ N ⊓ H, n * d * n⁻¹ ∈ N ⊓ H

/-- A subgroup fixes at least one common point. -/
def HasFixedPoint {G Ω : Type*} [Group G] [MulAction G Ω] (H : Subgroup G) : Prop :=
  ∃ x : Ω, ∀ h ∈ H, h • x = x

/-- Transitivity stated without a topology on the acted-on set. -/
def Transitive {G Ω : Type*} [Group G] [MulAction G Ω] : Prop :=
  ∀ x y : Ω, ∃ g : G, g • x = y

/-- Local fixed points, allowing a different point for each prime. -/
def SylowFixedPoints {G Ω : Type*} [Group G] [TopologicalSpace G]
    [MulAction G Ω] (H : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ P : Subgroup G,
    IsSylowPro p H P ∧ HasFixedPoint (Ω := Ω) P

/-- The finite quotients have cyclic image of a single topological generator. -/
def Procyclic (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ g : G, Dense (Subgroup.zpowers g : Set G)

/-- Continuous nonabelian 1-cocycles on a closed subgroup of `J`. -/
abbrev Cocycle {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N] (K : Subgroup J) :=
  _root_.LocalConjugacy.Cocycle (N := N) K

/-- The usual equivalence of nonabelian cocycles, with one global conjugator. -/
def Cohomologous {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N] {K : Subgroup J}
    (f g : Cocycle (N := N) K) : Prop :=
  ∃ n : N, ∀ x : K, g.toFun x = n⁻¹ * f.toFun x * ((x : J) • n)

/-- Finite, unbundled version of the same cocycle equation, with the action
given explicitly as a homomorphism into automorphisms. -/
def CocycleFn {J N : Type*} [Group J] [Group N]
    (a : J →* MulAut N) (f : J → N) : Prop :=
  ∀ s t, f (s * t) = f s * a s (f t)



/-- Stable elements: equality up to a single coboundary on each intersection
`K ∩ j K j⁻¹`. This also makes sense for nonnormal `K`. -/
def InvariantUnder {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N]
    (L K : Subgroup J) (f : Cocycle (N := N) K) : Prop :=
  ∀ j ∈ L, ∃ n : N, ∀ (x : J) (hx : x ∈ K) (hjx : j⁻¹ * x * j ∈ K),
    j • f.toFun ⟨j⁻¹ * x * j, hjx⟩ = n⁻¹ * f.toFun ⟨x, hx⟩ * (x • n)

/-- Equality of restrictions up to cohomology, written on representatives. -/
def RestrictsTo {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N]
    {K L : Subgroup J} (hKL : K ≤ L)
    (f : Cocycle (N := N) L) (g : Cocycle (N := N) K) : Prop :=
  ∃ n : N, ∀ x : K,
    g.toFun x = n⁻¹ * f.toFun ⟨x, hKL x.property⟩ * ((x : J) • n)

/-- Restriction is an isomorphism onto the stable classes. Injectivity and
surjectivity are expressed on representatives to avoid choices of quotients. -/
def RestrictionIsomorphism {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
    [TopologicalSpace N] [MulDistribMulAction J N]
    (L K : Subgroup J) (hKL : K ≤ L) : Prop :=
  (∀ (f g : Cocycle (N := N) L),
    (∃ n : N, ∀ x : K, g.toFun ⟨x, hKL x.property⟩ =
      n⁻¹ * f.toFun ⟨x, hKL x.property⟩ * ((x : J) • n)) → Cohomologous f g) ∧
  (∀ g : Cocycle (N := N) K, InvariantUnder L K g →
    ∃ f : Cocycle (N := N) L, RestrictsTo hKL f g)

/-- The product topology on the semidirect product. -/
instance semidirectTopology {J N : Type*} [Group J] [Group N]
    [TopologicalSpace J] [TopologicalSpace N] (a : J →* MulAut N) :
    TopologicalSpace (N ⋊[a] J) :=
  TopologicalSpace.induced (fun x => (x.left, x.right)) inferInstance

/-- The semidirect product attached to the left action on the coefficient group. -/
abbrev ActionProduct (J N : Type*) [Group J] [Group N] [MulDistribMulAction J N] :=
  N ⋊[MulDistribMulAction.toMulAut J N] J

/-- Restriction of a continuous cocycle along subgroup inclusion. -/
def restrictCocycle {J N : Type*} [Group J] [Group N]
    [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]
    {K L : Subgroup J} (hKL : K ≤ L)
    (f : Cocycle (N := N) L) : Cocycle (N := N) K where
  toFun := fun x => f.toFun ⟨x, hKL x.property⟩
  continuous_toFun := f.continuous_toFun.comp
    (continuous_subtype_val.subtype_mk fun x => hKL x.property)
  map_mul := fun x y => f.map_mul ⟨x, hKL x.property⟩ ⟨y, hKL y.property⟩

/-- Prime divisors of the supernatural order of a profinite group: those
occurring in at least one continuous finite quotient. -/
def PrimeDivisor (J : Type*) [Group J] [TopologicalSpace J] :=
  {p : Nat.Primes // ∃ U : OpenNormalSubgroup J, p.val ∣ Nat.card (J ⧸ U.toSubgroup)}

/-- Primary decomposition on cocycle representatives: the restriction map
lands in the stable classes, is injective, and is onto the product of the
stable classes, indexed by the paper's `π(J)`. -/
def PrimaryDecomposition {J N : Type*} [Group J] [Group N]
    [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]
    (P : PrimeDivisor J → Subgroup J) : Prop :=
  (∀ (f : Cocycle (N := N) (⊤ : Subgroup J)) (p : PrimeDivisor J),
    InvariantUnder ⊤ (P p) (restrictCocycle (show P p ≤ ⊤ from le_top) f)) ∧
  (∀ f g : Cocycle (N := N) (⊤ : Subgroup J),
    (∀ p : PrimeDivisor J, ∃ n : N, ∀ x : P p,
      g.toFun ⟨x, Subgroup.mem_top _⟩ =
        n⁻¹ * f.toFun ⟨x, Subgroup.mem_top _⟩ * ((x : J) • n)) → Cohomologous f g) ∧
  (∀ f : (p : PrimeDivisor J) → Cocycle (N := N) (P p),
    (∀ p, InvariantUnder ⊤ (P p) (f p)) →
    ∃ g : Cocycle (N := N) (⊤ : Subgroup J),
      ∀ p, RestrictsTo (show P p ≤ ⊤ from le_top) g (f p))

end LocalConjugacy

end LocalConjugacy.Proof

end


