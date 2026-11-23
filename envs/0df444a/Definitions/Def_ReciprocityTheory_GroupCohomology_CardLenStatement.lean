-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_CardLenStatement
-- name    : ReciprocityTheory_GroupCohomology_CardLenStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:13.606256+00:00
-- url     : https://prove2.me/theorems/9a52c91b-498e-41a4-924d-e38b1d89e979
-- title:
--   Card Len Statement
-- statement:
--   Definitions and structural lemmas for Card Len Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CardLenStatement.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
def PiRepStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (κ : Type u) (A : κ → TRep R G) (L : TRep R G) (π : ∀ a, Pair L (A a)),
  (∀ a, (π a).φ = MonoidHom.id G) → IsHomeomorph (fun (x : L.V) a => (π a).u x) →
  ∀ n, Bijective (LinearMap.pi fun a => ((π a).hom.f n)) ∧ Bijective (LinearMap.pi fun a => (π a).hom.H n)
def CentralStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (s : G) (c : R), s ∈ Subgroup.center G →
  (∀ m, M.rho s m = c • m) → ∀ n (x : M.H n), (c - 1) • x = 0
def QuadStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M M' : TRep R G) (U : Subgroup G), IsOpen (U : Set G) → U.index = 2 →
  IsUnit (2 : R) → ∀ P : Pair M' (M.resSub U), P.φ = U.subtype → IsHomeomorph P.u →
  (∀ g ∉ U, ∀ m, P.u (M'.rho g m) = -M.rho g (P.u m)) → ∀ n,
  Bijective (((Pair.res M U.subtype continuous_subtype_val).hom.H n).coprod (P.hom.H n))
def InfIsoStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  (∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R)) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → P.hom.QuasiIso
def IsZHat (G : Type u) [Group G] [TopologicalSpace G] (s : G) : Prop :=
  Dense (Subgroup.zpowers s : Set G) ∧ ∀ k : ℕ, 0 < k → ∃ W : Subgroup G, IsOpen (W : Set G) ∧ W.index = k
def ZHatStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (s : G), IsZHat G s → ∀ (M : TRep R G) [DiscreteTopology M.V], (∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) →
  (∃ e : H1 M.rho ≃ₗ[R] M.V ⧸ LinearMap.range (M.rho s - LinearMap.id),
    ∀ c : Z1 M.rho, e (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s)) ∧
  (∀ n, 1 < n → Subsingleton (M.H n)) ∧ (IsFiniteLength R M.V → M.coch.FinLen 1 ∧ M.coch.chi 1 = 0)
def ShiftStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (N : ℕ),
  (∀ (M : TRep R G) [DiscreteTopology M.V], (∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) → Subsingleton (M.H N)) →
  ∀ (M : TRep R G) [DiscreteTopology M.V], (∀ m : M.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) →
    ∀ n, N ≤ n → Subsingleton (M.H n)
def KilledStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M M' : TRep R G) [DiscreteTopology M.V] [DiscreteTopology M'.V]
  (P : Pair M M') (c : R), P.φ = MonoidHom.id G → (∀ m, P.u m = 0 → c • m = 0) →
  (∀ m' : M'.V, c • m' ∈ LinearMap.range P.u) → ∀ n,
  (∀ x, P.hom.H n x = 0 → c ^ 2 • x = 0) ∧ ∀ y : M'.H n, c ^ 2 • y ∈ LinearMap.range (P.hom.H n)
def CofinStatement : Prop := ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (G : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (t : R), Irreducible t →
  ∀ (K D : TRep R G) [DiscreteTopology K.V] [DiscreteTopology D.V] (i : Pair K D), i.φ = MonoidHom.id G →
  Injective i.u → (∀ x, x ∈ LinearMap.range i.u ↔ t • x = 0) → (∀ x : D.V, ∃ y, x = t • y) →
  (∀ x : D.V, ∃ m : ℕ, t ^ m • x = 0) → ∀ n, (∀ x : D.H n, ∃ m : ℕ, t ^ m • x = 0) ∧
    (IsFiniteLength R (K.H n) → IsArtinian R (D.H n))
def CardLenStatement : Prop := ∀ (R : Type u) [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
  (H : Type u) [AddCommGroup H] [Module R H], (IsFiniteLength R H ↔ Finite H) ∧
  (Finite H → Nat.card H = Nat.card (IsLocalRing.ResidueField R) ^ (Module.length R H).toNat)
end
end ReciprocityTheory.Coh


