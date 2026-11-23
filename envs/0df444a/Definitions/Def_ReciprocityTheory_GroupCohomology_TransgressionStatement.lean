-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
-- name    : ReciprocityTheory_GroupCohomology_TransgressionStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:55.473904+00:00
-- url     : https://prove2.me/theorems/72ec924e-87fa-42d6-a74c-48c8e6bb506c
-- title:
--   Transgression Statement
-- statement:
--   Definitions and structural lemmas for Transgression Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionStatement.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
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
section Defs
variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {M : TRep R G} {M' : TRep R G'}
def Pair.h0 (P : Pair M M') : H0 M.rho →ₗ[R] H0 M'.rho :=
  P.u.restrict fun m hm g => by rw [← P.equiv, hm (P.φ g)]
def Pair.h1 (P : Pair M M') : H1 M.rho →ₗ[R] H1 M'.rho :=
  pairH1DecompositionMap M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv
def Pair.h2 (P : Pair M M') : H2 M.rho →ₗ[R] H2 M'.rho :=
  compatiblePairH2 M.rho M'.rho P.φ P.φ_cont P.u P.u_cont P.equiv
def IsLow (M : TRep R G) (e₀ : M.H 0 ≃ₗ[R] H0 M.rho) (e₁ : M.H 1 ≃ₗ[R] H1 M.rho)
    (e₂ : M.H 2 ≃ₗ[R] H2 M.rho) : Prop :=
  (∀ x hx, (e₀ (M.coch.cls 0 x hx) : M.V) = x.1 ![]) ∧
  (∀ x hx, ∃ hz : (fun g => x.1 ![g]) ∈ Z1 M.rho, e₁ (M.coch.cls 1 x hx) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
  ∀ x hx, ∃ hz : (fun g : G × G => x.1 ![g.1, g.2]) ∈ Z2 M.rho,
    e₂ (M.coch.cls 2 x hx) = Submodule.Quotient.mk ⟨_, hz⟩
def Cx.FinGen (A : Cx R) (N : ℕ) : Prop :=
  (∀ n, Module.Finite R (A.H n)) ∧ ∀ n, N < n → Subsingleton (A.H n)
def Cx.chiRk (A : Cx R) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (N + 1), (-1) ^ n * (Module.finrank R (A.H n) : ℤ)
end Defs
def LowNatStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  (M : TRep R G) (M' : TRep R G') (P : Pair M M') e₀ e₁ e₂ e₀' e₁' e₂', IsLow M e₀ e₁ e₂ → IsLow M' e₀' e₁' e₂' →
  (∀ x, e₀' (P.hom.H 0 x) = P.h0 (e₀ x)) ∧ (∀ x, e₁' (P.hom.H 1 x) = P.h1 (e₁ x)) ∧
  ∀ x, e₂' (P.hom.H 2 x) = P.h2 (e₂ x)
def LowCupStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (b : Pairing M N P) cup m₀ m₁ m₂ n₀ n₁ n₂ p₀ p₁ p₂,
  IsCup b cup → IsLow M m₀ m₁ m₂ → IsLow N n₀ n₁ n₂ → IsLow P p₀ p₁ p₂ →
  (∀ x y, p₂ (cup 1 1 x y) = cupProductH1H1 M.rho N.rho P.rho b.β b.cont b.equiv N.cont (m₁ x) (n₁ y)) ∧
  (∀ x y, p₂ (cup 0 2 x y) = cupProductH0H2 M.rho N.rho P.rho b.β b.cont b.equiv (m₀ x) (n₂ y)) ∧
  ∀ x y, p₂ (cup 2 0 x y) = cupProductH2H0 M.rho N.rho P.rho b.β b.cont b.equiv (m₂ x) (n₀ y)
def LowLESStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A B C : TRep R G) (i : Pair A B) (p : Pair B C), admitted i p →
  ∃ (δ₀ : H0 C.rho →ₗ[R] H1 A.rho) (δ₁ : H1 C.rho →ₗ[R] H2 A.rho),
    (∀ (c : H0 C.rho) (b : B.V) (a : Z1 A.rho), p.u b = c → (∀ g, i.u (a.1 g) = B.rho g b - b) →
      δ₀ c = Submodule.Quotient.mk a) ∧
    (∀ (c : Z1 C.rho) (b : G → B.V) (a : Z2 A.rho), Continuous b → (∀ g, p.u (b g) = c.1 g) →
      (∀ g, i.u (a.1 g) = d1 B.rho b g) → δ₁ (Submodule.Quotient.mk c) = Submodule.Quotient.mk a) ∧
    Injective i.h0 ∧ Exact i.h0 p.h0 ∧ Exact p.h0 δ₀ ∧ Exact δ₀ i.h1 ∧ Exact i.h1 p.h1 ∧ Exact p.h1 δ₁ ∧
    Exact δ₁ i.h2 ∧ Exact i.h2 p.h2 ∧ (Subsingleton (A.H 3) → Surjective p.h2)
def LowResStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G),
  (∀ (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P →
    Injective P.h1 ∧ Exact P.h1 (resH1 M.rho N.subtype continuous_subtype_val)) ∧
  ∀ (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
    (∀ x, resH1 M.rho U.subtype continuous_subtype_val x = 0 → U.index • x = 0) ∧
    ∀ x, resH2 M.rho U.subtype continuous_subtype_val x = 0 → U.index • x = 0
def TransgressionStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → ∀ I : Submodule R ((M.resSub N).H 1),
  (∀ x, x ∈ I ↔ ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H 1 x = x) →
  ∃ tg : I →ₗ[R] Q.H 2,
    (∀ (y : M.coch.X 1) (z : Q.coch.X 2) (hz : Q.coch.d 2 z = 0) hy (x : I), M.coch.d 1 y = P.hom.f 2 z →
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy →
      tg x = Q.coch.cls 2 z hz) ∧
    (∀ x : I, ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), ∃ hy, M.coch.d 1 y = P.hom.f 2 z ∧
      x.1 = (M.resSub N).coch.cls 1 ((Pair.res M N.subtype continuous_subtype_val).hom.f 1 y) hy) ∧
    (∀ x : I, tg x = 0 ↔ x.1 ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H 1)) ∧
    Exact tg (P.hom.H 2)
def ChiRkStatement : Prop := ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A B C : Cx R) (N : ℕ),
  (∀ (i : Hom A B) (p : Hom B C), SES i p →
    (A.FinGen N → C.FinGen N → B.FinGen N ∧ B.chiRk N = A.chiRk N + C.chiRk N) ∧
    (B.FinGen N → C.FinGen N → A.FinGen (N + 1) ∧ A.chiRk (N + 1) = B.chiRk N - C.chiRk N) ∧
    (A.FinGen N → B.FinGen N → C.FinGen N ∧ C.chiRk N = B.chiRk N - A.chiRk N)) ∧
  (∀ φ : Hom A B, A.FinGen N → B.FinGen N →
    (fib φ).FinGen (N + 1) ∧ (fib φ).chiRk (N + 1) = A.chiRk N - B.chiRk N) ∧
  (A.FinGen N → B.FinGen N → (prod A B).FinGen N ∧ (prod A B).chiRk N = A.chiRk N + B.chiRk N) ∧
  ∀ (ι : Type u) [Fintype ι] (D : ι → Cx R), (∀ v, (D v).FinGen N) →
    (pi D).FinGen N ∧ (pi D).chiRk N = ∑ v, (D v).chiRk N
def RankLenStatement : Prop := ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (t : R),
  Irreducible t → ∀ (L C : Cx R) (i : Hom L L) (p : Hom L C) (m N : ℕ), (∀ n x, i.f n x = t ^ m • x) → SES i p →
  L.FinGen N → C.FinLen N ∧ C.chi N = m * L.chiRk N ∧ ∀ n,
    (Module.length R (C.H n)).toNat ≤ m * Module.finrank R (L.H n) +
      (Module.length R (Submodule.torsion R (L.H n))).toNat +
      (Module.length R (Submodule.torsion R (L.H (n + 1)))).toNat ∧
    m * Module.finrank R (L.H n) ≤ (Module.length R (C.H n)).toNat
def DivTStatement : Prop := ∀ (R : Type u) [CommRing R] (K D : Cx R) (i : Hom K D) (p : Hom D D) (t : R) δ,
  (∀ n x, p.f n x = t • x) → SES i p → IsConn i p δ → ∀ n,
  (∀ x, x ∈ LinearMap.range (i.H n) ↔ t • x = 0) ∧ (∀ x, δ n x = 0 ↔ ∃ y, x = t • y) ∧
  Exact (δ n) (i.H (n + 1))
def LocaliseStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (t : R) (L V : TRep R G) (j : Pair L V),
  j.φ = MonoidHom.id G → Topology.IsOpenEmbedding j.u → (∃ e : V.V ≃ₜ V.V, ∀ v, e v = t • v) →
  (∀ v : V.V, ∃ m : ℕ, t ^ m • v ∈ LinearMap.range j.u) → ∀ n, IsLocalizedModule (Submonoid.powers t) (j.hom.H n)
def TruncStatement : Prop := ∀ (R : Type u) [CommRing R] (A : Cx R) (L : Submodule R (A.H 1)),
  ∃ (U : Cx R) (j : Hom U A), Bijective (j.H 0) ∧ Injective (j.H 1) ∧ LinearMap.range (j.H 1) = L ∧
    ∀ n, 1 < n → Subsingleton (U.H n)
end
end ReciprocityTheory.Coh


