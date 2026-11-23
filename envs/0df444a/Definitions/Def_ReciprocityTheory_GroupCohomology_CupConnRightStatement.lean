-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
-- name    : ReciprocityTheory_GroupCohomology_CupConnRightStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:48.804468+00:00
-- url     : https://prove2.me/theorems/51c25e83-751e-45fc-9406-2b2fa86cd5fc
-- title:
--   Cup Conn Right Statement
-- statement:
--   Definitions and structural lemmas for Cup Conn Right Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupConnRightStatement.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
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
universe u
def BasicStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (φ : Hom A B) (ψ : Hom B C) (n : ℕ),
  (Hom.id A).H n = LinearMap.id ∧ (ψ.comp φ).H n = (ψ.H n).comp (φ.H n) ∧
  (∀ h : A.H n, ∃ x hx, h = A.cls n x hx) ∧ (∀ x hx, A.cls n x hx = 0 ↔ x ∈ A.B n) ∧
  ∀ x hx, ∃ hy, φ.H n (A.cls n x hx) = B.cls n (φ.f n x) hy
def LESStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (i : Hom A B) (p : Hom B C), SES i p →
  (∃ δ, IsConn i p δ ∧ LES i p δ) ∧ ∀ δ δ', IsConn i p δ → IsConn i p δ' → δ = δ'
def ConnNatStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C A' B' C' : Cx R) (i : Hom A B) (p : Hom B C)
  (i' : Hom A' B') (p' : Hom B' C') (α : Hom A A') (β : Hom B B') (γ : Hom C C') δ δ', SES i p → SES i' p' →
  (∀ n x, β.f n (i.f n x) = i'.f n (α.f n x)) → (∀ n x, γ.f n (p.f n x) = p'.f n (β.f n x)) →
  IsConn i p δ → IsConn i' p' δ' → ∀ n x, δ' n (γ.H n x) = α.H (n + 1) (δ n x)
def FibLESStatement : Prop := ∀ (R : Type u) [CommRing R] (A B : Cx R) (φ : Hom A B),
  ∃ δ, IsFibConn φ δ ∧ Injective ((fibFst φ).H 0) ∧ ∀ n, Exact ((fibFst φ).H n) (φ.H n) ∧
    Exact (φ.H n) (δ n) ∧ Exact (δ n) ((fibFst φ).H (n + 1))
def FibMapStatement : Prop := ∀ (R : Type u) [CommRing R] (A B A' B' : Cx R) (φ : Hom A B) (φ' : Hom A' B')
  (α : Hom A A') (β : Hom B B'), (∀ n x, β.f n (φ.f n x) = φ'.f n (α.f n x)) →
  ∃ γ : Hom (fib φ) (fib φ'), (∀ n x, (γ.f n x).1 = α.f n x.1) ∧
    (∀ n x, (γ.f (n + 1) x).2 = β.f n x.2) ∧ (α.QuasiIso → β.QuasiIso → γ.QuasiIso)
def FibSESStatement : Prop := ∀ (R : Type u) [CommRing R] (A₁ A₂ A₃ B₁ B₂ B₃ : Cx R) (φ₁ : Hom A₁ B₁)
  (φ₂ : Hom A₂ B₂) (φ₃ : Hom A₃ B₃) (i : Hom A₁ A₂) (p : Hom A₂ A₃) (i' : Hom B₁ B₂) (p' : Hom B₂ B₃)
  (γ : Hom (fib φ₁) (fib φ₂)) (γ' : Hom (fib φ₂) (fib φ₃)), SES i p → SES i' p' →
  (∀ n x, (γ.f n x).1 = i.f n x.1) → (∀ n x, (γ.f (n + 1) x).2 = i'.f n x.2) →
  (∀ n x, (γ'.f n x).1 = p.f n x.1) → (∀ n x, (γ'.f (n + 1) x).2 = p'.f n x.2) → SES γ γ'
def KerFibStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (i : Hom A B) (p : Hom B C), SES i p →
  ∃ k : Hom A (fib p), (∀ n x, k.f n x = (i.f n x, 0)) ∧ k.QuasiIso
def ProdStatement : Prop := ∀ (R : Type u) [CommRing R],
  (∀ (A B : Cx R) n, Bijective (((prodFst A B).H n).prod ((prodSnd A B).H n))) ∧
  ∀ (ι : Type u) (A : ι → Cx R) n, Bijective (LinearMap.pi fun v => (piProj A v).H n)
def ChiStatement : Prop := ∀ (R : Type u) [CommRing R] (A B C : Cx R) (N : ℕ),
  (∀ (i : Hom A B) (p : Hom B C), SES i p →
    (A.FinLen N → C.FinLen N → B.FinLen N ∧ B.chi N = A.chi N + C.chi N) ∧
    (B.FinLen N → C.FinLen N → A.FinLen (N + 1) ∧ A.chi (N + 1) = B.chi N - C.chi N) ∧
    (A.FinLen N → B.FinLen N → C.FinLen N ∧ C.chi N = B.chi N - A.chi N)) ∧
  (∀ φ : Hom A B, A.FinLen N → B.FinLen N → (fib φ).FinLen (N + 1) ∧ (fib φ).chi (N + 1) = A.chi N - B.chi N) ∧
  (A.FinLen N → B.FinLen N → (prod A B).FinLen N ∧ (prod A B).chi N = A.chi N + B.chi N) ∧
  ∀ (ι : Type u) [Fintype ι] (D : ι → Cx R), (∀ v, (D v).FinLen N) →
    (pi D).FinLen N ∧ (pi D).chi N = ∑ v, (D v).chi N
def TowerStatement : Prop := ∀ (R : Type u) [CommRing R] (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m))
  (L : Cx R) (π : ∀ m, Hom L (A m)), IsTowerLim A τ L π → ∀ n,
  (∀ y : ∀ m, (A m).H n, (∀ m, (τ m).H n (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).H n x = y m) ∧
  ((∀ k, n = k + 1 → ∀ m, IsArtinian R ((A m).H k)) → ∀ x : L.H n, (∀ m, (π m).H n x = 0) → x = 0)
def LowStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G),
  (∀ n, ∃ e : M.H n ≃ₗ[R] Hn M.rho n, ∀ x hx, ∃ hz : x.1 ∈ Zn M.rho n,
    e (M.coch.cls n x hx) = Submodule.Quotient.mk ⟨x.1, hz⟩) ∧
  (∃ e : M.H 0 ≃ₗ[R] H0 M.rho, ∀ x hx, (e (M.coch.cls 0 x hx) : M.V) = x.1 ![]) ∧
  (∃ e : M.H 1 ≃ₗ[R] H1 M.rho, ∀ x hx, ∃ hz : (fun g => x.1 ![g]) ∈ Z1 M.rho,
    e (M.coch.cls 1 x hx) = Submodule.Quotient.mk ⟨_, hz⟩) ∧
  ∃ e : M.H 2 ≃ₗ[R] H2 M.rho, ∀ x hx, ∃ hz : (fun g : G × G => x.1 ![g.1, g.2]) ∈ Z2 M.rho,
    e (M.coch.cls 2 x hx) = Submodule.Quotient.mk ⟨_, hz⟩
def AdmStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A B C : TRep R G) (i : Pair A B) (p : Pair B C),
  admitted i p → SES i.hom p.hom
def SectionStatement : Prop := ∀ (B C : Type u) [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C] (p : B →+ C), Continuous p → Surjective p →
  (DiscreteTopology C ∨ (CompactSpace B ∧ T2Space B ∧ TotallyDisconnectedSpace B ∧ T2Space C)) →
  ∃ s : C → B, Continuous s ∧ ∀ c, p (s c) = c
def GroupSectionStatement : Prop := ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (U : Subgroup G), IsClosed (U : Set G) →
  ∃ r : G → U, Continuous r ∧ r 1 = 1 ∧ ∀ (x : U) g, r (x * g) = x * r g
def InnerStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (P : Pair M M) (s : G),
  (∀ g, P.φ g = s⁻¹ * g * s) → (∀ m, P.u m = M.rho s m) → ∀ n, P.hom.H n = LinearMap.id
def InvRepStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal],
  ∃ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P
def InfResStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal]
  (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P →
  Injective (P.hom.H 1) ∧ Exact (P.hom.H 1) ((Pair.res M N.subtype continuous_subtype_val).hom.H 1) ∧
  ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) → (∀ m, c.u m = M.rho s m) →
    ∀ n x, c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n x) =
      (Pair.res M N.subtype continuous_subtype_val).hom.H n x
def FiveTermStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (N : Subgroup G) [N.Normal], IsClosed (N : Set G) →
  ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M), IsInvRep M N Q P → ∀ I : Submodule R ((M.resSub N).H 1),
  (∀ x, x ∈ I ↔ ∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H 1 x = x) →
  ∃ tg : I →ₗ[R] Q.H 2, (∀ x : I, tg x = 0 ↔
      x.1 ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H 1)) ∧ Exact tg (P.hom.H 2)
def CorStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
  ∃ cor, IsCor M U cor ∧ ∀ n x,
    cor.H n ((Pair.res M U.subtype continuous_subtype_val).hom.H n x) = U.index • x
def ResInjStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (U : Subgroup G) [U.FiniteIndex], IsOpen (U : Set G) →
  IsUnit (U.index : R) → ∀ n, Injective ((Pair.res M U.subtype continuous_subtype_val).hom.H n)
def ResNormalStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (N : Subgroup G) [N.Normal] [N.FiniteIndex],
  IsOpen (N : Set G) → IsUnit (N.index : R) → ∀ n (x : (M.resSub N).H n),
  (∀ (s : G) (c : Pair (M.resSub N) (M.resSub N)), (∀ g, (c.φ g : G) = s⁻¹ * g * s) →
    (∀ m, c.u m = M.rho s m) → c.hom.H n x = x) →
  x ∈ LinearMap.range ((Pair.res M N.subtype continuous_subtype_val).hom.H n)
def CupStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (b : Pairing M N P),
  (∀ p q f f' (g : Fin (p + q + 1) → G), dn P.rho (p + q) (cupFun b p q f f') g =
    cupFun b (p + 1) q (dn M.rho p f) f' (fun i => g (i.cast (by omega))) +
      (-1 : R) ^ p • cupFun b p (q + 1) f (dn N.rho q f') g) ∧
  (∃ cup, IsCup b cup) ∧ ∀ cup cup', IsCup b cup → IsCup b cup' → cup = cup'
def CupNatStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  (M N P : TRep R G) (M' N' P' : TRep R G') (b : Pairing M N P) (b' : Pairing M' N' P')
  (a₁ : Pair M M') (a₂ : Pair N N') (a₃ : Pair P P') cup cup', a₂.φ = a₁.φ → a₃.φ = a₁.φ →
  (∀ m n, a₃.u (b.β m n) = b'.β (a₁.u m) (a₂.u n)) → IsCup b cup → IsCup b' cup' →
  ∀ p q x y, a₃.hom.H (p + q) (cup p q x y) = cup' p q (a₁.hom.H p x) (a₂.hom.H q y)
def CupConnRightStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N₁ N₂ N₃ P₁ P₂ P₃ : TRep R G) (i : Pair N₁ N₂) (p : Pair N₂ N₃)
  (i' : Pair P₁ P₂) (p' : Pair P₂ P₃) (b₁ : Pairing M N₁ P₁) (b₂ : Pairing M N₂ P₂) (b₃ : Pairing M N₃ P₃)
  δ δ' c₁ c₃, admitted i p → admitted i' p' → (∀ m n, i'.u (b₁.β m n) = b₂.β m (i.u n)) →
  (∀ m n, p'.u (b₂.β m n) = b₃.β m (p.u n)) → IsConn i.hom p.hom δ → IsConn i'.hom p'.hom δ' →
  IsCup b₁ c₁ → IsCup b₃ c₃ → ∀ r q x y, δ' (r + q) (c₃ r q x y) = (-1 : R) ^ r • c₁ r (q + 1) x (δ q y)
def CupConnLeftStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M₁ M₂ M₃ N P₁ P₂ P₃ : TRep R G) (i : Pair M₁ M₂) (p : Pair M₂ M₃)
  (i' : Pair P₁ P₂) (p' : Pair P₂ P₃) (b₁ : Pairing M₁ N P₁) (b₂ : Pairing M₂ N P₂) (b₃ : Pairing M₃ N P₃)
  δ δ' c₁ c₃, admitted i p → admitted i' p' → (∀ m n, i'.u (b₁.β m n) = b₂.β (i.u m) n) →
  (∀ m n, p'.u (b₂.β m n) = b₃.β (p.u m) n) → IsConn i.hom p.hom δ → IsConn i'.hom p'.hom δ' →
  IsCup b₁ c₁ → IsCup b₃ c₃ → ∀ r q x y,
    δ' (r + q) (c₃ r q x y) = P₁.cast (by omega) (c₁ (r + 1) q (δ r x) y)
def CupAdjStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A B C A' B' C' P : TRep R G) (i : Pair A B) (p : Pair B C)
  (i' : Pair C' B') (p' : Pair B' A') (bA : Pairing A A' P) (bB : Pairing B B' P) (bC : Pairing C C' P)
  δ δ' cA cC, admitted i p → admitted i' p' → (∀ a b', bB.β (i.u a) b' = bA.β a (p'.u b')) →
  (∀ b c', bB.β b (i'.u c') = bC.β (p.u b) c') → IsConn i.hom p.hom δ → IsConn i'.hom p'.hom δ' →
  IsCup bA cA → IsCup bC cC → ∀ r q x y,
    P.cast (show r + 1 + q = r + (q + 1) by omega) (cA (r + 1) q (δ r x) y) +
      (-1 : R) ^ r • cC r (q + 1) x (δ' q y) = 0
def CupCommStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (b : Pairing M N P) (b' : Pairing N M P) cup cup',
  (∀ m n, b'.β n m = b.β m n) → IsCup b cup → IsCup b' cup' →
  ∀ p q x y, cup p q x y = (-1 : R) ^ (p * q) • P.cast (by omega) (cup' q p y x)
def CupCorStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M N P : TRep R G) (U : Subgroup G) [U.FiniteIndex] (b : Pairing M N P)
  (bU : Pairing (M.resSub U) (N.resSub U) (P.resSub U)) cup cupU corM corP, IsOpen (U : Set G) →
  bU.β = b.β → IsCup b cup → IsCup bU cupU → IsCor M U corM → IsCor P U corP → ∀ p q x y,
    corP.H (p + q) (cupU p q x ((Pair.res N U.subtype continuous_subtype_val).hom.H q y)) =
      cup p q (corM.H p x) y
def CoindStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (U : Subgroup G) (M : TRep R U),
  ∃ (C : TRep R G) (ev : Pair C M), IsCoind U M C ev
def ShapiroStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (U : Subgroup G) (M : TRep R U) (C : TRep R G)
  (ev : Pair C M), IsCoind U M C ev → (∃ r : G → U, Continuous r ∧ ∀ (x : U) g, r (x * g) = x * r g) →
  ev.hom.QuasiIso
def LimRepStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : ℕ → TRep R G) [∀ m, DiscreteTopology (A m).V]
  (τ : ∀ m, Pair (A (m + 1)) (A m)) (L : TRep R G) (π : ∀ m, Pair L (A m)),
  (∀ m, (τ m).φ = MonoidHom.id G ∧ (π m).φ = MonoidHom.id G ∧ Surjective (τ m).u ∧
    ∀ x, (τ m).u ((π (m + 1)).u x) = (π m).u x) →
  Topology.IsEmbedding (fun (x : L.V) m => (π m).u x) →
  (∀ y : ∀ m, (A m).V, (∀ m, (τ m).u (y (m + 1)) = y m) → ∃ x, ∀ m, (π m).u x = y m) →
  IsTowerLim (fun m => (A m).coch) (fun m => (τ m).hom) L.coch fun m => (π m).hom
def ColimStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (ι : Type u) [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  (A : ι → TRep R G) (L : TRep R G) [DiscreteTopology L.V] [∀ a, DiscreteTopology (A a).V]
  (j : ∀ a, Pair (A a) L) (t : ∀ a b, a ≤ b → Pair (A a) (A b)),
  (∀ a, (j a).φ = MonoidHom.id G ∧ Injective (j a).u) →
  (∀ a b h, (t a b h).φ = MonoidHom.id G ∧ ∀ x, (j b).u ((t a b h).u x) = (j a).u x) →
  (∀ x, ∃ a, x ∈ LinearMap.range (j a).u) → ∀ n,
  (∀ x : L.H n, ∃ a y, (j a).hom.H n y = x) ∧
  ∀ a (y : (A a).H n), (j a).hom.H n y = 0 → ∃ b h, (t a b h).hom.H n y = 0
def FiniteLevelStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (M : TRep R G) [DiscreteTopology M.V] (n : ℕ) (x : M.H n),
  (∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
    IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n)) ∧ (0 < n → ∃ k : ℕ, 0 < k ∧ k • x = 0)
def ModTStatement : Prop := ∀ (R : Type u) [CommRing R] (A C : Cx R) (i : Hom A A) (p : Hom A C) (t : R) δ,
  (∀ n x, i.f n x = t • x) → SES i p → IsConn i p δ → ∀ n,
  (∀ x, p.H n x = 0 ↔ ∃ y, x = t • y) ∧ Exact (p.H n) (δ n) ∧ ∀ x, x ∈ LinearMap.range (δ n) ↔ t • x = 0
def FinGenStatement : Prop := ∀ (R : Type u) [CommRing R] (t : R) [IsAdicComplete (Ideal.span {t}) R]
  (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m)),
  IsTowerLim A τ L π → (∀ n (x : L.X n), t • x = 0 → x = 0) →
  (∀ m n (x : L.X n), (π m).f n x = 0 ↔ ∃ y, x = t ^ (m + 1) • y) →
  (∀ n, IsFiniteLength R ((A 0).H n)) → ∀ n, Module.Finite R (L.H n) ∧ ∀ m, IsFiniteLength R ((A m).H n)
def SelStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (ι : Type u) (S : SelData M ι) (n : ℕ),
  ∃ δ : (pi S.loc).H n →ₗ[R] S.cx.H (n + 1), Exact (S.diff.H n) δ ∧
    LinearMap.range (S.toGlob.H n) = S.sel n ∧
    ((∀ v, Injective ((S.j v).H (n + 1))) → Exact δ (S.toGlob.H (n + 1)))
def SelChiStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (ι : Type u) [Fintype ι] (S : SelData M ι) (N : ℕ),
  M.coch.FinLen N → (∀ v, (S.U v).FinLen N) → (∀ v, (S.loc v).FinLen N) →
  S.cx.FinLen (N + 1) ∧ S.cx.chi (N + 1) = M.coch.chi N + ∑ v, ((S.U v).chi N - (S.loc v).chi N)
def SelQuotStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G) (ι : Type u) (S : SelData M ι) (W : ι → Cx R)
  (q : ∀ v, Hom (S.loc v) (W v)) (ψ : Hom M.coch (pi W)), (∀ v, SES (S.j v) (q v)) →
  (∀ n x v, ψ.f n x v = (q v).f n ((S.locHom v).f n x)) →
  ∃ γ : Hom S.cx (fib ψ), (∀ n x, (γ.f n x).1 = x.1.1) ∧ γ.QuasiIso
end ReciprocityTheory.Coh


