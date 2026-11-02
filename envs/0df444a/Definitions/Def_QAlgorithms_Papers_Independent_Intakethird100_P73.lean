-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P73
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P73
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T10:01:00.8505+00:00
-- url     : https://prove2.me/theorems/7e8b2b38-6362-4df9-afee-03e5d9fc4c90
-- title:
--   Definitions for Simplicial principal bundles in parametrized spaces
-- statement:
--   The objects the formalized statements of *Simplicial principal bundles in parametrized spaces* (arXiv:1203.2460) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `KSpace`: A k-space, without a separation axiom (PDF p. 2).
--   - `kify`: Kification, using the final topology for all compact Hausdorff probes (PDF p. 4, all products and limits are in K).
--   - `kifyProjection`: The identity map from the kification to the original space.
--   - `kifyProbe`: A compact Hausdorff probe is continuous into the kification by its definition.
--   - `kifyMap`: Kification of a continuous map; neither topology is silently discarded.
--   - `IsWeaklyHausdorff`: Weak Hausdorffness means that every compact Hausdorff probe has closed image (PDF p. 2). This does not require Hausdorffness.
--   - `SpaceOver`: An object of K/B (PDF p. 2).
--   - `MapOver`: A continuous map over the fixed base (PDF p. 2).
--   - `identityOver`: Identity morphism over B.
--   - `composeOver`: Composition of morphisms over B, in functional order.
--   - `FiberProductSet`: The underlying set of a fiber product, with its ordinary subspace topology only as the input to kification. It is not used as the categorical product.
--   - `fiberProductOver`: The actual fiber product over B with k-space topology (PDF pp. 4--5).
--   - `fiberProductSetMap`: The map of underlying pullback subspaces induced by two maps over B.
--   - `fiberProductMap`: Product of two given maps, with both pullback topologies kified. This is the product map, not the pushout-product (PDF p. 20).
--   - `FiberwiseHomotopic`: Fiberwise homotopy: a continuous homotopy on the kified tensor X times I, with both endpoints specified and the projection fixed for every time (PDF pp. 4--5).
--   - `IsFEquivalence`: An f-equivalence has an inverse over B and two fiberwise homotopies, not merely homotopy equivalences on separate fibers (PDF p. 5).
--   - `IsFFibration`: The fiberwise covering homotopy property, for every test object in K/B (PDF p. 5). The entire lift is over B.
--   - `IsStrongFCofibration`: Strong fbar-cofibrations have the LLP against all f-acyclic f-fibrations in K/B. Neither f-cofibrations nor NDR representations are substituted for this definition (PDF p. 5).
--   - `fiberPair`: A point of the kified fiber product, retaining the common-base equation.
--   - `ParametrizedGroup`: A group object in K/B, with continuous unit, multiplication, and inverse and all group axioms on each common fiber (PDF pp. 2, 5--6).
--   - `EquivariantSpace`: A continuous right action over B; its domain is a kified fiber product, not the Cartesian product of possibly different fibers (PDF p. 6).
--   - `EquivariantMap`: A G-equivariant map over B (PDF p. 6).
--   - `equivariantIdentity`: Identity G-map.
--   - `equivariantCompose`: Composite G-map in functional order.
--   - `EquivariantCylinderMap`: A G-map X tensor I to Y. Equivariance is required at every time, with G acting trivially on I, and the homotopy stays over B (PDF pp. 6--7).
--   - `EquivariantlyHomotopic`: Homotopy through G-maps over B with the specified endpoints (PDF p. 7).
--   - `IsEquivariantFEquivalence`: An equivariant f-equivalence includes an equivariant inverse and both homotopies over B (PDF p. 7).
--   - `IsEquivariantFFibration`: The equivariant covering homotopy property for every G-space over B (PDF p. 7).
--   - `IsEquivariantStrongFCofibration`: The LLP in G K/B against all equivariant f-acyclic f-fibrations (PDF p. 7). This is stronger than a condition only on underlying maps.
--   - `IsEquivariantFiberwiseNDR`: The source's right-equivariant fiberwise NDR condition (PDF pp. 5, 7). The zero set is exactly A, A is fixed for all times, and only u(x) < 1 requires the terminal homotopy value to lie in A.
--   - `GroupMapOver`: A continuous homomorphism of parametrized groups (PDF pp. 2, 8). Preservation of inverses follows from these group homomorphism axioms.
--   - `SimplicialParametrizedGroup`: A simplicial parametrized group is contravariant functor data on the whole simplex category, taking every arrow to a continuous homomorphism. The identity and composition equations specify the full simplicial object; levels are not arbitrary unrelated groups (PDF p. 2).
--   - `constantSimplicialGroup`: The constant simplicial parametrized group, for a sanity check.
--   - `baseOver`: The terminal object B→B, which is the domain of the identity section.
--   - `groupUnitSection`: The canonical identity section as a map over B (PDF pp. 5--6).
--   - `IsWellSectioned`: Well-sectionedness is the strong cofibration property of the canonical identity section, not an arbitrary supplied section (Definition 6, PDF p. 6).
--   - `IsGoodSimplicialGroup`: Goodness requires every degeneracy in every degree to be a strong fbar-cofibration (Definition 20, PDF p. 12).
-- source:
--   Simplicial principal bundles in parametrized spaces, arXiv:1203.2460v4, https://arxiv.org/abs/1203.2460v4

import Mathlib

/-!
Local definitions for Roberts--Stevenson, arXiv:1203.2460v4, PDF pp. 2, 4--5, 20.
Products below have the compactly generated topology. No weak Hausdorff
condition is imposed on total spaces. The other planned nodes are explicitly
deferred in this paper's HARD.md and GAPS.json, rather than weakened.
-/

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P73

open CategoryTheory

open scoped Topology

/-- A k-space, without a separation axiom (PDF p. 2). -/
structure KSpace where
  Carrier : Type u
  topology : TopologicalSpace Carrier
  generated : @CompactlyGeneratedSpace Carrier topology

/-- Use the carrier of the bundled k-space, without changing its topology. -/
instance kSpaceCoeSort : CoeSort KSpace.{u} (Type u) := ⟨KSpace.Carrier⟩

/-- Recover exactly the topology stored in the bundled k-space. -/
instance kSpaceTopology (X : KSpace.{u}) : TopologicalSpace X := X.topology

/-- Recover the compact-generation witness for that same stored topology. -/
instance kSpaceCompactlyGenerated (X : KSpace.{u}) : CompactlyGeneratedSpace X := X.generated

/-- Kification, using the final topology for all compact Hausdorff probes
(PDF p. 4, all products and limits are in K). -/
def kify (X : Type u) [TopologicalSpace X] : KSpace where
  Carrier := X
  topology := TopologicalSpace.compactlyGenerated.{u} X
  generated := by
    let T := Σ i : (S : CompHaus.{u}) × C(S, X), i.fst
    let q : T → X := fun z => z.1.2 z.2
    letI : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u} X
    exact uCompactlyGeneratedSpace_of_coinduced (f := q) continuous_coinduced_rng rfl

/-- The identity map from the kification to the original space. -/
def kifyProjection (X : Type u) [tX : TopologicalSpace X] : C(kify X, X) where
  toFun := id
  continuous_toFun := by
    change Continuous[TopologicalSpace.compactlyGenerated.{u} X, tX] (id : X → X)
    exact @continuous_from_compactlyGenerated.{u, u, u} X X tX tX id
      (fun _ g => g.continuous)

/-- A compact Hausdorff probe is continuous into the kification by its definition. -/
def kifyProbe {X : Type u} [TopologicalSpace X] (S : CompHaus.{u})
    (f : C(S, X)) : C(S, kify X) where
  toFun := f
  continuous_toFun := by
    change Continuous[inferInstance, TopologicalSpace.coinduced
      (fun z : (Σ i : (T : CompHaus.{u}) × C(T, X), i.fst) => z.1.2 z.2)
      inferInstance] (f : S → X)
    let T := Σ i : (U : CompHaus.{u}) × C(U, X), i.fst
    let q : T → X := fun z => z.1.2 z.2
    let j : S → T := fun s => ⟨⟨S, f⟩, s⟩
    have hj : Continuous j := continuous_sigmaMk
      (σ := fun i : (U : CompHaus.{u}) × C(U, X) => (i.fst : Type u))
      (i := (⟨S, f⟩ : (U : CompHaus.{u}) × C(U, X)))
    exact @Continuous.comp S T X inferInstance inferInstance
      (TopologicalSpace.coinduced q inferInstance) j q
      (continuous_coinduced_rng (f := q) (t := inferInstance)) hj

/-- Kification of a continuous map; neither topology is silently discarded. -/
def kifyMap {X Y : Type u} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : C(X, Y)) : C(kify X, kify Y) where
  toFun := f
  continuous_toFun := by
    change Continuous[TopologicalSpace.compactlyGenerated.{u} X,
      TopologicalSpace.compactlyGenerated.{u} Y] (f : X → Y)
    exact @continuous_from_compactlyGenerated.{u, u, u} X Y tX
      (TopologicalSpace.compactlyGenerated.{u} Y) (f : X → Y)
      (fun S g => (kifyProbe S (f.comp g)).continuous)

/-- Weak Hausdorffness means that every compact Hausdorff probe has closed image
(PDF p. 2). This does not require Hausdorffness. -/
def IsWeaklyHausdorff (B : KSpace.{u}) : Prop :=
  ∀ (S : CompHaus.{u}) (f : C(S, B)), IsClosed (Set.range f)

/-- An object of K/B (PDF p. 2). -/
structure SpaceOver (B : KSpace.{u}) where
  space : KSpace.{u}
  projection : C(space, B)

/-- A continuous map over the fixed base (PDF p. 2). -/
structure MapOver {B : KSpace} (X Y : SpaceOver B) where
  map : C(X.space, Y.space)
  over_base : ∀ x, Y.projection (map x) = X.projection x

/-- Identity morphism over B. -/
def identityOver {B : KSpace} (X : SpaceOver B) : MapOver X X where
  map := ContinuousMap.id X.space
  over_base := fun _ => rfl

/-- Composition of morphisms over B, in functional order. -/
def composeOver {B : KSpace} {X Y Z : SpaceOver B}
    (g : MapOver Y Z) (f : MapOver X Y) : MapOver X Z where
  map := g.map.comp f.map
  over_base := fun x => (g.over_base (f.map x)).trans (f.over_base x)

/-- The underlying set of a fiber product, with its ordinary subspace topology
only as the input to kification. It is not used as the categorical product. -/
abbrev FiberProductSet {B : KSpace} (X Y : SpaceOver B) :=
  {z : X.space × Y.space // X.projection z.1 = Y.projection z.2}

/-- The actual fiber product over B with k-space topology (PDF pp. 4--5). -/
def fiberProductOver {B : KSpace} (X Y : SpaceOver B) : SpaceOver B where
  space := kify (FiberProductSet X Y)
  projection :=
    (⟨fun z : FiberProductSet X Y => X.projection z.val.1, by fun_prop⟩ :
      C(FiberProductSet X Y, B)).comp (kifyProjection (FiberProductSet X Y))

/-- The map of underlying pullback subspaces induced by two maps over B. -/
def fiberProductSetMap {B : KSpace} {A X D Y : SpaceOver B}
    (f : MapOver A X) (g : MapOver D Y) :
    C(FiberProductSet A D, FiberProductSet X Y) where
  toFun := fun z => ⟨(f.map z.val.1, g.map z.val.2),
    (f.over_base z.val.1).trans (z.property.trans (g.over_base z.val.2).symm)⟩
  continuous_toFun := by fun_prop

/-- Product of two given maps, with both pullback topologies kified.
This is the product map, not the pushout-product (PDF p. 20). -/
def fiberProductMap {B : KSpace} {A X D Y : SpaceOver B}
    (f : MapOver A X) (g : MapOver D Y) :
    MapOver (fiberProductOver A D) (fiberProductOver X Y) where
  map := kifyMap (fiberProductSetMap f g)
  over_base := fun z => f.over_base z.val.1

/-- Fiberwise homotopy: a continuous homotopy on the kified tensor X times I,
with both endpoints specified and the projection fixed for every time
(PDF pp. 4--5). -/
def FiberwiseHomotopic {B : KSpace} {X Y : SpaceOver B}
    (f g : MapOver X Y) : Prop :=
  ∃ H : C(kify (X.space × unitInterval), Y.space),
    (∀ x, H (x, 0) = f.map x) ∧
    (∀ x, H (x, 1) = g.map x) ∧
    ∀ x t, Y.projection (H (x, t)) = X.projection x

/-- An f-equivalence has an inverse over B and two fiberwise homotopies,
not merely homotopy equivalences on separate fibers (PDF p. 5). -/
def IsFEquivalence {B : KSpace} {X Y : SpaceOver B} (f : MapOver X Y) : Prop :=
  ∃ g : MapOver Y X,
    FiberwiseHomotopic (composeOver g f) (identityOver X) ∧
    FiberwiseHomotopic (composeOver f g) (identityOver Y)

/-- The fiberwise covering homotopy property, for every test object in K/B
(PDF p. 5). The entire lift is over B. -/
def IsFFibration {B : KSpace} {X Y : SpaceOver B} (p : MapOver X Y) : Prop :=
  ∀ (Z : SpaceOver B) (a : MapOver Z X)
    (H : C(kify (Z.space × unitInterval), Y.space)),
    (∀ z t, Y.projection (H (z, t)) = Z.projection z) →
    (∀ z, H (z, 0) = p.map (a.map z)) →
    ∃ L : C(kify (Z.space × unitInterval), X.space),
      (∀ z t, X.projection (L (z, t)) = Z.projection z) ∧
      (∀ z, L (z, 0) = a.map z) ∧
      ∀ z t, p.map (L (z, t)) = H (z, t)

/-- Strong fbar-cofibrations have the LLP against all f-acyclic f-fibrations
in K/B. Neither f-cofibrations nor NDR representations are substituted for
this definition (PDF p. 5). -/
def IsStrongFCofibration {B : KSpace} {A X : SpaceOver B} (i : MapOver A X) : Prop :=
  ∀ (U V : SpaceOver B) (p : MapOver U V),
    IsFFibration p → IsFEquivalence p →
    ∀ (a : MapOver A U) (b : MapOver X V),
      (∀ z, p.map (a.map z) = b.map (i.map z)) →
      ∃ l : MapOver X U,
        (∀ z, l.map (i.map z) = a.map z) ∧
        ∀ x, p.map (l.map x) = b.map x

/-- Sanity: identity maps have the stated lifting property. -/
example {B : KSpace} (X : SpaceOver B) :
    IsStrongFCofibration (identityOver X) := by
  intro U V p hp he a b h
  exact ⟨a, fun _ => rfl, h⟩

/-- Sanity: the product map acts on both coordinates, with no union or
pushout-product hidden in its definition. -/
example {B : KSpace} {A X D Y : SpaceOver B} (f : MapOver A X) (g : MapOver D Y)
    (z : (fiberProductOver A D).space) :
    ((fiberProductMap f g).map z).val = (f.map z.val.1, g.map z.val.2) := by
  rfl

/-- A point of the kified fiber product, retaining the common-base equation. -/
def fiberPair {B : KSpace} {X Y : SpaceOver B} (x : X.space) (y : Y.space)
    (h : X.projection x = Y.projection y) : (fiberProductOver X Y).space :=
  ⟨(x, y), h⟩

/-- A group object in K/B, with continuous unit, multiplication, and inverse
and all group axioms on each common fiber (PDF pp. 2, 5--6). -/
structure ParametrizedGroup (B : KSpace) where
  total : SpaceOver B
  unit : C(B, total.space)
  unit_over : ∀ b, total.projection (unit b) = b
  multiply : MapOver (fiberProductOver total total) total
  inverse : MapOver total total
  left_unit : ∀ g, multiply.map
    (fiberPair (unit (total.projection g)) g (unit_over _)) = g
  right_unit : ∀ g, multiply.map
    (fiberPair g (unit (total.projection g)) (unit_over _).symm) = g
  left_inverse : ∀ g, multiply.map
    (fiberPair (inverse.map g) g (inverse.over_base g)) = unit (total.projection g)
  right_inverse : ∀ g, multiply.map
    (fiberPair g (inverse.map g) (inverse.over_base g).symm) = unit (total.projection g)
  associative : ∀ g h k (hgh : total.projection g = total.projection h)
    (hhk : total.projection h = total.projection k),
    multiply.map (fiberPair (multiply.map (fiberPair g h hgh)) k
      ((multiply.over_base (fiberPair g h hgh)).trans (hgh.trans hhk))) =
    multiply.map (fiberPair g (multiply.map (fiberPair h k hhk))
      (hgh.trans (multiply.over_base (fiberPair h k hhk)).symm))

/-- Sanity: every base admits the trivial parametrized group, whose fibers
are singletons. This also covers the empty base. -/
example (B : KSpace) : Nonempty (ParametrizedGroup B) := by
  let T : SpaceOver B := ⟨B, ContinuousMap.id B⟩
  let m : MapOver (fiberProductOver T T) T :=
    { map := (⟨fun z : FiberProductSet T T => z.val.1, by fun_prop⟩ :
        C(FiberProductSet T T, B)).comp (kifyProjection (FiberProductSet T T))
      over_base := fun _ => rfl }
  exact ⟨{ total := T
           unit := ContinuousMap.id B
           unit_over := fun _ => rfl
           multiply := m
           inverse := identityOver T
           left_unit := fun _ => rfl
           right_unit := fun _ => rfl
           left_inverse := fun _ => rfl
           right_inverse := fun _ => rfl
           associative := fun _ _ _ _ _ => rfl }⟩

/-- A continuous right action over B; its domain is a kified fiber product,
not the Cartesian product of possibly different fibers (PDF p. 6). -/
structure EquivariantSpace {B : KSpace} (G : ParametrizedGroup B) where
  total : SpaceOver B
  action : MapOver (fiberProductOver total G.total) total
  action_unit : ∀ x, action.map
    (fiberPair x (G.unit (total.projection x)) (G.unit_over _).symm) = x
  action_multiply : ∀ x g h (hxg : total.projection x = G.total.projection g)
    (hgh : G.total.projection g = G.total.projection h),
    action.map (fiberPair (action.map (fiberPair x g hxg)) h
      ((action.over_base (fiberPair x g hxg)).trans (hxg.trans hgh))) =
    action.map (fiberPair x (G.multiply.map (fiberPair g h hgh))
      (hxg.trans (G.multiply.over_base (fiberPair g h hgh)).symm))

/-- A G-equivariant map over B (PDF p. 6). -/
structure EquivariantMap {B : KSpace} {G : ParametrizedGroup B}
    (X Y : EquivariantSpace G) where
  map : MapOver X.total Y.total
  equivariant : ∀ x g (h : X.total.projection x = G.total.projection g),
    map.map (X.action.map (fiberPair x g h)) =
    Y.action.map (fiberPair (map.map x) g ((map.over_base x).trans h))

/-- Identity G-map. -/
def equivariantIdentity {B : KSpace} {G : ParametrizedGroup B}
    (X : EquivariantSpace G) : EquivariantMap X X where
  map := identityOver X.total
  equivariant := fun _ _ _ => rfl

/-- Composite G-map in functional order. -/
def equivariantCompose {B : KSpace} {G : ParametrizedGroup B}
    {X Y Z : EquivariantSpace G} (g : EquivariantMap Y Z) (f : EquivariantMap X Y) :
    EquivariantMap X Z where
  map := composeOver g.map f.map
  equivariant := by
    intro x a h
    change g.map.map (f.map.map (X.action.map (fiberPair x a h))) = _
    rw [f.equivariant, g.equivariant]
    rfl

/-- A G-map X tensor I to Y. Equivariance is required at every time,
with G acting trivially on I, and the homotopy stays over B (PDF pp. 6--7). -/
structure EquivariantCylinderMap {B : KSpace} {G : ParametrizedGroup B}
    (X Y : EquivariantSpace G) where
  map : C(kify (X.total.space × unitInterval), Y.total.space)
  over_base : ∀ x t, Y.total.projection (map (x, t)) = X.total.projection x
  equivariant : ∀ x g (h : X.total.projection x = G.total.projection g) t,
    map (X.action.map (fiberPair x g h), t) =
    Y.action.map (fiberPair (map (x, t)) g ((over_base x t).trans h))

/-- Homotopy through G-maps over B with the specified endpoints (PDF p. 7). -/
def EquivariantlyHomotopic {B : KSpace} {G : ParametrizedGroup B}
    {X Y : EquivariantSpace G} (f g : EquivariantMap X Y) : Prop :=
  ∃ H : EquivariantCylinderMap X Y,
    (∀ x, H.map (x, 0) = f.map.map x) ∧
    ∀ x, H.map (x, 1) = g.map.map x

/-- An equivariant f-equivalence includes an equivariant inverse and both
homotopies over B (PDF p. 7). -/
def IsEquivariantFEquivalence {B : KSpace} {G : ParametrizedGroup B}
    {X Y : EquivariantSpace G} (f : EquivariantMap X Y) : Prop :=
  ∃ g : EquivariantMap Y X,
    EquivariantlyHomotopic (equivariantCompose g f) (equivariantIdentity X) ∧
    EquivariantlyHomotopic (equivariantCompose f g) (equivariantIdentity Y)

/-- The equivariant covering homotopy property for every G-space over B
(PDF p. 7). -/
def IsEquivariantFFibration {B : KSpace} {G : ParametrizedGroup B}
    {X Y : EquivariantSpace G} (p : EquivariantMap X Y) : Prop :=
  ∀ (Z : EquivariantSpace G) (a : EquivariantMap Z X)
    (H : EquivariantCylinderMap Z Y),
    (∀ z, H.map (z, 0) = p.map.map (a.map.map z)) →
    ∃ L : EquivariantCylinderMap Z X,
      (∀ z, L.map (z, 0) = a.map.map z) ∧
      ∀ z t, p.map.map (L.map (z, t)) = H.map (z, t)

/-- The LLP in G K/B against all equivariant f-acyclic f-fibrations
(PDF p. 7). This is stronger than a condition only on underlying maps. -/
def IsEquivariantStrongFCofibration {B : KSpace} {G : ParametrizedGroup B}
    {A X : EquivariantSpace G} (i : EquivariantMap A X) : Prop :=
  ∀ (U V : EquivariantSpace G) (p : EquivariantMap U V),
    IsEquivariantFFibration p → IsEquivariantFEquivalence p →
    ∀ (a : EquivariantMap A U) (b : EquivariantMap X V),
      (∀ z, p.map.map (a.map.map z) = b.map.map (i.map.map z)) →
      ∃ l : EquivariantMap X U,
        (∀ z, l.map.map (i.map.map z) = a.map.map z) ∧
        ∀ x, p.map.map (l.map.map x) = b.map.map x

/-- The source's right-equivariant fiberwise NDR condition (PDF pp. 5, 7).
The zero set is exactly A, A is fixed for all times, and only u(x) < 1
requires the terminal homotopy value to lie in A. -/
def IsEquivariantFiberwiseNDR {B : KSpace} {G : ParametrizedGroup B}
    (X : EquivariantSpace G) (A : Set X.total.space) : Prop :=
  ∃ u : C(X.total.space, unitInterval),
    ∃ H : EquivariantCylinderMap X X,
      (∀ x, x ∈ A ↔ u x = 0) ∧
      (∀ x, H.map (x, 0) = x) ∧
      (∀ x ∈ A, ∀ t, H.map (x, t) = x) ∧
      (∀ x, (u x : ℝ) < 1 → H.map (x, 1) ∈ A) ∧
      ∀ x g (h : X.total.projection x = G.total.projection g),
        u (X.action.map (fiberPair x g h)) = u x

/-- Sanity: the identity G-map satisfies the equivariant LLP. -/
example {B : KSpace} {G : ParametrizedGroup B} (X : EquivariantSpace G) :
    IsEquivariantStrongFCofibration (equivariantIdentity X) := by
  intro U V p hp he a b h
  exact ⟨a, fun _ => rfl, h⟩

/-- Sanity: the whole space is an NDR subspace, using u = 0 and the
constant-in-time equivariant fiberwise homotopy. -/
example {B : KSpace} {G : ParametrizedGroup B} (X : EquivariantSpace G) :
    IsEquivariantFiberwiseNDR X Set.univ := by
  let H : EquivariantCylinderMap X X :=
    { map := ContinuousMap.fst.comp (kifyProjection (X.total.space × unitInterval))
      over_base := fun _ _ => rfl
      equivariant := fun _ _ _ _ => rfl }
  refine ⟨ContinuousMap.const _ 0, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x
    rfl
  · intro x hx t
    rfl
  · intro x hx
    trivial
  · intro x g h
    rfl

/-- A continuous homomorphism of parametrized groups (PDF pp. 2, 8).
Preservation of inverses follows from these group homomorphism axioms. -/
structure GroupMapOver {B : KSpace} (G H : ParametrizedGroup B) where
  map : MapOver G.total H.total
  unit_preserved : ∀ b, map.map (G.unit b) = H.unit b
  multiply_preserved : ∀ g h (e : G.total.projection g = G.total.projection h),
    map.map (G.multiply.map (fiberPair g h e)) =
    H.multiply.map (fiberPair (map.map g) (map.map h)
      ((map.over_base g).trans (e.trans (map.over_base h).symm)))

/-- A simplicial parametrized group is contravariant functor data on the
whole simplex category, taking every arrow to a continuous homomorphism.
The identity and composition equations specify the full simplicial object;
levels are not arbitrary unrelated groups (PDF p. 2). -/
structure SimplicialParametrizedGroup (B : KSpace) where
  obj : SimplexCategoryᵒᵖ → ParametrizedGroup B
  map : ∀ {a b : SimplexCategoryᵒᵖ}, (a ⟶ b) → GroupMapOver (obj a) (obj b)
  map_identity : ∀ (a : SimplexCategoryᵒᵖ) (x : (obj a).total.space),
    (map (𝟙 a)).map.map x = x
  map_composition : ∀ {a b c : SimplexCategoryᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (x : (obj a).total.space),
    (map (f ≫ g)).map.map x =
      (map g).map.map ((map f).map.map x)

/-- The constant simplicial parametrized group, for a sanity check. -/
def constantSimplicialGroup {B : KSpace} (G : ParametrizedGroup B) :
    SimplicialParametrizedGroup B where
  obj := fun _ => G
  map := fun _ =>
    { map := identityOver G.total
      unit_preserved := fun _ => rfl
      multiply_preserved := fun _ _ _ => rfl }
  map_identity := fun _ _ => rfl
  map_composition := fun _ _ _ => rfl

/-- The terminal object B→B, which is the domain of the identity section. -/
def baseOver (B : KSpace) : SpaceOver B := ⟨B, ContinuousMap.id B⟩

/-- The canonical identity section as a map over B (PDF pp. 5--6). -/
def groupUnitSection {B : KSpace} (G : ParametrizedGroup B) :
    MapOver (baseOver B) G.total where
  map := G.unit
  over_base := G.unit_over

/-- Well-sectionedness is the strong cofibration property of the canonical
identity section, not an arbitrary supplied section (Definition 6, PDF p. 6). -/
def IsWellSectioned {B : KSpace} (G : ParametrizedGroup B) : Prop :=
  IsStrongFCofibration (groupUnitSection G)

/-- Goodness requires every degeneracy in every degree to be a strong
fbar-cofibration (Definition 20, PDF p. 12). -/
def IsGoodSimplicialGroup {B : KSpace} (G : SimplicialParametrizedGroup B) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 1)),
    IsStrongFCofibration ((G.map (SimplexCategory.σ i).op).map)

/-- Sanity: every degeneracy of the constant simplicial group is exactly
the identity on the given group, including degree zero. -/
example {B : KSpace} (G : ParametrizedGroup B) (n : ℕ) (i : Fin (n + 1))
    (x : G.total.space) :
    (((constantSimplicialGroup G).map (SimplexCategory.σ i).op).map.map x) = x := by
  rfl

end QAlgorithms.Papers.Independent.Intakethird100.P73


