-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P44
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P44
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:51:12.407873+00:00
-- url     : https://prove2.me/theorems/9280c8a0-8bb2-4590-b332-cdf18c34d465
-- title:
--   Definitions for Equivalences of Smooth and Continuous Principal Bundles with Infinite-Dimensional Structure Group
-- statement:
--   The objects the formalized statements of *Equivalences of Smooth and Continuous Principal Bundles with Infinite-Dimensional Structure Group* (arXiv:math/0604142) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Quadrant`: The positive quadrant with its subspace topology (Remark I.6, PDF p. 4).
--   - `QuadrantSmoothOn`: Local smooth extension into the ambient finite-dimensional real vector space, as required by Remark I.6, PDF p. 4. Only values on `s` constrain the extension.
--   - `CornerAtlas`: A finite-dimensional smooth corner atlas, including precisely Hausdorffness and paracompactness; no global second-countability condition (Remark I.6, PDF p. 4). The transition domain is relative to the quadrant. Maximalizing this atlas gives its usual smooth structure; no ambient embedding of `M` is required.
--   - `PrincipalAtlas`: Principal-bundle data with specified local trivializations (Definition I.1, PDF p. 2). The action is on the right. Inverse-coordinate formulas express projection compatibility and equivariance without a choice of local sections.
--   - `ContinuousCocycle`: Continuous normalized transition functions on their actual overlaps, with the printed triple-product cocycle law (Remark I.2, PDF p. 3).
--   - `CocycleRepresentative`: The disjoint union of local products, with the sum of their product topologies (Remark I.2, PDF p. 3).
--   - `CocycleRelation`: The source identification: `(i,x,a)` and `(j,x,b)` are related exactly when `k_ji(x) * a = b` (Remark I.2, PDF p. 3).
--   - `CocycleTotal`: The actual quotient of local products (Remark I.2, PDF p. 3). `Quot` takes the equivalence closure of the displayed relation; normalization and the cocycle law make that relation itself an equivalence relation.
--   - `cocycleProjection`: The projection `[i,x,k] ↦ x`, computed from the quotient (Remark I.2, PDF p. 3).
--   - `cocycleRightAction`: Right multiplication `[i,x,k] · b = [i,x,k*b]`, computed on representatives (Remark I.2, PDF p. 3).
--   - `canonicalBundleMap`: The canonical map from an existing bundle chooses a chart containing its base point and then takes `[i,Omega_i(p)]` (Remark I.2, PDF p. 3). Its independence of this choice is part of the reconstruction theorem.
-- source:
--   Equivalences of Smooth and Continuous Principal Bundles with Infinite-Dimensional Structure Group, arXiv:math/0604142v3, https://arxiv.org/abs/math/0604142v3

import Mathlib

/-!
Statements from Müller–Wockel, arXiv:math/0604142v3.
The locally convex smooth results are explicitly deferred in the unit's HARD.md.
The definitions below are paper-local and contain no assumed smoothing results.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P44

open Set
open scoped ContDiff

/-- The positive quadrant with its subspace topology (Remark I.6, PDF p. 4). -/
abbrev Quadrant (d : ℕ) := {x : Fin d → ℝ // ∀ i, 0 ≤ x i}

/-- Local smooth extension into the ambient finite-dimensional real vector space,
as required by Remark I.6, PDF p. 4. Only values on `s` constrain the extension. -/
def QuadrantSmoothOn {d e : ℕ} (f : Quadrant d → Quadrant e)
    (s : Set (Quadrant d)) : Prop :=
  ∀ x ∈ s, ∃ v : Set (Fin d → ℝ), IsOpen v ∧ x.val ∈ v ∧
    ∃ g : (Fin d → ℝ) → (Fin e → ℝ), ContDiffOn ℝ ∞ g v ∧
      ∀ y ∈ s, y.val ∈ v → g y.val = (f y).val

/-- A finite-dimensional smooth corner atlas, including precisely Hausdorffness and
paracompactness; no global second-countability condition (Remark I.6, PDF p. 4).
The transition domain is relative to the quadrant. Maximalizing this atlas gives
its usual smooth structure; no ambient embedding of `M` is required. -/
structure CornerAtlas (d : ℕ) (M : Type*) [TopologicalSpace M] where
  hausdorff : T2Space M
  paracompact : ParacompactSpace M
  charts : Set (OpenPartialHomeomorph M (Quadrant d))
  covers : ∀ x : M, ∃ c ∈ charts, x ∈ c.source
  compatible : ∀ c ∈ charts, ∀ b ∈ charts,
    QuadrantSmoothOn (fun x => b (c.symm x)) (c.target ∩ c.symm ⁻¹' b.source)

/-- Identity coordinate changes have the required extension, including in dimension
zero. This sanity check uses the ambient identity, rather than a derivative condition
imposed on an empty interior (Remark I.6, PDF p. 4). -/
example (d : ℕ) : QuadrantSmoothOn (fun x : Quadrant d => x) Set.univ := by
  intro x hx
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, id, contDiff_id.contDiffOn,
    fun _ _ _ => rfl⟩

/-- The dimension-zero quadrant is the one-point real coordinate space. -/
example (x y : Quadrant 0) : x = y := by
  apply Subtype.ext
  exact funext fun i => Fin.elim0 i

/-- Principal-bundle data with specified local trivializations (Definition I.1,
PDF p. 2). The action is on the right. Inverse-coordinate formulas express
projection compatibility and equivariance without a choice of local sections. -/
structure PrincipalAtlas {M K P I : Type*} [TopologicalSpace M]
    [TopologicalSpace K] [Group K] [TopologicalSpace P]
    (eta : P → M) (act : P → K → P) (u : I → Set M) where
  open_sets : ∀ i, IsOpen (u i)
  covers : ∀ x, ∃ i, x ∈ u i
  projection_continuous : Continuous eta
  action_continuous : Continuous (fun z : P × K => act z.1 z.2)
  action_one : ∀ p, act p 1 = p
  action_mul : ∀ p a b, act (act p a) b = act p (a * b)
  projection_action : ∀ p a, eta (act p a) = eta p
  trivialization : ∀ i, {p : P // eta p ∈ u i} ≃ₜ (u i × K)
  inverse_base : ∀ i (x : u i) a,
    eta ((trivialization i).symm (x, a)).val = x.val
  inverse_action : ∀ i (x : u i) a b,
    act ((trivialization i).symm (x, a)).val b =
      ((trivialization i).symm (x, a * b)).val

/-- Continuous normalized transition functions on their actual overlaps,
with the printed triple-product cocycle law (Remark I.2, PDF p. 3). -/
structure ContinuousCocycle {M K I : Type*} [TopologicalSpace M]
    [TopologicalSpace K] [Group K] (u : I → Set M) where
  open_sets : ∀ i, IsOpen (u i)
  covers : ∀ x, ∃ i, x ∈ u i
  transition : ∀ i j, {x : M // x ∈ u i ∩ u j} → K
  transition_continuous : ∀ i j, Continuous (transition i j)
  normalized : ∀ i (x : u i), transition i i ⟨x.val, x.property, x.property⟩ = 1
  cocycle : ∀ i j n (x : M) (hi : x ∈ u i) (hj : x ∈ u j) (hn : x ∈ u n),
    transition i j ⟨x, hi, hj⟩ * transition j n ⟨x, hj, hn⟩ *
      transition n i ⟨x, hn, hi⟩ = 1

/-- The disjoint union of local products, with the sum of their product topologies
(Remark I.2, PDF p. 3). -/
abbrev CocycleRepresentative {M K I : Type*} (u : I → Set M) := Σ i, u i × K

/-- The source identification: `(i,x,a)` and `(j,x,b)` are related exactly when
`k_ji(x) * a = b` (Remark I.2, PDF p. 3). -/
def CocycleRelation {M K I : Type*} [TopologicalSpace M] [TopologicalSpace K]
    [Group K] {u : I → Set M} (c : ContinuousCocycle (K := K) u)
    (a b : CocycleRepresentative (K := K) u) : Prop :=
  ∃ x : M, ∃ hi : x ∈ u a.1, ∃ hj : x ∈ u b.1,
    a.2.1.val = x ∧ b.2.1.val = x ∧
      c.transition b.1 a.1 ⟨x, hj, hi⟩ * a.2.2 = b.2.2

/-- The actual quotient of local products (Remark I.2, PDF p. 3).
`Quot` takes the equivalence closure of the displayed relation; normalization and
the cocycle law make that relation itself an equivalence relation. -/
abbrev CocycleTotal {M K I : Type*} [TopologicalSpace M] [TopologicalSpace K]
    [Group K] {u : I → Set M} (c : ContinuousCocycle (K := K) u) :=
  Quot (CocycleRelation c)

/-- The quotient topology, rather than a freely chosen topology on the quotient
(Remark I.2, PDF p. 3). -/
instance cocycleTotalTopology {M K I : Type*} [TopologicalSpace M]
    [TopologicalSpace K] [Group K] {u : I → Set M}
    (c : ContinuousCocycle (K := K) u) : TopologicalSpace (CocycleTotal c) :=
  TopologicalSpace.coinduced (Quot.mk (CocycleRelation c))
    (inferInstance : TopologicalSpace (CocycleRepresentative (K := K) u))

/-- The projection `[i,x,k] ↦ x`, computed from the quotient (Remark I.2, PDF p. 3). -/
def cocycleProjection {M K I : Type*} [TopologicalSpace M] [TopologicalSpace K]
    [Group K] {u : I → Set M} (c : ContinuousCocycle (K := K) u) : CocycleTotal c → M :=
  Quot.lift (fun a => a.2.1.val) (by
    intro a b h
    rcases h with ⟨x, hi, hj, ha, hb, hk⟩
    exact ha.trans hb.symm)

/-- Right multiplication `[i,x,k] · b = [i,x,k*b]`, computed on representatives
(Remark I.2, PDF p. 3). -/
def cocycleRightAction {M K I : Type*} [TopologicalSpace M] [TopologicalSpace K]
    [Group K] {u : I → Set M} (c : ContinuousCocycle (K := K) u)
    (q : CocycleTotal c) (k : K) : CocycleTotal c :=
  Quot.map (fun a : CocycleRepresentative (K := K) u =>
    ⟨a.1, a.2.1, a.2.2 * k⟩) (by
      intro a b h
      rcases h with ⟨x, hi, hj, ha, hb, hk⟩
      refine ⟨x, hi, hj, ha, hb, ?_⟩
      simpa only [mul_assoc] using congrArg (fun z : K => z * k) hk) q

/-- The canonical map from an existing bundle chooses a chart containing its base
point and then takes `[i,Omega_i(p)]` (Remark I.2, PDF p. 3). Its independence of
this choice is part of the reconstruction theorem. -/
def canonicalBundleMap {M K P I : Type*} [TopologicalSpace M]
    [TopologicalSpace K] [Group K] [TopologicalSpace P] {u : I → Set M}
    {eta : P → M} {act : P → K → P} (c : ContinuousCocycle (K := K) u)
    (a : PrincipalAtlas eta act u) (p : P) : CocycleTotal c :=
  let i := (a.covers (eta p)).choose
  Quot.mk (CocycleRelation c) ⟨i, a.trivialization i ⟨p, (a.covers (eta p)).choose_spec⟩⟩

/-- Equal-chart representatives really are identified, by normalization. This also
pins the multiplication order in the quotient (Remark I.2, PDF p. 3). -/
example {M K I : Type*} [TopologicalSpace M] [TopologicalSpace K] [Group K]
    {u : I → Set M} (c : ContinuousCocycle (K := K) u) (i : I) (x : u i) (k : K) :
    CocycleRelation c ⟨i, x, k⟩ ⟨i, x, k⟩ := by
  refine ⟨x.val, x.property, x.property, rfl, rfl, ?_⟩
  exact (congrArg (fun z : K => z * k) (c.normalized i x)).trans (one_mul k)

/-- The quotient projection has its specified value on every representative. -/
example {M K I : Type*} [TopologicalSpace M] [TopologicalSpace K] [Group K]
    {u : I → Set M} (c : ContinuousCocycle (K := K) u) (a : CocycleRepresentative (K := K) u) :
    cocycleProjection c (Quot.mk (CocycleRelation c) a) = a.2.1.val := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P44


