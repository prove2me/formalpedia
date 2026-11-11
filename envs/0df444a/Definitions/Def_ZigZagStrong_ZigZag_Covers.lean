-- Prove2me | Definitions.Def_ZigZagStrong_ZigZag_Covers
-- name    : ZigZagStrong_ZigZag_Covers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:20.31818+00:00
-- url     : https://prove2.me/theorems/00c59ba0-9700-48a5-8bde-e86609d62717
-- title:
--   Port graphs, the rooted truncation and return-walk series
-- statement:
--   A port graph is an involutive rotation on port–vertex pairs. Its zig-zag adjacency counts every zig and zag incidence. Oriented edges retain the middle port and both gadget-incidence indices; reversal swaps the zig and zag incidences and reverses the rotation. This also retains the two orientations of an ordinary loop. The canonical tree uses the free product of $d$ copies of $\mathbb Z_2$.
--
--   The rooted truncation retains a chosen initial gadget incidence, removes competing root incidences and competing edges across the corresponding two-cloud cut, and takes the reachable root component. Its adjacency is constructed from the infinite adjacency by a finite-rank deletion correction and compression to the closed span of that component. A walk carries a separate index for every parallel edge occurrence. If $s_\ell$ and $c_\ell$ are the first-return and all-return counts, define
--   $$S_X(z)=\sum_{\ell\ge1}s_\ell z^\ell,\qquad C_X(z)=\sum_{\ell\ge0}c_\ell z^\ell.$$
--   Radii and coefficient growth use extended nonnegative reals, preserving infinite radii. No growth value or spectral identity is assumed by the construction.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Appendix A, pp. 27–29; CCM24, ECCC TR24-089, §5.1.1, printed pp. 24–27 (PDF pp. 26–29).

import Definitions.Def_ZigZagStrong_ZigZag_Models

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open scoped BigOperators

/-- Arbitrary port labelings, including those not arising from group actions. -/
structure PortGraph (d : ℕ) (V : Type*) where
  rot : Equiv.Perm (Fin d × V)
  involutive : Function.Involutive rot

def PortGraph.base {d : ℕ} {V : Type*} (G : PortGraph d V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ i j, G.rot (i,x) = (j,y)
  symm := ⟨by
    intro x y h
    obtain ⟨i,j,hij⟩ := h.2
    refine ⟨h.1.symm, j, i, ?_⟩
    rw [← hij, G.involutive]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A port-labeled simple d-regular tree; infinitude is required where it is used. -/
def PortGraph.IsTree {d : ℕ} {V : Type*} (G : PortGraph d V) : Prop :=
  G.base.IsTree ∧ (∀ x i, (G.rot (i,x)).2 ≠ x) ∧
    ∀ x i j, (G.rot (i,x)).2 = (G.rot (j,x)).2 → i = j

/-- The full multiplicity of zig-zag paths, without collapsing parallel paths. -/
def zigzagKernel {d c : ℕ} {V : Type*} (H : Gadget d c) (G : PortGraph d V)
    (x y : Fin d × V) : ℕ := by
  classical
  exact ∑ t : Fin d, if (G.rot (t,x.2)).2 = y.2
    then H.edges x.1 t * H.edges (G.rot (t,x.2)).1 y.1 else 0

/-- An oriented zig-zag edge retains both gadget incidences and the middle port.
In particular, reversing a loop need not fix its incidence. -/
structure ZigzagPath {d c : ℕ} {V : Type*} (H : Gadget d c) (G : PortGraph d V)
    (x y : Fin d × V) where
  middle : Fin d
  vertex_eq : (G.rot (middle, x.2)).2 = y.2
  zig : Fin (H.edges x.1 middle)
  zag : Fin (H.edges (G.rot (middle, x.2)).1 y.1)

/-- Reverse the actual three-step path, swapping its zig and zag incidences. -/
def reverseZigzagPath {d c : ℕ} {V : Type*} {H : Gadget d c} {G : PortGraph d V}
    {x y : Fin d × V} (p : ZigzagPath H G x y) : ZigzagPath H G y x := by
  have hs (i j : Fin d) : H.edges i j = H.edges j i :=
    congrArg (fun A : Matrix (Fin d) (Fin d) ℕ => A j i) H.symmetric.eq
  have hr : G.rot ((G.rot (p.middle, x.2)).1, y.2) = (p.middle, x.2) := by
    rw [← p.vertex_eq]
    exact G.involutive _
  refine ⟨(G.rot (p.middle, x.2)).1, by simpa using congrArg (fun z : Fin d × V => z.2) hr,
    ⟨p.zag.val, ?_⟩, ⟨p.zig.val, ?_⟩⟩
  · simpa only [hs y.1] using p.zag.isLt
  · simpa only [hr, hs p.middle] using p.zig.isLt

def matchingKernel {d c : ℕ} (H : Gadget d c)
    (x y : Fin d × FreeInvolutions d) : ℕ := by
  classical
  exact ∑ t : Fin d, if involutionGenerator t * x.2 = y.2
    then H.edges x.1 t * H.edges t y.1 else 0

/-- CCM24 §5.1.1: one chosen initial incidence; all competing root incidences
and all competing edges across its tree-cloud cut are deleted. -/
def truncatedKernel {d c : ℕ} (H : Gadget d c) (a t : Fin d)
    (x y : Fin d × FreeInvolutions d) : ℕ := by
  classical
  let o : Fin d × FreeInvolutions d := (a,1)
  let u := involutionGenerator t
  exact if x = o then (if y.2 = u then H.edges t y.1 else 0)
    else if y = o then (if x.2 = u then H.edges t x.1 else 0)
    else if (x.2 = 1 ∧ y.2 = u) ∨ (y.2 = 1 ∧ x.2 = u) then 0
    else matchingKernel H x y

def truncationVertices {d c : ℕ} (H : Gadget d c) (a t : Fin d) :
    Set (Fin d × FreeInvolutions d) :=
  {x | Relation.ReflTransGen (fun x y => 0 < truncatedKernel H a t x y) (a,1) x}

abbrev TreeClouds (d : ℕ) := Clouds d (L2 (FreeInvolutions d))

def cloudDelta {d : ℕ} (x : Fin d × FreeInvolutions d) : TreeClouds d :=
  PiLp.single 2 x.1 (lp.single 2 x.2 (1 : ℂ))

def cloudCoord {d : ℕ} (x : Fin d × FreeInvolutions d) : TreeClouds d →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : FreeInvolutions d => ℂ) 2 x.2).comp
    (PiLp.proj 2 (fun _ : Fin d => L2 (FreeInvolutions d)) x.1)

/-- Only vertices in these finitely many clouds meet a changed edge. -/
def changedVertices (d : ℕ) : Finset (Fin d × FreeInvolutions d) := by
  classical
  exact Finset.univ.product (insert 1 (Finset.univ.image involutionGenerator))

/-- The actual full adjacency plus its finite-rank edge-deletion correction. -/
def deletedAdj {d c : ℕ} (H : Gadget d c) (a t : Fin d) : TreeClouds d →L[ℂ] TreeClouds d :=
  matchingLimit H + ∑ x ∈ changedVertices d, ∑ y ∈ changedVertices d,
    ((truncatedKernel H a t x y : ℂ) - (matchingKernel H x y : ℂ)) •
      (cloudCoord y).smulRight (cloudDelta x)

def truncationSpace {d c : ℕ} (H : Gadget d c) (a t : Fin d) : Submodule ℂ (TreeClouds d) :=
  (Submodule.span ℂ (cloudDelta '' truncationVertices H a t)).topologicalClosure

instance {d c : ℕ} (H : Gadget d c) (a t : Fin d) : CompleteSpace (truncationSpace H a t) :=
  by unfold truncationSpace; infer_instance

/-- Adjacency compressed to the root component, on its genuine closed ℓ² subspace. -/
def truncatedAdj {d c : ℕ} (H : Gadget d c) (a t : Fin d) :=
  (truncationSpace H a t).orthogonalProjectionOnto.comp
    ((deletedAdj H a t).comp (truncationSpace H a t).subtypeL)

/-- A walk carries one index for each occurrence of a parallel adjacency edge. -/
def Walks {d c : ℕ} (H : Gadget d c) (a t : Fin d) (ℓ : ℕ) :=
  {v : Fin (ℓ+1) → Fin d × FreeInvolutions d // v 0 = (a,1) ∧ v (Fin.last ℓ) = (a,1)}

def walkMultiplicity {d c : ℕ} (H : Gadget d c) (a t : Fin d) {ℓ : ℕ}
    (v : Walks H a t ℓ) : ℕ :=
  ∏ i : Fin ℓ, truncatedKernel H a t (v.val i.castSucc) (v.val i.succ)

def closedCount {d c : ℕ} (H : Gadget d c) (a t : Fin d) (ℓ : ℕ) : ℕ :=
  Nat.card (Σ v : Walks H a t ℓ, Fin (walkMultiplicity H a t v))

def firstReturnCount {d c : ℕ} (H : Gadget d c) (a t : Fin d) (ℓ : ℕ) : ℕ :=
  Nat.card (Σ v : {v : Walks H a t ℓ // 0 < ℓ ∧
    ∀ i : Fin (ℓ+1), 0 < i.val → i.val < ℓ → v.val i ≠ (a,1)},
    Fin (walkMultiplicity H a t v.val))

/-- Radius in the extended nonnegative reals, so the everywhere-convergent series has radius ∞. -/
def seriesRadius (a : ℕ → ℕ) : ENNReal :=
  ⨆ r : {r : ℝ // 0 ≤ r ∧ Summable (fun n => (a n : ℝ) * r ^ n)}, ENNReal.ofReal r.val

def walkGrowth (a : ℕ → ℕ) : ENNReal :=
  Filter.limsup (fun n : ℕ => (a n : ENNReal) ^ ((n : ℝ)⁻¹)) Filter.atTop
end ZigZagStrong.ZigZag


