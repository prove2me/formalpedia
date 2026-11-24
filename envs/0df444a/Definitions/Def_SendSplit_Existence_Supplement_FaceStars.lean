-- Prove2me | Definitions.Def_SendSplit_Existence_Supplement_FaceStars
-- name    : SendSplit_Existence_Supplement_FaceStars
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:46:43.582946+00:00
-- url     : https://prove2.me/theorems/c380d082-161d-455a-b445-06bce40ec90a
-- title:
--   Section 4 — face-star augmentation G″ and its geometric clockwise order
-- statement:
--   For a nonempty face set $D_F$ of a plane embedding, the augmentation adds a fresh point $t$ inside the complementary face and one arc $(v,t)$ for each distinct $v\in D_F$ when $|D_F|\ge2$. Each new arc is simple and continuous; its interior stays in $F$, and distinct new arcs meet only at $t$. Singleton face sets have their unique order and require no added vertex.
--
--   A finite indexed family may contain overlapping face sets. With $T''=\{t:|D^t|\ge2\}$, its graph is
--   $$N''=N\sqcup T'',\qquad A''=A\sqcup\{(v,t):v\in D^t,\ t\in T''\}.$$
--   Compatibility means that distinct new stars have distinct centers and meet only at old shared endpoints. The cover predicate separately expresses that their face sets cover all nonzero-demand vertices.
--
--   Clockwise order is read from the incidences at the new center, using orientation-preserving ambient coordinates: in those coordinates sufficiently short spoke germs are radial, with strictly increasing clockwise angles. A positive coordinate change is specified by an isotopy through homeomorphisms from the identity. This defines the actual topological circular order, independently of every tree and separation conclusion.
--
--   **Formalization Note** The original curves need not have straight endpoint germs. Existence of an augmentation and of clockwise coordinates for every augmentation is stated as a conclusion of the companion theorem, not assumed as an extra regularity premise. Face-boundary repetitions are resolved by the actual chosen incident arcs. This $G''$ is different from the published goal's sink-component augmentation.
-- source:
--   Erickson, Monma and Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Mathematics of Operations Research 12(4) (1987), DOI 10.1287/moor.12.4.634, pp. 645–646, Section 4, augmented graph G″ and clockwise ordering (PDF 13–14)

import Mathlib
import Definitions.Def_SendSplit_Existence_Supplement_PlaneEmbedding
import Definitions.Def_SendSplit_Existence_Supplement_CircularIntervals

set_option autoImplicit false

namespace SendSplit.Existence.Supplement

variable {n : ℕ} {G : ArcGraph n}

/-- One new vertex in a face and one new arc from each distinct demand vertex on
that face. Arc interiors lie in the face; they meet each other only at the new vertex.
The old drawing is retained verbatim. Incident corners are selected by these curves,
so repeated occurrences of a boundary vertex cause no artificial simplicity assumption. -/
structure FaceStar (P : Drawing G) (r : Fin n → ℝ) (F : PlaneFace P) where
  at_least_two : 2 ≤ (faceSet P r F).card
  center : Plane
  center_mem : center ∈ F.region
  spoke : {v // v ∈ faceSet P r F} → unitInterval → Plane
  continuous_spoke : ∀ v, Continuous (spoke v)
  injective_spoke : ∀ v, Function.Injective (spoke v)
  start : ∀ v, spoke v 0 = P.pos v.val
  finish : ∀ v, spoke v 1 = center
  inside_face : ∀ v s, s ≠ 0 → spoke v s ∈ F.region
  disjoint_spokes : ∀ v w s t, v ≠ w → spoke v s = spoke w t → s = 1 ∧ t = 1

/-- The source's rule adds no vertex for a singleton face set. -/
inductive FaceAugmentation (P : Drawing G) (r : Fin n → ℝ) (F : PlaneFace P) where
  | singleton (one : (faceSet P r F).card = 1)
  | star (data : FaceStar P r F)

/-- Positive orientation expressed without differentiability: an ambient homeomorphism
is isotopic to the identity. Continuity of both evaluation maps is required. These are
coordinate changes, not restrictions that the original curves be straight. -/
def IsPositiveChart (h : Plane ≃ₜ Plane) : Prop :=
  ∃ H : unitInterval → Plane ≃ₜ Plane,
    H 0 = Homeomorph.refl Plane ∧ H 1 = h ∧
    Continuous (fun p : unitInterval × Plane => H p.1 p.2) ∧
    Continuous (fun p : unitInterval × Plane => (H p.1).symm p.2)

/-- Unit vector whose angle increases clockwise in the standard oriented plane. -/
noncomputable def clockwiseRay (θ : ℝ) : Plane := ⟨Real.cos θ, -Real.sin θ⟩

/-- Clockwise order around the new vertex. In positive local coordinates the
spoke germs are distinct radial segments with strictly increasing clockwise angles.
Existence of such coordinates for every star is a conclusion of the theorem, not
an input regularity hypothesis. The drawing itself need not have straight germs. -/
def IsClockwiseStarOrder {P : Drawing G} {r : Fin n → ℝ} {F : PlaneFace P}
    (S : FaceStar P r F) (o : CircularOrder (faceSet P r F)) : Prop :=
  ∃ (h : Plane ≃ₜ Plane) (ε : ℝ) (θ : Fin (faceSet P r F).card → ℝ),
    IsPositiveChart h ∧ h S.center = 0 ∧ 0 < ε ∧ StrictMono θ ∧
    (∀ k, 0 ≤ θ k ∧ θ k < 2 * Real.pi) ∧
    ∀ k, (h '' Set.range (S.spoke (o.enum k))) ∩ Metric.ball 0 ε =
      {z | ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < ε ∧ z = ρ • clockwiseRay (θ k)}

/-- Geometric compatibility, with the unique order for a singleton. No tree,
flow, root, separation property or conclusion occurs in this predicate. -/
def IsClockwise {P : Drawing G} {r : Fin n → ℝ} {F : PlaneFace P}
    (U : FaceAugmentation P r F) (o : CircularOrder (faceSet P r F)) : Prop :=
  match U with
  | .singleton _ => True
  | .star S => IsClockwiseStarOrder S o

/-- A finite indexed collection can have overlapping face sets. The added centers
and interiors must be compatible when simultaneously drawn. This is the geometric
G″, distinct from the published sink-component augmentation. The theorem is pointwise
for every face and every star, hence also applies to every member of such a family.
No covering or disjointness condition on the face sets is needed for that conclusion. -/
structure FaceStarFamily (P : Drawing G) (r : Fin n → ℝ) (T : Type) [Fintype T] where
  face : T → PlaneFace P
  augmentation : ∀ t, FaceAugmentation P r (face t)
  distinct_centers : ∀ t u, t ≠ u → ∀ (S : FaceStar P r (face t))
    (R : FaceStar P r (face u)), augmentation t = .star S → augmentation u = .star R →
    S.center ≠ R.center
  cross_disjoint : ∀ t u, t ≠ u → ∀ (S : FaceStar P r (face t))
    (R : FaceStar P r (face u)), augmentation t = .star S → augmentation u = .star R →
    ∀ v w s q, S.spoke v s = R.spoke w q → s = 0 ∧ q = 0

/-- The additional vertices T″ of a finite family. -/
def AddedFaceVertex {P : Drawing G} {r : Fin n → ℝ} {T : Type} [Fintype T]
    (B : FaceStarFamily P r T) := {t : T // 2 ≤ (faceSet P r (B.face t)).card}

/-- N″ = N ⊔ T″, with the new vertices fresh even when labels overlap. -/
abbrev AugmentedVertex {P : Drawing G} {r : Fin n → ℝ} {T : Type} [Fintype T]
    (B : FaceStarFamily P r T) := Fin n ⊕ AddedFaceVertex B

/-- Original arcs and one new arc for each distinct face-set member. -/
abbrev AugmentedArc {P : Drawing G} {r : Fin n → ℝ} {T : Type} [Fintype T]
    (B : FaceStarFamily P r T) :=
  {p // p ∈ G.A} ⊕ (Σ t : AddedFaceVertex B, {v // v ∈ faceSet P r (B.face t.val)})

def augmentedTail {P : Drawing G} {r : Fin n → ℝ} {T : Type} [Fintype T]
    (B : FaceStarFamily P r T) : AugmentedArc B → AugmentedVertex B
  | .inl e => .inl e.val.1
  | .inr e => .inl e.2.val

def augmentedHead {P : Drawing G} {r : Fin n → ℝ} {T : Type} [Fintype T]
    (B : FaceStarFamily P r T) : AugmentedArc B → AugmentedVertex B
  | .inl e => .inl e.val.2
  | .inr e => .inr e.1

/-- The cover condition used in the surrounding algorithmic discussion. Theorem 3
itself is local to each face and does not require a cover. -/
def IsFaceCover {P : Drawing G} {r : Fin n → ℝ} {T : Type} [Fintype T]
    (B : FaceStarFamily P r T) : Prop :=
  ∀ v, r v ≠ 0 → ∃ t, v ∈ faceSet P r (B.face t)

end SendSplit.Existence.Supplement


