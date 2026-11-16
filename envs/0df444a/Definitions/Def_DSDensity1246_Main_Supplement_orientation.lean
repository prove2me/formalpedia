-- Prove2me | Definitions.Def_DSDensity1246_Main_Supplement_orientation
-- name    : DSDensity1246_Main_Supplement_orientation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:22:32.086197+00:00
-- url     : https://prove2.me/theorems/0f350b95-7faf-4645-ba53-6dfd0401bddc
-- title:
--   List orientations and vertex outdegrees
-- statement:
--   Let W be an arbitrary class of words of length n over a label space Y, and let ℓ be a natural number. Each edge of the published one-inclusion hypergraph retains its direction and assignment off that direction. An ℓ-list orientation selects a finite subset σ(e) of each edge, with
--
--   $$\sigma(e)\subseteq e,\qquad |\sigma(e)|\le\ell.$$
--
--   The outdegree of a vertex w is the number of directions whose incident edge does not select w. This count is at most n even if W or Y is infinite. Neither the orientation structure nor its capacity condition assumes any density or dimension bound.
--
--   **Formalization Note** Directions use Fin n and vertices are members of W. Empty selections are allowed, as in the source's at-most-ℓ convention; when n=0 every vertex has outdegree zero.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), pp. 17–18, §5.1.1; pp. 45–46, Lemma A.1

import Definitions.Def_DSDensity1246_Main_oneInclusion

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- §5.1.1, pp.17–18: each indexed edge selects at most ℓ incident vertices.
No bound on outdegree is included in the data. -/
structure ListOrientation {Y : Type*} {n : ℕ} (ℓ : ℕ) (W : Set (Fin n → Y)) where
  selected : OneInclusionEdge W → Finset (Fin n → Y)
  incident : ∀ e, (↑(selected e) : Set (Fin n → Y)) ⊆ edge W e.1 e.2.1
  capacity : ∀ e, (selected e).card ≤ ℓ

/-- The unique edge in direction i incident to w. Direction indices are retained. -/
def incidentEdge {Y : Type*} {n : ℕ} {W : Set (Fin n → Y)}
    (w : W) (i : Fin n) : OneInclusionEdge W :=
  ⟨i, away i w.1, ⟨w.1, w.2, rfl⟩⟩

/-- Number of incident edges which do not select w. This is finite even for infinite W. -/
noncomputable def listOutdegree {Y : Type*} {n ℓ : ℕ} {W : Set (Fin n → Y)}
    (σ : ListOrientation ℓ W) (w : W) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => w.1 ∉ σ.selected (incidentEdge w i))).card

end DSDensity1246.Main.Supplement


