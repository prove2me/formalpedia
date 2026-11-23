-- Prove2me | Definitions.Def_DetANN_Thm11_LocalProjection
-- name    : DetANN_Thm11_LocalProjection
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:17:38.197237+00:00
-- url     : https://prove2.me/theorems/8b3669fa-c5bf-4860-bb9d-24e941d7a64b
-- title:
--   Superblock projections and representative-indexed local ANN databases
-- statement:
--   For each walk tuple $v$ of §7.1, this module represents the superblock $\mathcal A_v$ as an actual Euclidean vector rather than only through its squared norm. If $\ell$ is the walk length and $L$ is the repetition count, its dimension is $16^\ell L$; coordinate $(o,r)$ is the $r$th coordinate of the block selected by the walk occurrence $o$. Repeated endpoints and repeated blocks are retained with multiplicity.
--
--   For a padded database $\bar P$, `projectedSet` is the deduplicated set $\{\mathcal A_v\bar P_i:i<n\}$. `localData` enumerates this finite set injectively, as required by the interface of Lemma 3.3. Every local point has a chosen original representative, exposed both for subtype elements (`localRep`) and for local indices (`localRepIdx`). Conversely, `localClass i` is the local index of the projection of the original point $P_i$, so every original point is available for comparison even after deduplication.
--
--   The structural lemmas identify projections of representatives and of original-point classes and prove compatibility with subtraction. No balance, injectivity of the projections, positivity of `annReps`, or nonemptiness of the database is assumed; the definitions remain meaningful in the degenerate cases as well.
--
--   **Formalization Note** The fixed enumeration of walk occurrences uses `Fintype.equivFin`; the construction is noncomputable because representatives and finite enumerations are chosen classically.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §7.1, p.17, especially the definition of the superblock and the projected local databases preceding equation (25). Deduplication and original representatives are the formal interface needed to apply Lemma 3.3, p.7, whose input list is injective.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily
import Definitions.Def_DetANN_Thm11_Split

namespace DetANN
namespace Thm11

/-- Walk occurrences, in the paper's fixed order. -/
abbrev WalkOcc (ε : ℝ) := Fin (walkLen ε) → Fin 16

/-- The projected dimension `16^ℓ · L`. -/
noncomputable def annDim {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) : ℕ :=
  16 ^ walkLen ε * annReps C₀ k P ε

/-- Base-16 enumeration of the walk occurrences. -/
noncomputable def occEquiv (ε : ℝ) : Fin (16 ^ walkLen ε) ≃ WalkOcc ε :=
  (finCongr (by classical simp [WalkOcc])).trans (Fintype.equivFin (WalkOcc ε)).symm

/-- The concatenated superblock projection, with coordinates ordered by walk occurrence and then
by repetition. -/
noncomputable def annProject {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (z : EuclideanSpace ℝ (Fin (2 ^ k))) : EuclideanSpace ℝ (Fin (annDim C₀ k P ε)) :=
  WithLp.toLp 2 fun c =>
    let oc := finProdFinEquiv.symm c
    annBlocks C₀ k P ε (annTuples k ε v (occEquiv ε oc.1)) z oc.2

/-- The projection respects subtraction of input vectors. -/
lemma annProject_sub {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (z w : EuclideanSpace ℝ (Fin (2 ^ k))) :
    annProject C₀ k P ε v (z - w) = annProject C₀ k P ε v z - annProject C₀ k P ε v w := by
  ext c
  change annBlocks C₀ k P ε (annTuples k ε v (occEquiv ε (finProdFinEquiv.symm c).1)) (z - w)
      (finProdFinEquiv.symm c).2 =
    annBlocks C₀ k P ε (annTuples k ε v (occEquiv ε (finProdFinEquiv.symm c).1)) z
      (finProdFinEquiv.symm c).2 -
    annBlocks C₀ k P ε (annTuples k ε v (occEquiv ε (finProdFinEquiv.symm c).1)) w
      (finProdFinEquiv.symm c).2
  rw [map_sub]
  rfl

/-- The deduplicated projected database for one tuple. -/
noncomputable def projectedSet {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k)) :
    Finset (EuclideanSpace ℝ (Fin (annDim C₀ k P ε))) :=
  Finset.univ.image fun i => annProject C₀ k P ε v (padVec (2 ^ k) (P i))

/-- An injective enumeration of the deduplicated projected database. -/
noncomputable def localData {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k)) :
    Fin (projectedSet C₀ k P ε v).card → EuclideanSpace ℝ (Fin (annDim C₀ k P ε)) :=
  fun a => ((Fintype.equivFin _).symm (finCongr (Fintype.card_coe _).symm a)).1

lemma localData_injective {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k)) :
    Function.Injective (localData C₀ k P ε v) := by
  intro a b hab
  apply (finCongr (Fintype.card_coe (projectedSet C₀ k P ε v)).symm).injective
  apply (Fintype.equivFin (projectedSet C₀ k P ε v)).symm.injective
  apply Subtype.ext
  exact hab

/-- A representative original point of each projected point. -/
noncomputable def localRep {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (y : projectedSet C₀ k P ε v) : Fin n :=
  Classical.choose (Finset.mem_image.mp y.2)

lemma annProject_localRep {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (y : projectedSet C₀ k P ε v) :
    annProject C₀ k P ε v (padVec (2 ^ k) (P (localRep C₀ k P ε v y))) = y.1 := by
  exact (Classical.choose_spec (Finset.mem_image.mp y.2)).2

/-- The original representative associated with an index in `localData`. -/
noncomputable def localRepIdx {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (a : Fin (projectedSet C₀ k P ε v).card) : Fin n :=
  localRep C₀ k P ε v ((Fintype.equivFin _).symm (finCongr (Fintype.card_coe _).symm a))

lemma annProject_localRepIdx {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k))
    (a : Fin (projectedSet C₀ k P ε v).card) :
    annProject C₀ k P ε v (padVec (2 ^ k) (P (localRepIdx C₀ k P ε v a))) =
      localData C₀ k P ε v a := by
  exact annProject_localRep C₀ k P ε v
    ((Fintype.equivFin _).symm (finCongr (Fintype.card_coe _).symm a))

/-- The local-database index of the projection of an original point. -/
noncomputable def localClass {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k)) (i : Fin n) :
    Fin (projectedSet C₀ k P ε v).card :=
  finCongr (Fintype.card_coe _) (Fintype.equivFin _
    ⟨annProject C₀ k P ε v (padVec (2 ^ k) (P i)), by simp [projectedSet]⟩)

lemma localData_localClass {d n : ℕ} (C₀ : ℝ) (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : Fin (2 ^ k)) (i : Fin n) :
    localData C₀ k P ε v (localClass C₀ k P ε v i) =
      annProject C₀ k P ε v (padVec (2 ^ k) (P i)) := by
  simp [localData, localClass]

end Thm11
end DetANN


