-- Prove2me | Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
-- name    : QAlgorithms_Defs_SchurWeylDecomposition
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:42:16.677567+00:00
-- url     : https://prove2.me/theorems/148e39dc-e5ca-41d5-9580-d8fb6f946734
-- title:
--   SchurWeylDecomposition
-- statement:
--   SchurWeylDecomposition
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SchurWeylDecomposition.lean

import Definitions.Def_QAlgorithms_Defs_SchurModules
import Definitions.Def_QAlgorithms_Defs_SchurCharacters
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix

namespace QAlgorithms.Schur

attribute [local instance] Classical.propDecidable

/-- Occupied cell coordinates are below the number of boxes, by up-left
closure (1508.01907 p.4, Young diagrams). -/
theorem partition_cell_bound {d n : ℕ} (lambda : Partition d n)
    {i j : ℕ} (h : (i,j) ∈ lambda.val) : i < n ∧ j < n := by
  have hi : i+1 ≤ lambda.val.cells.card := by
    have hs : (Finset.range (i+1)).image (fun k => (k,j)) ⊆ lambda.val.cells := by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      exact lambda.val.up_left_mem (by simpa using Finset.mem_range.mp hk) le_rfl h
    have hb := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
      Finset.card_range] at hb
    exact hb
  have hj : j+1 ≤ lambda.val.cells.card := by
    have hs : (Finset.range (j+1)).image (fun k => (i,k)) ⊆ lambda.val.cells := by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      exact lambda.val.up_left_mem le_rfl (by simpa using Finset.mem_range.mp hk) h
    have hb := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
      Finset.card_range] at hb
    exact hb
  change i+1 ≤ lambda.val.card at hi
  change j+1 ≤ lambda.val.card at hj
  rw [lambda.property.1] at hi hj
  omega

/-- Finite enumeration of exactly the size-n, height-bounded public shapes
(1508.01907 pp.4,6). -/
instance partitionFinite (d n : ℕ) : Finite (Partition d n) := by
  let encode : Partition d n → Finset (Fin n × Fin n) := fun lambda =>
    Finset.univ.filter fun c => (c.1.val,c.2.val) ∈ lambda.val
  apply Finite.of_injective encode
  intro lambda mu he
  apply Subtype.ext
  apply YoungDiagram.ext
  apply Finset.ext
  intro c
  constructor
  · intro hc
    have hb := partition_cell_bound lambda hc
    have hm : (⟨c.1,hb.1⟩,⟨c.2,hb.2⟩) ∈ encode lambda := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩
    rw [he] at hm
    simpa [encode] using hm
  · intro hc
    have hb := partition_cell_bound mu hc
    have hm : (⟨c.1,hb.1⟩,⟨c.2,hb.2⟩) ∈ encode mu := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩
    rw [← he] at hm
    simpa [encode] using hm

/-- Finite shape basis for weak Schur sampling (1508.01907 pp.4,6). -/
instance partitionFintype (d n : ℕ) : Fintype (Partition d n) := Fintype.ofFinite _

/-- Discrete measurable shapes, alongside Borel unitary outcomes
(1508.01907 pp.6-7). -/
instance partitionMeasurable (d n : ℕ) : MeasurableSpace (Partition d n) := ⊤

/-- All singleton shape events are measurable (1508.01907 pp.6-7). -/
instance partitionMeasurableSingleton (d n : ℕ) :
    MeasurableSingletonClass (Partition d n) := ⟨fun _ => trivial⟩

/-- Orthogonal projection onto the regular Young left ideal, written on the
permutation basis (1508.01797 pp.4-5, Specht factor). -/
def spechtProjection {d n : ℕ} (lambda : Partition d n) :
    Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  Matrix.of fun g h => inner ℂ (ket g) ((spechtSpace lambda).starProjection (ket h))

/-- Character of the computed Specht action. Extending the action by zero on the
orthogonal complement lets its trace be taken in the regular basis
(1508.01797 pp.4-5, P_lambda). -/
def spechtCharacter {d n : ℕ} (lambda : Partition d n) (pi : Equiv.Perm (Fin n)) : ℂ :=
  (leftRegular pi * spechtProjection lambda).trace

/-- The full lambda-isotypic central character idempotent for the tensor
permutation action: dim(Sp_lambda)/n! times the character-weighted group sum
(1508.01797 pp.4-6; 1508.01907 pp.4-6). Unlike a single tensor Young image,
this includes all copies of Sp_lambda. Projector, orthogonality and completeness
identities remain supporting representation-theoretic verification. -/
def isotypicProjector {d n : ℕ} (lambda : Partition d n) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ((Module.finrank ℂ (spechtSpace lambda) : ℂ)/(n.factorial : ℂ)) •
    ∑ pi : Equiv.Perm (Fin n), spechtCharacter lambda pi⁻¹ • tensorPermutation d n pi

/-- On one tensor factor, the Specht ideal is the whole one-dimensional regular
space, so its orthogonal projection is identity (1508.01797 pp.4-5). -/
example {d : ℕ} (lambda : Partition d 1) : spechtProjection lambda = 1 := by
  have hs : spechtSpace lambda = ⊤ := by
    rw [spechtSpace,youngRightOperator_one]
    simp
  ext g h
  simp [spechtProjection,hs,Submodule.starProjection_top,ket,Matrix.one_apply,EuclideanSpace.inner_single_left]


/-- Public coordinates for the direct sum of Specht tensor Schur factors,
with Specht first (1508.01907 p.4). -/
abbrev DecompositionIndex (d n : ℕ) :=
  (lambda : Partition d n) ×
    (Fin (Module.finrank ℂ (spechtSpace lambda)) ×
      Fin (Module.finrank ℂ (schurModule lambda)))

/-- Young-ideal evaluation intertwiner: a regular-group vector s in Sp_lambda
acts on v in the tensor Young image by sum_g s_g P_g v. Public orthonormal
bases are fixed before rho (1508.01907 p.4; 1508.01797 pp.4-5). -/
def youngSynthesis (d n : ℕ) :
    Matrix (Fin n → Fin d) (DecompositionIndex d n) ℂ :=
  Matrix.of fun x index =>
    ∑ g : Equiv.Perm (Fin n),
      ((stdOrthonormalBasis ℂ (spechtSpace index.1) index.2.1).val g) *
        act (tensorPermutation d n g)
          (stdOrthonormalBasis ℂ (schurModule index.1) index.2.2).val x

/-- Public Schur-Weyl transform, as the matrix of the unitary equivalence
from tensor space to the Specht-first direct sum in orthonormal coordinates.
Polar normalization of the Young evaluation intertwiner removes the
nonorthogonal symmetrizer scale; inverse square root acts on the full Gram
operator. No state or certified decomposition is supplied. Unitarity and
both intertwining identities remain supporting verification statements
(1508.01907 p.4). -/
def decomposition (d n : ℕ) :
    Matrix (DecompositionIndex d n) (Fin n → Fin d) ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹)
    ((youngSynthesis d n)ᴴ * youngSynthesis d n) * (youngSynthesis d n)ᴴ

/-- At one copy, Young evaluation reduces to the defining Schur vector
times the single Specht coordinate; there is no tensor permutation left.
Polar normalization then removes only that one-dimensional Specht basis
phase (1508.01907 p.4, one-box case). -/
example {d : ℕ} (lambda : Partition d 1)
    (i : Fin (Module.finrank ℂ (spechtSpace lambda)))
    (j : Fin (Module.finrank ℂ (schurModule lambda))) (x : Fin 1 → Fin d) :
    youngSynthesis d 1 x ⟨lambda,(i,j)⟩ =
      ((stdOrthonormalBasis ℂ (spechtSpace lambda) i).val 1) *
        (stdOrthonormalBasis ℂ (schurModule lambda) j).val x := by
  letI : Unique (Equiv.Perm (Fin 1)) := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
  have hp : tensorPermutation d 1 (1 : Equiv.Perm (Fin 1)) = 1 := by
    ext y z
    rfl
  simp [youngSynthesis,hp,act]

end QAlgorithms.Schur


