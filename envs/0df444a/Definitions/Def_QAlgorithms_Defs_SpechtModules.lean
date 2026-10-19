-- Prove2me | Definitions.Def_QAlgorithms_Defs_SpechtModules
-- name    : QAlgorithms_Defs_SpechtModules
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:39:08.749813+00:00
-- url     : https://prove2.me/theorems/f5058929-2ffc-4c76-92f9-060899e4dbc5
-- title:
--   SpechtModules
-- statement:
--   SpechtModules
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SpechtModules.lean

import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix

namespace QAlgorithms.Schur

attribute [local instance] Classical.propDecidable

/-- Public cell numbering for a shape of size n. Changing the numbering conjugates
the representation and does not change its isomorphism class
(1508.01797 pp.4-5, Young symmetrizer construction). -/
def cellNumbering {d n : ℕ} (lambda : Partition d n) : lambda.val.cells ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa [YoungDiagram.card] using lambda.property.1)

/-- Row-preserving permutations for the numbered Young diagram
(1508.01797 p.4, subgroup A_T). -/
def rowPermutations {d n : ℕ} (lambda : Partition d n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun pi => ∀ i,
    ((cellNumbering lambda).symm (pi i)).val.1 = ((cellNumbering lambda).symm i).val.1

/-- Column-preserving permutations (1508.01797 p.4, subgroup B_T). -/
def columnPermutations {d n : ℕ} (lambda : Partition d n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun pi => ∀ i,
    ((cellNumbering lambda).symm (pi i)).val.2 = ((cellNumbering lambda).symm i).val.2

/-- Right multiplication by the row-symmetrized, column-antisymmetrized Young
element in the regular S_n module. Its image is the Specht left ideal
(1508.01797 pp.4-5). It is not claimed to be an orthogonal projector. -/
def youngRightOperator {d n : ℕ} (lambda : Partition d n) :
    Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  Matrix.of fun g h => ∑ a ∈ rowPermutations lambda, ∑ b ∈ columnPermutations lambda,
    if g = h*a*b then ((Equiv.Perm.sign b : ℤˣ) : ℤ) else 0

/-- The Specht module constructed as the regular Young left ideal, with its
inherited finite-dimensional Hilbert inner product (1508.01797 pp.4-5;
1508.01907 pp.4-6). The dimension is determined by lambda. -/
def spechtSpace {d n : ℕ} (lambda : Partition d n) :
    Submodule ℂ (EuclideanSpace ℂ (Equiv.Perm (Fin n))) :=
  LinearMap.range (Matrix.toEuclideanLin (youngRightOperator lambda))

/-- Left regular action on the permutation basis (1508.01797 p.4, S_n action). -/
def leftRegular {n : ℕ} (pi : Equiv.Perm (Fin n)) :
    Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ :=
  Matrix.of fun g h => if g = pi*h then 1 else 0

/-- Actual Specht action on the constructed Young left ideal. The orthogonal
projection supplies a subtype-valued formula; left multiplication already preserves
this ideal, so it does not alter the action (1508.01797 pp.4-5; 1508.01907 pp.4-6).
Representation laws and the standard-tableau dimension formula are supporting work. -/
def spechtRepresentation {d n : ℕ} (lambda : Partition d n) (pi : Equiv.Perm (Fin n)) :
    spechtSpace lambda →ₗ[ℂ] spechtSpace lambda :=
  (spechtSpace lambda).orthogonalProjectionOnto.toLinearMap.comp
    ((Matrix.toEuclideanLin (leftRegular pi)).comp (spechtSpace lambda).subtype)

/-- One-box Young element is the identity of the one-dimensional regular module
(1508.01797 pp.4-5). -/
theorem youngRightOperator_one {d : ℕ} (lambda : Partition d 1) :
    youngRightOperator lambda = 1 := by
  letI : Unique (Equiv.Perm (Fin 1)) := ⟨⟨1⟩,fun _ => Subsingleton.elim _ _⟩
  ext g h
  have hg : g = 1 := Subsingleton.elim _ _
  have hh : h = 1 := Subsingleton.elim _ _
  subst g
  subst h
  have hr : rowPermutations lambda = {1} := by
    ext pi
    have hp : pi = 1 := Subsingleton.elim _ _
    subst pi
    simp [rowPermutations]
  have hc : columnPermutations lambda = {1} := by
    ext pi
    have hp : pi = 1 := Subsingleton.elim _ _
    subst pi
    simp [columnPermutations]
  simp [youngRightOperator,hr,hc]
  rw [Finset.filter_singleton]
  simp

example {d : ℕ} (lambda : Partition d 1) :
    spechtSpace lambda = ⊤ := by
  rw [spechtSpace,youngRightOperator_one]
  simp

end QAlgorithms.Schur


