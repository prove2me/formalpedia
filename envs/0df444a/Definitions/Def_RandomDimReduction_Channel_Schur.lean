-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Schur
-- name    : RandomDimReduction_Channel_Schur
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:23:37.079656+00:00
-- url     : https://prove2.me/theorems/5205685c-fc63-463d-ae88-c75c8d1b2d9a
-- title:
--   Labelled compatible Schur coordinates and representation dimensions
-- statement:
--   Shapes are partitions of $n$, independent of the ambient dimension. The Specht dimension is the dimension of the published Young left ideal; the Weyl dimension is the dimension of the actual published Schur module, or zero when the height exceeds $d$. Isotypic projectors use the published central character formula. A shared unitary Specht model is labelled by equivalence to each actual Specht module. A Schur transform is a unitary matrix $S$ with matrix functions $\nu_\lambda^d$ satisfying
--   $$ S F_\pi^d A^{\otimes n} S^\dagger=\bigoplus_\lambda\kappa_\lambda(\pi)\otimes\nu_\lambda^d(A) $$
--   for every permutation and every complex matrix $A$, including singular ones. Blocks are extracted from $SXS^\dagger$.
--
--   The shared Specht model makes it meaningful to preserve a Specht register while changing dimension. No twirl or dimension-reduction theorem is included in this interface.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), §5.1, Eq.(13), pp.15–16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Tensor
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition

set_option autoImplicit false

noncomputable section
open Matrix
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- All partitions of n, independent of the ambient dimension. -/
abbrev Shape (n : ℕ) := QAlgorithms.Schur.Partition n n

def height {n : ℕ} (lam : Shape n) : ℕ := lam.val.colLen 0

def shapeAt {n d : ℕ} (lam : Shape n) (h : height lam ≤ d) :
    QAlgorithms.Schur.Partition d n := ⟨lam.val, lam.property.1, h⟩

def spechtDim {n : ℕ} (lam : Shape n) : ℕ :=
  Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lam)

/-- Dimension of the actual Schur module, with zero for absent blocks. -/
def weylDim (d : ℕ) {n : ℕ} (lam : Shape n) : ℕ :=
  if h : height lam ≤ d then
    Module.finrank ℂ (QAlgorithms.Schur.schurModule (shapeAt lam h)) else 0

/-- The source's Πlam, defined by the published central character idempotent. -/
def isotypic (d : ℕ) {n : ℕ} (lam : Shape n) : Op (Word n d) :=
  if h : height lam ≤ d then QAlgorithms.Schur.isotypicProjector (shapeAt lam h) else 0

def lowProjector (n k d : ℕ) : Op (Word n d) :=
  ∑ lam : Shape n, if height lam ≤ k then isotypic d lam else 0

def highProjector (n k d : ℕ) : Op (Word n d) :=
  ∑ lam : Shape n, if k < height lam then isotypic d lam else 0

abbrev SchurIndex (n d : ℕ) :=
  (lam : Shape n) × (Fin (spechtDim lam) × Fin (weylDim d lam))

/-- Reference Specht action, used only to label equivalence classes. -/
def standardSpecht {n : ℕ} (lam : Shape n) (π : Equiv.Perm (Fin n)) :
    Op (Fin (spechtDim lam)) := fun i j =>
  inner ℂ (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam) i)
    (QAlgorithms.Schur.spechtRepresentation lam π
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lam) j))

/-- One unitary model for each labelled Specht class, shared across dimensions.
The equivalence condition fixes the label without prescribing inefficient coordinates. -/
structure SpechtModel (n : ℕ) where
  action : ∀ lam : Shape n, Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin (spechtDim lam)) ℂ
  labelled : ∀ lam, ∃ E : Matrix.unitaryGroup (Fin (spechtDim lam)) ℂ,
    ∀ π, (E : Op _) * (action lam π : Op _) * (E : Op _)ᴴ = standardSpecht lam π

/-- Eq.(13), p.15. ν is evaluated on ALL matrices, including singular ones.
Unitarity and this intertwining relation define a Schur coordinate system;
none of the twirl, moment or reduction formulas is assumed. -/
structure SchurTransform {n : ℕ} (κ : SpechtModel n) (d : ℕ) where
  U : Matrix (SchurIndex n d) (Word n d) ℂ
  left_unitary : U * Uᴴ = 1
  right_unitary : Uᴴ * U = 1
  nu : ∀ lam : Shape n, Op (Fin d) → Op (Fin (weylDim d lam))
  intertwines : ∀ (π : Equiv.Perm (Fin n)) (A : Op (Fin d)),
    U * QAlgorithms.Schur.tensorPermutation d n π * tensor n A * Uᴴ =
      Matrix.blockDiagonal' (fun lam =>
        Matrix.kronecker (κ.action lam π : Op _) (nu lam A))

/-- A block of U X U†, with the source's Specht-first factor order. -/
def schurBlock {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (X : Op (Word n d)) (lam μ : Shape n) :
    Matrix (Fin (spechtDim lam) × Fin (weylDim d lam))
      (Fin (spechtDim μ) × Fin (weylDim d μ)) ℂ :=
  fun i j => (S.U * X * S.Uᴴ) ⟨lam, i⟩ ⟨μ, j⟩

/-- The block matrix appearing in Lemma 5.4. -/
def twirlBlocks {n d : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (X : Op (Word n d)) : Op (SchurIndex n d) :=
  Matrix.blockDiagonal' fun lam => Matrix.kronecker
    (WildeQIT.partialTraceRight (schurBlock S X lam lam))
    (((weylDim d lam : ℂ)⁻¹) • (1 : Op (Fin (weylDim d lam))))

/-- The low-block formula in Theorem 5.3, in the k-Schur output space. -/
def reductionBlocks {n d k : ℕ} {κ : SpechtModel n} (S : SchurTransform κ d)
    (X : Op (Word n d)) : Op (SchurIndex n k) :=
  Matrix.blockDiagonal' fun lam => Matrix.kronecker
    (WildeQIT.partialTraceRight (schurBlock S X lam lam))
    (((weylDim k lam : ℂ)⁻¹) • (1 : Op (Fin (weylDim k lam))))

end RandomDimReduction.Channel


