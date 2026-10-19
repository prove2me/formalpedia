-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
-- name    : MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:05.357702+00:00
-- url     : https://prove2.me/theorems/2050d9d3-68aa-4e2b-bfaf-a40391d45230
-- title:
--   Definitions of ProjectorONB: Projector Range Orthonormal Bases This file packages the finite-dimensional spectral decomposition of an orthogonal…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.ProjectorONB` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Projector Range Orthonormal Bases. This file packages the finite-dimensional spectral decomposition of an orthogonal projector as an orthonormal basis of its range. It supplies the rank-one decomposition needed by the rank-reduction truncation branch in the low-degree-test formalization.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (5): `MIPStarRE.Quantum.IsProj.rangeONB` (Choose an orthonormal basis of the range of a projector using Mathlib's Hermitian spectral theorem.); `MIPStarRE.Quantum.ProjectorRangeONB` (A rank-indexed orthonormal basis of the range of a projector, packaged with the corresponding rank-one decomposition.); `MIPStarRE.Quantum.ProjectorRangeONB.rankOne` (The rank-one projector attached to one vector of a projector range ONB.); `MIPStarRE.Quantum.ProjectorRangeONB.subprojector` (The partial projector obtained by summing a subset of range ONB rank-one projectors.); `_private.MIPRE.Background.LIDT.MIPStarRE.Quantum.ProjectorONB.0.MIPStarRE.Quantum.IsProj.nonzeroEigenEquivFinRank` (The nonzero-eigenvalue index set of a projector has cardinality equal to its matrix rank.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eigenvalues_zero_or_one`, `eq_sum_nonzero_eigenvector_projectors`, `rankOne_apply`, `hermitian_eq_sum_eigenvalues_vecMulVec`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.Quantum.ProjectorONB` (`MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/ProjectorONB.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/ProjectorONB.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace

set_option backward.isDefEq.respectTransparency false

/-!
# Projector Range Orthonormal Bases

This file packages the finite-dimensional spectral decomposition of an
orthogonal projector as an orthonormal basis of its range. It supplies the
rank-one decomposition needed by the rank-reduction truncation branch in the
low-degree-test formalization.

## References

- `references/ldt-paper/orthonormalization.tex`, lines 570--573.
- `MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/LowRank.lean`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.L2Operator

namespace MIPStarRE.Quantum

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral expansion of a Hermitian matrix as a sum of rank-one eigenvector
projectors weighted by eigenvalues. -/
lemma hermitian_eq_sum_eigenvalues_vecMulVec (A : Op ι) (hA : A.IsHermitian) :
    A = ∑ i : ι, ((hA.eigenvalues i : ℂ) •
      Matrix.vecMulVec ((hA.eigenvectorBasis i).ofLp)
        (star ((hA.eigenvectorBasis i).ofLp))) := by
  classical
  calc
    A = Unitary.conjStarAlgAut ℂ (Op ι) hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
    _ = ∑ i : ι, ((hA.eigenvalues i : ℂ) •
        Matrix.vecMulVec ((hA.eigenvectorBasis i).ofLp)
          (star ((hA.eigenvectorBasis i).ofLp))) := by
          ext r c
          simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
            Matrix.sum_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          simp [Matrix.smul_apply, Matrix.vecMulVec_apply]
          ring

/-- For a Hermitian idempotent matrix, every eigenvalue is either `0` or `1`. -/
lemma IsProj.eigenvalues_zero_or_one (P : Op ι) (hP : IsProj P) (i : ι) :
    hP.isSelfAdjoint.isHermitian.eigenvalues i = 0 ∨
      hP.isSelfAdjoint.isHermitian.eigenvalues i = 1 := by
  let hPHerm := hP.isSelfAdjoint.isHermitian
  let v : ι → ℂ := (hPHerm.eigenvectorBasis i).ofLp
  have hv_ne : v ≠ 0 := by
    change (hPHerm.eigenvectorBasis i).ofLp ≠ 0
    simpa using hPHerm.eigenvectorBasis.orthonormal.ne_zero i
  have hmul1 : P *ᵥ v = hPHerm.eigenvalues i • v := by
    simpa [v] using hPHerm.mulVec_eigenvectorBasis i
  have hmul2 : P *ᵥ (P *ᵥ v) = P *ᵥ v := by
    simp [v, hP.isIdempotentElem.eq]
  have hscalar : hPHerm.eigenvalues i * hPHerm.eigenvalues i =
      hPHerm.eigenvalues i := by
    have htmp : (hPHerm.eigenvalues i * hPHerm.eigenvalues i) • v =
        hPHerm.eigenvalues i • v := by
      calc
        (hPHerm.eigenvalues i * hPHerm.eigenvalues i) • v
            = hPHerm.eigenvalues i •
                (hPHerm.eigenvalues i • v) := by
              exact (smul_smul (hPHerm.eigenvalues i)
                (hPHerm.eigenvalues i) v).symm
        _ = hPHerm.eigenvalues i • (P *ᵥ v) := by rw [hmul1]
        _ = P *ᵥ (hPHerm.eigenvalues i • v) := by
              exact (Matrix.mulVec_smul P (hPHerm.eigenvalues i) v).symm
        _ = P *ᵥ (P *ᵥ v) := by rw [hmul1]
        _ = P *ᵥ v := hmul2
        _ = hPHerm.eigenvalues i • v := hmul1
    exact (smul_left_injective ℝ hv_ne) htmp
  have hfactor :
      hPHerm.eigenvalues i * (hPHerm.eigenvalues i - 1) = 0 := by
    nlinarith [hscalar]
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl hzero
  · right
    linarith

/-- A projector is the sum of the rank-one projectors onto the eigenvectors with
nonzero eigenvalue. For a projector these are exactly the `1`-eigenvectors. -/
lemma IsProj.eq_sum_nonzero_eigenvector_projectors (P : Op ι) (hP : IsProj P) :
    P = ∑ i : {i // hP.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0},
      Matrix.vecMulVec ((hP.isSelfAdjoint.isHermitian.eigenvectorBasis i.1).ofLp)
        (star ((hP.isSelfAdjoint.isHermitian.eigenvectorBasis i.1).ofLp)) := by
  classical
  let p : ι → Prop := fun i => hP.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0
  let E : ι → Op ι := fun i =>
    Matrix.vecMulVec ((hP.isSelfAdjoint.isHermitian.eigenvectorBasis i).ofLp)
      (star ((hP.isSelfAdjoint.isHermitian.eigenvectorBasis i).ofLp))
  calc
    P = ∑ i : ι, ((hP.isSelfAdjoint.isHermitian.eigenvalues i : ℂ) • E i) := by
          simpa [E] using hermitian_eq_sum_eigenvalues_vecMulVec P hP.isSelfAdjoint.isHermitian
    _ = ∑ i : ι, if p i then E i else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rcases hP.eigenvalues_zero_or_one P i with hzero | hone
          · simp [p, E, hzero]
          · simp [p, E, hone]
    _ = ∑ i : {i // p i}, E i.1 := by
          rw [← Finset.sum_filter]
          rw [← Finset.sum_subtype_eq_sum_filter]
          simp [p]

/-- A rank-indexed orthonormal basis of the range of a projector, packaged with
the corresponding rank-one decomposition. -/
structure ProjectorRangeONB (P : Op ι) (hP : IsProj P) where
  /-- The chosen range basis vectors. -/
  vec : Fin P.rank → ι → ℂ
  /-- The chosen vectors are orthonormal. -/
  orthonormal : ∀ i j, star (vec i) ⬝ᵥ vec j = if i = j then 1 else 0
  /-- The projector decomposes as the sum of the rank-one projectors onto the
  chosen range basis. -/
  decomposition : P = ∑ i, Matrix.vecMulVec (vec i) (star (vec i))

namespace ProjectorRangeONB

variable {P : Op ι} {hP : IsProj P} (b : ProjectorRangeONB P hP)

omit [DecidableEq ι] in
/-- The rank-one projector attached to one vector of a projector range ONB. -/
noncomputable def rankOne (i : Fin P.rank) : Op ι :=
  Matrix.vecMulVec (b.vec i) (star (b.vec i))

omit [DecidableEq ι] in
/-- The partial projector obtained by summing a subset of range ONB rank-one projectors. -/
noncomputable def subprojector (S : Finset (Fin P.rank)) : Op ι :=
  ∑ i ∈ S, b.rankOne i

omit [DecidableEq ι] in
@[simp] lemma rankOne_apply (i : Fin P.rank) :
    b.rankOne i = Matrix.vecMulVec (b.vec i) (star (b.vec i)) := rfl

end ProjectorRangeONB

/-- The nonzero-eigenvalue index set of a projector has cardinality equal to its
matrix rank. -/
noncomputable def IsProj.nonzeroEigenEquivFinRank (P : Op ι) (hP : IsProj P) :
    {i : ι // hP.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0} ≃ Fin P.rank :=
  Fintype.equivFinOfCardEq hP.isSelfAdjoint.isHermitian.rank_eq_card_non_zero_eigs.symm

/-- Choose an orthonormal basis of the range of a projector using Mathlib's
Hermitian spectral theorem. -/
noncomputable def IsProj.rangeONB (P : Op ι) (hP : IsProj P) :
    ProjectorRangeONB P hP := by
  classical
  let e := hP.nonzeroEigenEquivFinRank P
  let vec : Fin P.rank → ι → ℂ := fun i =>
    (hP.isSelfAdjoint.isHermitian.eigenvectorBasis (e.symm i).1).ofLp
  refine
    { vec := vec
      orthonormal := ?_
      decomposition := ?_ }
  · intro i j
    have hindex : ((e.symm i).1 = (e.symm j).1) ↔ i = j := by
      constructor
      · intro h
        exact (EquivLike.injective e.symm) (Subtype.ext h)
      · intro h
        simp [h]
    have horth := orthonormal_iff_ite.mp hP.isSelfAdjoint.isHermitian.eigenvectorBasis.orthonormal
      (e.symm i).1 (e.symm j).1
    simpa [vec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, hindex] using
      horth
  · have hdecomp := hP.eq_sum_nonzero_eigenvector_projectors P
    simpa [vec, e] using
      (hdecomp.trans
        ((e.symm.sum_comp
          fun i : {i : ι // hP.isSelfAdjoint.isHermitian.eigenvalues i ≠ 0} =>
            Matrix.vecMulVec ((hP.isSelfAdjoint.isHermitian.eigenvectorBasis i.1).ofLp)
              (star ((hP.isSelfAdjoint.isHermitian.eigenvectorBasis i.1).ofLp))).symm))

end

end MIPStarRE.Quantum


