-- Prove2me | Definitions.Def_opg37364_lps13_eigenspaces
-- name    : opg37364_lps13_eigenspaces
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-09T15:37:27.889258+00:00
-- url     : https://prove2.me/theorems/5f13d89e-721d-4373-ab66-6c528e5e9706
-- title:
--   PSL₂ representations on the fixed-p=13 LPS adjacency eigenspaces
-- statement:
--   For a prime $q>13$ and a chosen $i\in\mathbb F_q$ with $i^2=-1$, use the existing fixed-$p=13$ graph on $P=\operatorname{PGL}_2(\mathbb F_q)$. Its ambient complex vector space is $\mathbb C^P$. The operator $A$ is exactly the ordinary complex adjacency matrix acting on column functions, with no degree normalization; its matrix is the entrywise scalar extension of the real adjacency matrix.
--
--   Let $j:\operatorname{PSL}_2(\mathbb F_q)\hookrightarrow P$ be Mathlib's natural projective inclusion. Left multiplication on vertices induces the representation $(L_g f)(v)=f(j(g)^{-1}v)$. For each real parameter $\mu$, the constructor restricts this representation to $\ker(A-\mu I)$ over $\mathbb C$. Finite dimensionality is inherited from the finite function space and its submodules.
--
--   The bundle includes the finite vertex enumeration, projective inclusion, vertex permutation, complex-linear pullback, ambient representation, ordinary adjacency operator, and eigenspace representation. Its explicit commutation and stability certificates are needed to type the subrepresentation constructor: simultaneous left multiplication preserves right-Cayley adjacency, and reindexing the finite adjacency sum proves $AL_g=L_gA$. These certificates are fully proved, not assumed. The eigenspace is allowed to be zero. No connectedness, quadratic-nonresidue, girth, spectral-bound or nontrivial-representation assertion is included.
-- source:
--   Davidoff, Sarnak and Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs (2003), Example 3.4.2(iii)-(iv) and Definition 3.4.3, printed p. 87; Definition 4.1.1, printed p. 108; Section 4.1, Exercise 4(b), printed p. 112. https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . Specialization of the classical left-regular invariance of Cayley adjacency eigenspaces to the previously defined fixed-p=13 PGL graph, restricted along the natural PSL₂→PGL₂ inclusion. No claim of mathematical novelty.

import Definitions.Def_opg37364_lps13
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RepresentationTheory.Basic

set_option autoImplicit false

noncomputable section
open scoped Classical

namespace OPG37364

/-- The existing LPS13 graph's projective general linear vertex group. -/
abbrev LPS13Vertex (q : ℕ) := Matrix.ProjGenLinGroup (Fin 2) (ZMod q)

/-- The projective special linear group acting on the vertex group. -/
abbrev LPS13ActingGroup (q : ℕ) := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)

/-- Complex-valued functions on the existing PGL₂ vertex type. -/
abbrev LPS13Functions (q : ℕ) := LPS13Vertex q → ℂ

variable {q : ℕ}

/-- A finite enumeration for matrix-vector sums; the vertex type was already proved finite. -/
noncomputable instance lps13PGL_fintype [Fact q.Prime] :
    Fintype (LPS13Vertex q) := Fintype.ofFinite _

/-- The natural injective homomorphism from PSL₂ to PGL₂. -/
def lps13PSLToPGL : LPS13ActingGroup q →* LPS13Vertex q :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL

/-- Left multiplication on vertices, with its inverse included. -/
def lps13LeftVertex (g : LPS13ActingGroup q) : LPS13Vertex q ≃ LPS13Vertex q :=
  Equiv.mulLeft (lps13PSLToPGL g)

/-- Pullback by inverse left multiplication: `(L_g f)(v) = f(j(g)⁻¹ * v)`. -/
def lps13LeftTranslate (g : LPS13ActingGroup q) : LPS13Functions q ≃ₗ[ℂ] LPS13Functions q :=
  LinearEquiv.piCongrLeft' ℂ (fun _ : LPS13Vertex q => ℂ) (lps13LeftVertex g)

@[simp] theorem lps13LeftTranslate_apply (g : LPS13ActingGroup q)
    (f : LPS13Functions q) (v : LPS13Vertex q) :
    lps13LeftTranslate g f v = f ((lps13PSLToPGL g)⁻¹ * v) := rfl

/-- The left regular action restricted along the natural PSL₂→PGL₂ inclusion. -/
def lps13LeftRepresentation : Representation ℂ (LPS13ActingGroup q) (LPS13Functions q) where
  toFun g := (lps13LeftTranslate g).toLinearMap
  map_one' := by
    ext f v
    simp
  map_mul' g h := by
    ext f v
    simp [mul_assoc]

@[simp] theorem lps13LeftRepresentation_apply (g : LPS13ActingGroup q)
    (f : LPS13Functions q) (v : LPS13Vertex q) :
    lps13LeftRepresentation g f v = f ((lps13PSLToPGL g)⁻¹ * v) := rfl

variable [Fact q.Prime]

/-- The ordinary, unnormalized complex adjacency operator of the existing graph. -/
def lps13AdjacencyEnd (hq : 13 < q) (i : LPS13Root q) : Module.End ℂ (LPS13Functions q) :=
  ((lps13Graph hq i).adjMatrix ℂ).mulVecLin

theorem lps13AdjacencyEnd_apply (hq : 13 < q) (i : LPS13Root q)
    (f : LPS13Functions q) (v : LPS13Vertex q) :
    lps13AdjacencyEnd hq i f v =
      ∑ w, if (lps13Graph hq i).Adj v w then f w else 0 := by
  simp [lps13AdjacencyEnd, Matrix.mulVec, dotProduct,
    SimpleGraph.adjMatrix_apply, ite_mul]

/-- Entrywise scalar extension of the real adjacency matrix, without a claim about spectra. -/
theorem lps13AdjMatrix_complex (hq : 13 < q) (i : LPS13Root q) :
    (lps13Graph hq i).adjMatrix ℂ =
      ((lps13Graph hq i).adjMatrix ℝ).map (fun x : ℝ => (x : ℂ)) := by
  ext u v
  simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

/-- Simultaneous left multiplication preserves the right Cayley graph's adjacency. -/
theorem lps13LeftVertex_adj_iff (hq : 13 < q) (i : LPS13Root q)
    (g : LPS13ActingGroup q) (u v : LPS13Vertex q) :
    (lps13Graph hq i).Adj (lps13LeftVertex g u) (lps13LeftVertex g v) ↔
      (lps13Graph hq i).Adj u v :=
  SimpleGraph.mulCayley_adj_mul_iff_right

/-- Commutation certificate needed to restrict the action to adjacency eigenspaces. -/
theorem lps13AdjacencyEnd_commute (hq : 13 < q) (i : LPS13Root q)
    (g : LPS13ActingGroup q) :
    Commute (lps13AdjacencyEnd hq i) (lps13LeftRepresentation g) := by
  apply LinearMap.ext
  intro f
  funext v
  change lps13AdjacencyEnd hq i (lps13LeftRepresentation g f) v =
    lps13LeftRepresentation g (lps13AdjacencyEnd hq i f) v
  simp only [lps13AdjacencyEnd_apply, lps13LeftRepresentation_apply]
  have hsum := Equiv.sum_comp (Equiv.mulLeft ((lps13PSLToPGL g)⁻¹))
    (fun w => if (lps13Graph hq i).Adj ((lps13PSLToPGL g)⁻¹ * v) w then f w else 0)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro w _
  change (if (lps13Graph hq i).Adj v w then f ((lps13PSLToPGL g)⁻¹ * w) else 0) =
    if (lps13Graph hq i).Adj ((lps13PSLToPGL g)⁻¹ * v) ((lps13PSLToPGL g)⁻¹ * w)
      then f ((lps13PSLToPGL g)⁻¹ * w) else 0
  have hadj : (lps13Graph hq i).Adj ((lps13PSLToPGL g)⁻¹ * v)
      ((lps13PSLToPGL g)⁻¹ * w) ↔ (lps13Graph hq i).Adj v w :=
    SimpleGraph.mulCayley_adj_mul_iff_right
  simp only [hadj]

/-- The ordinary complex adjacency eigenspace at a real parameter. It may be zero. -/
abbrev lps13AdjacencyEigenspace (hq : 13 < q) (i : LPS13Root q) (μ : ℝ) :=
  (lps13AdjacencyEnd hq i).eigenspace (μ : ℂ)

/-- The stability certificate used by the representation restriction constructor. -/
theorem lps13Eigenspace_stable (hq : 13 < q) (i : LPS13Root q)
    (μ : ℝ) (g : LPS13ActingGroup q) :
    Set.MapsTo (lps13LeftRepresentation g)
      (lps13AdjacencyEigenspace hq i μ) (lps13AdjacencyEigenspace hq i μ) :=
  Module.End.mapsTo_genEigenspace_of_comm (lps13AdjacencyEnd_commute hq i g) (μ : ℂ) 1

/-- The finite-dimensional complex PSL₂ representation on an adjacency eigenspace.
No nonzero-eigenspace or nontrivial-action hypothesis or conclusion is built into this object. -/
def lps13EigenspaceRepresentation (hq : 13 < q) (i : LPS13Root q) (μ : ℝ) :
    Representation ℂ (LPS13ActingGroup q) (lps13AdjacencyEigenspace hq i μ) :=
  lps13LeftRepresentation.subrepresentation (lps13AdjacencyEigenspace hq i μ)
    (fun g => lps13Eigenspace_stable hq i μ g)

end OPG37364


