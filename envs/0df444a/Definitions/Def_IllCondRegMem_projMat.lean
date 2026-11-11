-- Prove2me | Definitions.Def_IllCondRegMem_projMat
-- name    : IllCondRegMem_projMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:45.96433+00:00
-- url     : https://prove2.me/theorems/a7b8d68e-1922-42fb-9c67-71f6b2298c75
-- title:
--   Orthogonal projection matrices $P_F$ and measurable random subspaces and matrices
-- statement:
--   Write $\mathbb R^d$ for the Euclidean space of column vectors indexed by $\{1,\dots,d\}$. For a linear subspace $F\subseteq\mathbb R^d$, $P_F$ denotes the **orthogonal projection** onto $F$; as a matrix, its $j$-th column is $P_F e_j$, the projection of the $j$-th standard basis vector. The **Grassmannian** $\mathrm{Gr}(k,d)$ is the set of $k$-dimensional subspaces of $\mathbb R^d$, and $\mathrm{Gr}(k,F)$ the set of those contained in $F$.
--
--   A **random subspace** is a map $\omega\mapsto E(\omega)$ from a probability space to subspaces of $\mathbb R^d$ such that every entry of the matrix $P_{E(\omega)}$ is a measurable function of $\omega$; a **random matrix** is a matrix-valued map whose entries are measurable.
--
--   These objects are used by every statement of the mission about random subspaces (pruned distributions, the masking lemma, the pruning map) and random covariance matrices.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` (abbreviated `Vec d`); subspaces are `Submodule ℝ (Vec d)` and $P_F$ is `F.starProjection`. Measurability of a random subspace is read through the injective map $E\mapsto P_E$, the usual Borel structure of the Grassmannian.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), §2 "Notations", p.6 (PDF p.7)

import Mathlib

open MeasureTheory

namespace IllCondRegMem

/-- The ambient space `ℝ^d` with its Euclidean inner product, norm and Borel σ-algebra.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §2, p.6.

**Formalization Note.** `Vec d` is `EuclideanSpace ℝ (Fin d)`; its elements are column vectors
indexed by `Fin d`. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- **Orthogonal projection matrix** `P_F` of a subspace `F ⊆ ℝ^d`.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §2
"Notations", p.6: "for any subspace F ⊆ ℝ^d we denote … by P_F its orthogonal projection".

`projMat F` is the `d × d` matrix whose `j`-th column is the orthogonal projection of the
`j`-th standard basis vector onto `F`.

**Formalization Note.** Subspaces are `Submodule ℝ (Vec d)` (every such subspace is closed, so
the orthogonal projection `F.starProjection` exists). The Grassmannian `Gr(k, d)` is the set of
subspaces with `Module.finrank ℝ F = k`. -/
noncomputable def projMat {d : ℕ} (F : Submodule ℝ (Vec d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => F.starProjection (EuclideanSpace.single j (1 : ℝ)) i

/-- A **random subspace** `E : Ω → Submodule ℝ (Vec d)` is measurable when every entry of its
projection matrix `P_E` is a measurable function of the sample point.

**Formalization Note.** This is the Borel structure of the Grassmannian, read through the
injective map `E ↦ P_E`; it is required so that the probabilities of events about `E` and the
laws built from `E` are defined. -/
def IsRandomSubspace {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (E : Ω → Submodule ℝ (Vec d)) : Prop :=
  ∀ i j, Measurable fun ω => projMat (E ω) i j

/-- A **random matrix** `A : Ω → Matrix (Fin m) (Fin n) ℝ` is measurable when every entry is a
measurable function of the sample point. -/
def IsRandomMatrix {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (A : Ω → Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, Measurable fun ω => A ω i j

end IllCondRegMem


