-- Prove2me | Definitions.Def_PreservePast_IsHaarFrame
-- name    : PreservePast_IsHaarFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:33.167203+00:00
-- url     : https://prove2.me/theorems/c734e126-ea01-479a-b78f-fa9e0d108583
-- title:
--   Haar law of orthonormal $t$-frames and the uniform law on the sphere
-- statement:
--   An ordered orthonormal $t$-frame in $\mathbb R^D$ ($t\le D$) is a $D\times t$ matrix $U$ whose columns $U_1,\dots,U_t$ are orthonormal. The **Haar law** of such frames is the uniform, rotation-invariant law: a probability law concentrated on orthonormal frames and invariant under $U\mapsto OU$ for every orthogonal $O\in O(D)$. Since $O(D)$ acts transitively on frames, this law is unique. A matrix $V\in\mathbb R^{q\times d}$ uniform on the **row-Stiefel manifold** is the transpose of a Haar $q$-frame of $\mathbb R^d$. For $t=1$ one gets the **uniform law on the unit sphere** $S^{D-1}$, defined in the same way for vectors.
--
--   **Formalization Note** A frame is the $t$-tuple of its columns (`Fin t → EuclideanSpace ℝ (Fin D)`); orthogonal maps are linear isometry equivalences of $\mathbb R^D$. Both definitions are predicates on a measure; a verification file proves that such measures exist (the push-forward of the Haar measure of $O(D)$), so statements quantified over them are not vacuous.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3, Lemma 2, p.6 (PDF p.8); §C.2, Lemma 5, p.18 (PDF p.20)

import Mathlib

open MeasureTheory

namespace PreservePast

/-- **The Haar law of an ordered orthonormal `t`-frame in `ℝ^D`.**
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3, Lemma 2, p.6 (PDF p.8): "Let µ be the Haar law, namely the uniform rotation-invariant
law, of an ordered orthonormal t-frame U ∈ ℝ^{D×t} (D ≥ t); the columns of U are t orthonormal
vectors"; §C.2, Lemma 5, p.18: "V ∈ ℝ^{q×d} … uniform on the row-Stiefel manifold".

A frame is the `t`-tuple of its columns. `IsHaarFrame D t μ` says that `μ` is a probability law
concentrated on orthonormal `t`-tuples and invariant under every orthogonal transformation of
`ℝ^D` applied to all columns. Such a law exists for `t ≤ D` and is unique (the orthogonal group acts
transitively on frames), so this characterizes the uniform law on the Stiefel manifold. A row-Stiefel
matrix `V ∈ ℝ^{q×d}` is the transpose of a Haar `q`-frame of `ℝ^d` (its rows are the frame).

**Formalization Note.** Columns are `EuclideanSpace ℝ (Fin D)` vectors; orthogonal maps are linear
isometry equivalences. Existence is proved in a verification file (push-forward of the Haar measure
of the orthogonal group). -/
def IsHaarFrame (D t : ℕ) (μ : Measure (Fin t → EuclideanSpace ℝ (Fin D))) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ U ∂μ, Orthonormal ℝ U) ∧
    ∀ Q : EuclideanSpace ℝ (Fin D) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin D),
      μ.map (fun U j => Q (U j)) = μ

/-- **The uniform law on the unit sphere `S^{D−1}` of `ℝ^D`** (Lemma 5, p.18: "a vector V uniform
on a D-dimensional unit sphere"): a probability law concentrated on unit vectors and invariant under
every orthogonal transformation (unique for `D ≥ 1`). -/
def IsUniformSphere (D : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin D))) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ v ∂μ, ‖v‖ = 1) ∧
    ∀ Q : EuclideanSpace ℝ (Fin D) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin D), μ.map Q = μ

end PreservePast


