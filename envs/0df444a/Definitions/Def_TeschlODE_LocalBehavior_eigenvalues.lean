-- Prove2me | Definitions.Def_TeschlODE_LocalBehavior_eigenvalues
-- name    : TeschlODE_LocalBehavior_eigenvalues
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:55:35.327675+00:00
-- url     : https://prove2.me/theorems/4d81cf45-8b9b-4142-bd49-8b09fee47fd0
-- title:
--   The (complex) eigenvalues $\alpha_j$ of a real $n \times n$ matrix
-- statement:
--   Let $n \in \mathbb{N}$ and let $A$ be a real $n \times n$ matrix. The **eigenvalues** of $A$ are the complex numbers $z$ for which there is a nonzero vector $v \in \mathbb{C}^n$ with
--   $$A v = z v,$$
--   where $A$ acts on $\mathbb{C}^n$ by regarding its real entries as complex numbers. Equivalently, they are the complex roots $\alpha_1, \dots, \alpha_m$ of the characteristic polynomial of $A$.
--
--   Every stability statement of Chapters 9 and 10 is phrased through them: the linear flow $e^{tA}$ is hyperbolic when no $\alpha_j$ has zero real part, and the linear map $x \mapsto Ax$ is hyperbolic when no $\alpha_j$ has modulus one.
--
--   **Formalization Note.** The set is `{z : ℂ | Module.End.HasEigenvalue (Matrix.toLin' (A.map (↑))) z}`, i.e. eigenvalues of the complexified matrix. Real matrices have non-real eigenvalues in general, which is why the set lives in $\mathbb{C}$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 253, §9.1 (eigenvalues α_j of A, as in §3.2)

import Mathlib

namespace TeschlODE.LocalBehavior

/-- Teschl, §3.2 and §9.1, p. 253: the eigenvalues `α_j` of a real `n × n` matrix `A`, i.e. the
complex numbers `z` for which `A`, regarded as a complex matrix acting on `ℂⁿ`, has an eigenvector.
Equivalently, the (complex) roots of the characteristic polynomial of `A`. -/
def eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Set ℂ :=
  {z | Module.End.HasEigenvalue (Matrix.toLin' (A.map (fun r : ℝ => (r : ℂ)))) z}

end TeschlODE.LocalBehavior


