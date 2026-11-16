-- Prove2me | Definitions.Def_SmoothBerr_Supplement_IsGeneralInverseProblem
-- name    : SmoothBerr_Supplement_IsGeneralInverseProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:54:27.023694+00:00
-- url     : https://prove2.me/theorems/4818c51e-cd2e-43d9-8072-8175b13b5bf6
-- title:
--   Setting 6.1 (General Inverse Problem)
-- statement:
--   A **general inverse problem** consists of a set $\mathcal F\subseteq\mathbb R^{n\times n}$ of invertible matrices and a test $\mathrm{acc}:\mathbb R^{n\times n}\times\mathbb R^n\times\mathbb R^n\to\{0,1\}$ such that for all $A\in\mathcal F$, all orthogonal $U,V\in\mathbb R^{n\times n}$ and all $b,z\in\mathbb R^n$:
--
--   1. (orthogonal invariance of $\mathcal F$) $U^\top AV\in\mathcal F$;
--   2. (orthogonal invariance of the test) if $Ub=b$ then $\mathrm{acc}(U^\top AV,b,z)=\mathrm{acc}(A,b,Vz)$;
--   3. (solvability) $\mathrm{acc}(A,b,A^{-1}b)=1$.
--
--   The backward-error test $\mathrm{acc}(A,b,z)=\mathbf 1\{\mathrm{berr}(A,b,z)\le\varepsilon\}$ of Eq. (18) is the instance behind Theorem 4.4. The setting is the hypothesis of Theorems 6.2 and 6.4.
--
--   **Formalization Note** The $\{0,1\}$-valued test is a predicate ($\mathrm{acc}=1$ is the predicate holding); orthogonal matrices are the elements of `Matrix.orthogonalGroup`.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Setting 6.1, p.16

import Mathlib

open Matrix

namespace SmoothBerr.Supplement

/-- **Setting 6.1 (General Inverse Problem)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed
analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256
9575cd20…, Setting 6.1, p.16). A set `F` of invertible `n × n` matrices and a test
`acc(A, b, z)` such that for all `A ∈ F`, all orthogonal `U, V` and all `b, z`:
1. `UᵀAV ∈ F` (orthogonal invariance of `F`);
2. if `Ub = b` then `acc(UᵀAV, b, z) = acc(A, b, Vz)` (orthogonal invariance of `acc`);
3. `acc(A, b, A⁻¹b) = 1` (solvability).

**Formalization Note** The `{0,1}`-valued test is a predicate (`acc = 1` is `acc` holding).
Orthogonal means membership in `Matrix.orthogonalGroup (Fin n) ℝ`. -/
def IsGeneralInverseProblem {n : ℕ} (F : Set (Matrix (Fin n) (Fin n) ℝ))
    (acc : Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Prop) : Prop :=
  (∀ A ∈ F, IsUnit A.det) ∧
  (∀ A ∈ F, ∀ U ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ V ∈ Matrix.orthogonalGroup (Fin n) ℝ,
    Uᵀ * A * V ∈ F) ∧
  (∀ A ∈ F, ∀ U ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ V ∈ Matrix.orthogonalGroup (Fin n) ℝ,
    ∀ b z : Fin n → ℝ, U *ᵥ b = b → (acc (Uᵀ * A * V) b z ↔ acc A b (V *ᵥ z))) ∧
  (∀ A ∈ F, ∀ b : Fin n → ℝ, acc A b (A⁻¹ *ᵥ b))

end SmoothBerr.Supplement


