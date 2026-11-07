-- Prove2me | Definitions.Def_EuclidSPAgg_IsOrthogonalBox
-- name    : EuclidSPAgg_IsOrthogonalBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:25.543309+00:00
-- url     : https://prove2.me/theorems/286a3688-231a-4c51-9aa3-95549d4cddbf
-- title:
--   Orthogonal box
-- statement:
--   A set $C\subseteq E$ is an **orthogonal box** if it is a product of nonempty closed intervals in an orthonormal affine frame. The factors may be bounded intervals, half-lines, full lines or singletons. Equivalently, there are an orthonormal basis $(e_1,\dots,e_d)$ of $E$ and nonempty closed intervals $J_1,\dots,J_d\subseteq\mathbb R$ (possibly with infinite endpoints) such that
--   $$
--   C=\{x\in E:\ \langle e_j,x\rangle\in J_j\ \text{for } j=1,\dots,d\}.
--   $$
--
--   **Formalization Note** A nonempty closed interval with possibly infinite endpoints is a nonempty closed order-connected subset of $\mathbb R$. The affine origin of the frame is absorbed into the intervals, and an intrinsic frame of a lower-dimensional box is extended to $E$ by singleton factors, as the paper does on p.9.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- An orthogonal box (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)): a product of nonempty closed intervals
in an orthonormal affine frame; factors may be bounded, half-lines, full lines or singletons.

**Formalization Note** The frame is an orthonormal basis `B` of `E`, and the box is
`{x | ∀ j, ⟨B j, x⟩ ∈ J j}`. Each factor `J j ⊆ ℝ` is nonempty, closed and order-connected,
which is exactly a nonempty closed interval with possibly infinite endpoints (singletons and `ℝ`
included). The affine origin is absorbed into the factors, and an intrinsic frame of a
lower-dimensional box is extended to `E` by singleton factors, as on p.9. -/
def IsOrthogonalBox {d : ℕ} (C : Set (E d)) : Prop :=
  ∃ (B : OrthonormalBasis (Fin d) ℝ (E d)) (J : Fin d → Set ℝ),
    (∀ j, (J j).Nonempty ∧ IsClosed (J j) ∧ (J j).OrdConnected) ∧
    C = {x | ∀ j, inner ℝ (B j) x ∈ J j}

end EuclidSPAgg


