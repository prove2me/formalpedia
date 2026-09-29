-- Prove2me | Definitions.Def_PassivityUn_admissible
-- name    : PassivityUn_admissible
-- status  : Definition
-- author  : @ShapeZero
-- created : 2026-09-23T20:54:10.124785+00:00
-- url     : https://prove2.me/theorems/9c1ec95f-5969-4724-983a-f6971f58628f
-- title:
--   Symmetric matrices commuting with $J$ (admissible coupling class)
-- statement:
--   Let $J_n = \begin{pmatrix} 0 & -I_n \\ I_n & 0 \end{pmatrix}$ be the standard complex structure on real $2n\times 2n$ block matrices. Three real linear subspaces of this $4n^2$-dimensional space are defined:
--
--   1. $\mathrm{commJ}(n) = \{\, W : WJ_n = J_nW \,\}$, the matrices commuting with $J_n$;
--   2. $\mathrm{symm}(n) = \{\, W : W^{\mathsf T} = W \,\}$, the symmetric matrices;
--   3. the **admissible coupling class**
--   $$
--   \mathcal{A}_n = \mathrm{symm}(n) \cap \mathrm{commJ}(n) = \{\, W \in \mathbb{R}^{2n\times 2n} : W^{\mathsf T} = W \ \text{and}\ WJ_n = J_nW \,\}.
--   $$
--
--   $\mathcal{A}_n$ is the object whose dimension the mission's goal computes.
--
--   **Formalization Note** Each condition is the kernel of a linear map ($W \mapsto WJ_n - J_nW$ and $W \mapsto W^{\mathsf T} - W$), so each set is a subspace by construction.
-- source:
--   Shape Zero LLC, "Formal Proofs of the C1 Verification Package" (August 2026), §6, Theorem 6.1 (J-compatible symmetric couplings): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ShapeZero_C1_Formal_Proofs.pdf ; corrected in "Errata — C1 Formal Proofs (Sections 3 and 6)", Corrected Theorem 6.1(b): https://github.com/ShapeZeroSZ/shape-zero/blob/main/01_source/proofs/ERRATUM_Theorem_6.1.md

import Mathlib
import Definitions.Def_PassivityUn_stdJ

open Matrix

namespace PassivityUn

/-- Commuting with J, as the kernel of W ↦ W J - J W. -/
def commJ (n : ℕ) : Submodule ℝ (Matrix (Blk n) (Blk n) ℝ) :=
  LinearMap.ker (LinearMap.mulRight ℝ (stdJ n) - LinearMap.mulLeft ℝ (stdJ n))

/-- Symmetric, as the kernel of W ↦ Wᵀ - W. -/
def symm (n : ℕ) : Submodule ℝ (Matrix (Blk n) (Blk n) ℝ) :=
  LinearMap.ker ((Matrix.transposeLinearEquiv (Blk n) (Blk n) ℝ ℝ).toLinearMap
                 - LinearMap.id)

/-- The passivity-admissible coupling class. -/
def admissible (n : ℕ) : Submodule ℝ (Matrix (Blk n) (Blk n) ℝ) :=
  symm n ⊓ commJ n

end PassivityUn


