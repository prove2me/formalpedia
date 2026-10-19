-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
-- name    : OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:22:24.828243+00:00
-- url     : https://prove2.me/theorems/204cb8db-2cc1-427d-adf3-ae9aee434be1
-- title:
--   The field criterion over the coordinate field
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it.
--
--   Let $K\subseteq\mathbb R$ be the coordinate field of the configuration, the subfield generated over $\mathbb Q$ by all coordinates $a_{ij}$. Let $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$ be the augmented points, with values in $K$.
--
--   1. **Tensor ring.** $K\otimes_{\mathbb Q}K$, a commutative $\mathbb Q$-algebra.
--   2. **Multiplication.** The $\mathbb Q$-algebra homomorphism $m:K\otimes_{\mathbb Q}K\to K$, $x\otimes y\mapsto xy$.
--   3. **Field criterion.** There is a matrix $P=(P_{\alpha\beta})_{\alpha,\beta\in\{0,\dots,d\}}$ over $K\otimes_{\mathbb Q}K$ with
--   $$
--   \sum_{\alpha,\beta}\bigl(\tilde a_i(\alpha)\otimes1\bigr)P_{\alpha\beta}\bigl(1\otimes\tilde a_i(\beta)\bigr)=0\quad\text{for every }i,\qquad m(P_{jk})=\delta_{jk}\ \ (1\le j,k\le d).
--   $$
--
--   This is the field-coefficient form of the tensor criterion. For injective configurations with full affine span and at least two points, it is equivalent to the Ramsey property.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyQuadratic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic

namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

abbrev TensorRing {s d : ℕ} (a : Fin s → Space d) := Coeff a ⊗[ℚ] Coeff a

def multiply {s d : ℕ} (a : Fin s → Space d) : TensorRing a →ₐ[ℚ] Coeff a :=
  Algebra.TensorProduct.lmul' ℚ

def FieldCriterion {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∃ P : Matrix (Option (Fin d)) (Option (Fin d)) (TensorRing a),
    (∀ i : Fin s, ∑ α, ∑ β,
      ((augmented a i α) ⊗ₜ[ℚ] (1 : Coeff a)) * P α β *
      ((1 : Coeff a) ⊗ₜ[ℚ] (augmented a i β)) = 0) ∧
    (∀ α β : Fin d, multiply a (P (some α) (some β)) = if α = β then 1 else 0)

end EuclideanRamsey

end

end OAI


