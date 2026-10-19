-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
-- name    : OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:25:10.021996+00:00
-- url     : https://prove2.me/theorems/e0040391-c394-441b-9d04-f260d2299d18
-- title:
--   The coordinate field and the field criterion
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it.
--
--   1. **Coordinate field.** For a configuration $a_0,\dots,a_{s-1}\in\mathbb R^d$, the subfield $K\subseteq\mathbb R$ generated over $\mathbb Q$ by all coordinates $a_{ij}$. Each coordinate is an element of $K$.
--   2. **Augmented points.** $\tilde a_i:\{0,\dots,d\}\to K$ with $\tilde a_i(0)=1$ and $\tilde a_i(j)=a_{ij}$.
--   3. **Tensor ring and multiplication.** $K\otimes_{\mathbb Q}K$ and the algebra homomorphism $m(x\otimes y)=xy$.
--   4. **Field criterion.** There is a matrix $P$ indexed by $\{0,\dots,d\}^2$ over $K\otimes_{\mathbb Q}K$ with
--   $$
--   \sum_{\alpha,\beta}\bigl(\tilde a_i(\alpha)\otimes1\bigr)P_{\alpha\beta}\bigl(1\otimes\tilde a_i(\beta)\bigr)=0\ \text{ for all }i,\qquad m(P_{jk})=\delta_{jk}\ (1\le j,k\le d).
--   $$
--
--   For injective configurations with full affine span and at least two points, the field criterion is equivalent to the Ramsey property.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle

namespace OAI

noncomputable section
open scoped TensorProduct
namespace EuclideanRamsey

def coordinateField {s d : ℕ} (a : Fin s → Space d) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (Set.range (fun ij : Fin s × Fin d => a ij.1 ij.2))

abbrev Coeff {s d : ℕ} (a : Fin s → Space d) := ↥(coordinateField a)
abbrev TensorRing {s d : ℕ} (a : Fin s → Space d) := Coeff a ⊗[ℚ] Coeff a

def coordinate {s d : ℕ} (a : Fin s → Space d) (i : Fin s) (j : Fin d) : Coeff a :=
  ⟨a i j, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self (i, j))⟩

def augmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → Coeff a
  | none => 1
  | some j => coordinate a i j

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


