-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate
-- name    : KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:19:28.393645+00:00
-- url     : https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f
-- title:
--   Coordinate tensors and slot symmetrization
-- statement:
--   `Coord n k` is the Euclidean space `EuclideanSpace ℝ (Fin k → Fin n)`, whose norm is the coordinate Hilbert–Schmidt norm for real tensors with $k$ slots and entries indexed by `Fin n`. `slots k a b` selects positions $p$ with $a\le p<b$, while `slotPerm` permutes tensor slots by $(\operatorname{slotPerm}\,\sigma\,A)(i)=A(i\circ\sigma)$. The declarations `slotPerm_one`, `slotPerm_mul`, and `slotPerm_apply` establish the representation laws, `slotRep` packages this action, and `symmetrize n k q` averages over permutations of the first $q$ slots.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Tensor.Symmetrization
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev Coord (n k : ℕ) : Type := EuclideanSpace ℝ (Fin k → Fin n)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Theorems in source order:
--
--   - [`card_slots`](https://prove2.me/theorems/bb7f2252-e4b8-450e-8add-eea118a83e46)
--   - [`norm_le_four_pow_mul_norm_symmetrize`](https://prove2.me/theorems/f0e3d670-24f7-4ef8-927b-cc5e41de1898)
--   - [`sum_sq_blocks_le`](https://prove2.me/theorems/4c57808a-480e-483b-b687-b1b06f6ba0cf)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean) · `FunctionalInequalities.Analysis.Tensor.Coordinate` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean#L22-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coordinate`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Finset
namespace FunctionalInequalities
namespace Analysis
namespace Tensor
/-- Real tensors with `k` indices, each ranging over `Fin n`, as a Euclidean space: the norm is the
Hilbert–Schmidt norm `|A| = (∑_{i₁,…,i_k} A_{i₁…i_k}²)^{1/2}` of BKL Section 2. -/
abbrev Coord (n k : ℕ) : Type := EuclideanSpace ℝ (Fin k → Fin n)
/-- The positions `a ≤ p < b` among the `k` index positions. -/
def slots (k a b : ℕ) : Finset (Fin k) :=
  univ.filter fun p => a ≤ p.val ∧ p.val < b
/-- Permuting the index positions of a tensor: `(slotPerm σ A) i = A (i ∘ σ)`. -/
def slotPerm (n k : ℕ) (σ : Equiv.Perm (Fin k)) : Coord n k ≃ₗᵢ[ℝ] Coord n k :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.arrowCongr σ (Equiv.refl (Fin n)))
theorem slotPerm_apply (n k : ℕ) (σ : Equiv.Perm (Fin k)) (A : Coord n k) (i : Fin k → Fin n) :
    slotPerm n k σ A i = A (i ∘ σ) := by
    simp [slotPerm, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', Equiv.arrowCongr, Function.comp_def]
theorem slotPerm_one (n k : ℕ) : slotPerm n k 1 = 1 := by
    apply LinearIsometryEquiv.ext
    intro A
    apply PiLp.ext
    intro i
    rw [slotPerm_apply]
    simp
theorem slotPerm_mul (n k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    slotPerm n k (σ * τ) = slotPerm n k σ * slotPerm n k τ := by
    ext A i
    simp [slotPerm_apply, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      Function.comp_assoc]
/-- The orthogonal representation of `Perm (Fin k)` on tensors with `k` indices by permutation of
index positions. -/
def slotRep (n k : ℕ) : Equiv.Perm (Fin k) →* (Coord n k ≃ₗᵢ[ℝ] Coord n k) where
  toFun := slotPerm n k
  map_one' := slotPerm_one n k
  map_mul' := slotPerm_mul n k
/-- `S_q A`: the average of `A` over all permutations of its first `q` indices. -/
def symmetrize (n k q : ℕ) (A : Coord n k) : Coord n k :=
  blockAverage (slotRep n k) (slots k 0 q) A
end Tensor
end Analysis
end FunctionalInequalities


