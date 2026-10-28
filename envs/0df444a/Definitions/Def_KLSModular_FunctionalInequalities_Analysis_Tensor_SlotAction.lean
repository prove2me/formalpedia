-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction
-- name    : KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:01:19.023984+00:00
-- url     : https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4
-- title:
--   Coordinate tensors and matrix slot actions
-- statement:
--   An order-$r$ coordinate tensor is represented as a function $(\mathrm{Fin}\,r\to\mathrm{Fin}\,n)\to\mathbb{R}$. `inner T S` is its Euclidean coordinate inner product $\sum_J T_JS_J$; `actOn H s T` applies a matrix $H$ to the $s$-th tensor input, and `actSum H T` sums this action over all slots. These definitions use `Function.update` to preserve every tensor index except the selected one.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def inner (T S : (Fin r → Fin n) → ℝ) : ℝ := ∑ J, T J * S J
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`slot_bound`](https://prove2.me/theorems/ce4763d5-d9d2-4ff2-890e-e23900cb107a)
--   - [`drift_expression_ge`](https://prove2.me/theorems/a395a5ad-1152-4611-ab50-eae8318965ce)
--   - [`actOn_mul`](https://prove2.me/theorems/cfa56bc5-17bf-4d9e-adde-cb98770df824)
--   - [`inner_actOn_left`](https://prove2.me/theorems/5abfdc6c-c268-4e15-8e06-33c59ea2d64e)
--   - [`inner_actSum_actSum`](https://prove2.me/theorems/af677909-39f3-405f-9380-dc4ed282eb33)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean) · `FunctionalInequalities.Analysis.Tensor.SlotAction` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L19-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction`; the repository is private at upload time).

import Mathlib

noncomputable section
open Matrix
namespace FunctionalInequalities
namespace Analysis
namespace CoordinateTensor
variable {n r : ℕ}
/-- The Euclidean inner product of two order-`r` coordinate tensors on `ℝⁿ`. -/
def inner (T S : (Fin r → Fin n) → ℝ) : ℝ := ∑ J, T J * S J
/-- `H^{(s)}`: the matrix `H` acting on the `s`-th input of an order-`r` tensor (BKL arXiv:2610.05474v1, p. 23). -/
def actOn (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun J => ∑ k, H (J s) k * T (Function.update J s k)
/-- `Σ_H = Σ_s H^{(s)}`. -/
def actSum (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin r → Fin n) → ℝ) : (Fin r → Fin n) → ℝ :=
  fun J => ∑ s, actOn H s T J
end CoordinateTensor
end Analysis
end FunctionalInequalities


