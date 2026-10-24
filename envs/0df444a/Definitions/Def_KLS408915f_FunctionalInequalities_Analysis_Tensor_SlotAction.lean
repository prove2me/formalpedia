-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
-- name    : KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:53:34.762191+00:00
-- url     : https://prove2.me/theorems/58359763-4ee1-48ae-a024-baae62335f5a
-- title:
--   Coordinate tensors and matrix slot actions
-- statement:
--   An order-$r$ coordinate tensor is represented as a function $(\mathrm{Fin}\,r\to\mathrm{Fin}\,n)\to\mathbb{R}$. `inner T S` is its Euclidean coordinate inner product $\sum_J T_JS_J$; `actOn H s T` applies a matrix $H$ to the $s$-th tensor input, and `actSum H T` sums this action over all slots. These definitions use `Function.update` to preserve every tensor index except the selected one.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L19-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction`; the repository is private at upload time).

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


