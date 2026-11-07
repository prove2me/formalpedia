-- Prove2me | Definitions.Def_MultiSelectPandora_insertTop
-- name    : MultiSelectPandora_insertTop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:30.777931+00:00
-- url     : https://prove2.me/theorems/a49d01dc-0514-4593-b849-4774c73d4e12
-- title:
--   Keeping the top $k$ after inserting a value
-- statement:
--   For a sorted state $\alpha$ and a value $x$, this is the state
--   $$\mathrm{top}_k(\alpha\cup\{x\})=\mathrm{sort}(\alpha_1,\dots,\alpha_{k-1},\max\{\alpha_k,x\}).$$
--   Its $j$-th entry is $\max\{\alpha_j,\min\{x,\alpha_{j-1}\}\}$, with $\alpha_0=+\infty$.
--
--   **Formalization Note** The closed form avoids sorting. The verification file proves that the result is sorted and nonnegative and is a rearrangement of $(\alpha_1,\dots,\alpha_{k-1},\max\{\alpha_k,x\})$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.6 (PDF p.7); Table 1, p.7 (PDF p.8)

import Mathlib

namespace MultiSelectPandora

/-- **Keeping the top `k` after inserting a value**: `top_k(α ∪ {x}) = sort(α_1, …, α_{k−1}, max{α_k, x})`.
Beyhaghi–Han–Luqman manuscript, §2.2, p.6 (PDF p.7), and Table 1, p.7 (PDF p.8).

**Formalization Note.** On a sorted `α` the `j`-th entry of the result is `max(α_j, min(x, α_{j−1}))`, with `α_0 = +∞`. The
verification file proves that this is the sorted rearrangement of `(α_1, …, α_{k−1}, max{α_k, x})`. A negative `x` leaves
`α` unchanged, which matches the `k` zeros of `top_k`. -/
noncomputable def insertTop {k : ℕ} (α : Fin k → ℝ) (x : ℝ) : Fin k → ℝ := fun j =>
  if h : j.val = 0 then max (α j) x else max (α j) (min x (α ⟨j.val - 1, by omega⟩))

end MultiSelectPandora


