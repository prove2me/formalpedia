-- Prove2me | Definitions.Def_SigmoidWire_Supplement_IsDepth2Layered
-- name    : SigmoidWire_Supplement_IsDepth2Layered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:38:38.71636+00:00
-- url     : https://prove2.me/theorems/3034d8e3-de5c-4f32-b14d-0e6b362af101
-- title:
--   Depth-two sigmoidal circuits with $h$ bottom gates
-- statement:
--   A sigmoidal circuit on $n$ inputs is a **depth-two circuit with $h$ bottom gates** if it has $h+1$ gates, the bottom gates $0,\dots,h-1$ read only the input variables, and the output gate $h$ reads the bottom gates and possibly input variables directly. Its output is
--   $$\mathrm{Sigmoid}\Big(c_0+\sum_{j=1}^n u_jx_j+\sum_{i=1}^h v_i\,\mathrm{Sigmoid}\big(b_i+\textstyle\sum_{j}w_{ij}x_j\big)\Big).$$
--
--   This is the architecture of the weight upper bound of Theorem 6.1.
--
--   **Formalization Note** Weights and biases are arbitrary reals; a zero weight is an absent wire.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.1 and its proof, p.38

import Mathlib
import Definitions.Def_SigmoidWire_Circuit

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Depth-two circuits with `h` bottom gates (Theorem 6.1).**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 6.1 and its proof,
p.38 (PDF p.40): "a depth-2 sigmoidal circuit with h ≥ 1 gates in the bottom layer"; the proof writes
the output's pre-activation as `c(x) + Σ_{i=1}^h v_i σ(b_i + Σ_j w_ij x_j)` with
`c(x) = c_0 + Σ_j u_j x_j`, "where u_j is the weight of the direct wire from x_j to the output".

`IsDepth2Layered C h` says that `C` has `h + 1` gates, that gates `0, …, h − 1` (the bottom layer)
read only the inputs, and that the output gate `h` may read the bottom gates and the inputs.

**Formalization Note.** Weights and biases are arbitrary reals; a zero weight is an absent wire. -/
def IsDepth2Layered {n : ℕ} (C : Circuit n) (h : ℕ) : Prop :=
  C.size = h ∧ ∀ j : Fin (C.size + 1), j.val < h → ∀ g : Fin j, C.weight j (Sum.inr g) = 0

end SigmoidWire.Supplement


