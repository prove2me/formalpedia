-- Prove2me | Definitions.Def_SigmoidWire_Supplement_GateWeightsLe
-- name    : SigmoidWire_Supplement_GateWeightsLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:39:04.263146+00:00
-- url     : https://prove2.me/theorems/e91a9c6f-f018-46b6-85b5-73d45acc2f1f
-- title:
--   Gate-to-gate weights within $[-W,W]$ (the weights of Definition 5.27)
-- statement:
--   A sigmoidal circuit has **gate-to-gate weights within $[-W,W]$** if every weight $w_{uv}$ on a wire from a gate $u$ to a gate $v$ satisfies $|w_{uv}|\le W$. Weights on input variables and biases are not constrained.
--
--   In a polynomial-adjusted sigmoidal circuit (Definition 5.27) each gate computes $\mathrm{Sigmoid}\big(p_v(x)+\sum_{u\to v}w_{uv}G_u(x)\big)$ with $p_v$ a polynomial in the inputs with arbitrary real coefficients, and "its weights are the coefficients $w_{uv}$ of the wires between gates". A sigmoidal circuit is the degree-one case, so this condition is the weight bound under which the paper proves its average-sensitivity and parity-correlation bounds (Theorems 5.19 and 5.20). Every circuit with all weights and biases in $[-W,W]$ satisfies it.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Definition 5.27, p.34

import Mathlib
import Definitions.Def_SigmoidWire_Circuit

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **Gate-to-gate weights within `[−W, W]`** (the weights of a polynomial-adjusted circuit,
Definition 5.27).

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Definition 5.27, p.34
(PDF p.36): each gate computes `Sigmoid(p_v(x) + Σ_{u→v} w_uv G_u(x))` "for a multilinear polynomial
p_v of degree at most r in the input variables (with arbitrary real coefficients)", and "its weights
are the coefficients w_uv of the wires between gates". "In particular, a depth-d sigmoidal circuit
whose weights are within [−W, W] is a depth-d polynomial-adjusted sigmoidal circuit of degree 1
whose weights are within [−W, W]."

`GateWeightsLe C W`: every weight on a wire from a gate to a gate has absolute value at most `W`.

**Formalization Note.** Input weights and biases are not constrained (they form the degree-1
polynomial `p_v`). A circuit with `C.ParamsLe W` satisfies `GateWeightsLe C W`. -/
def GateWeightsLe {n : ℕ} (C : Circuit n) (W : ℝ) : Prop :=
  ∀ (j : Fin (C.size + 1)) (g : Fin j), |C.weight j (Sum.inr g)| ≤ W

end SigmoidWire.Supplement


