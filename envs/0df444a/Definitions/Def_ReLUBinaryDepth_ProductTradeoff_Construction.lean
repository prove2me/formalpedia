-- Prove2me | Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Construction
-- name    : ReLUBinaryDepth_ProductTradeoff_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:19.228613+00:00
-- url     : https://prove2.me/theorems/a6134da0-88b7-485c-b8e2-df58d71ed99a
-- title:
--   The unrolled two-unit product circuit
-- statement:
--   The circuit is constructed from $B$ and the coordinate constants, with $M=B^n$. It has $n$ hidden layers of two ReLU units each, followed by a single summation ReLU. At stage $i$, the two preactivations are
--   $$\theta_i(0)a(i)-Mx_i,\qquad \theta_i(1)a(i)-M(1-x_i).$$
--   Here $a(0)=1$ is supplied by constant biases. At later stages the preceding pair of actual gate outputs is summed by the incoming affine weights; no separate sum unit is inserted between stages. The final gate adds the last two values. When $n=0$, only the final gate remains, with bias 1. All unused weights are zero.
--
--   This is actual circuit data: evaluation uses the general affine/ReLU semantics. Equality with the recurrence or the product is a separate theorem, not a field of the construction.
-- source:
--   Neil Krishnan, Elchanan Mossel, STOC 2027 submission #1645 (October 2026), Lemma 2.2 and the paragraph following it, p. 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Product

namespace ReLUBinaryDepth.ProductTradeoff

noncomputable section

/-- At stage i>0, the accumulator is the sum of the preceding pair of gate outputs.
The i=0 branch uses the initial accumulator 1 as a constant bias. -/
def productStageGate {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ)
    (i : Fin n) (b : Bool) : AffineGate n where
  bias := (if i.val = 0 then θ i b else 0) - (if b then B ^ n else 0)
  inputWeight := fun j => if j = i then (if b then B ^ n else -(B ^ n)) else 0
  previousWeight := fun j =>
    if 0 < i.val ∧ (j = 2 * (i.val - 1) ∨ j = 2 * (i.val - 1) + 1)
    then θ i b else 0

/-- A real affine/ReLU circuit with n pairs of gates and a single final summation ReLU.
No product or recurrence identity is assumed in this definition. -/
def productNetwork {n : ℕ} (B : ℝ) (θ : Fin n → Bool → ℝ) : Network n where
  layers := List.ofFn (fun i : Fin n =>
    [productStageGate B θ i false, productStageGate B θ i true])
  output := {
    bias := if n = 0 then 1 else 0
    inputWeight := fun _ => 0
    previousWeight := fun j =>
      if 0 < n ∧ (j = 2 * (n - 1) ∨ j = 2 * (n - 1) + 1) then 1 else 0 }
  outputRelu := true

end
end ReLUBinaryDepth.ProductTradeoff


