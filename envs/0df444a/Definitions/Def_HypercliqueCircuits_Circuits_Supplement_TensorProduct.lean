-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Supplement_TensorProduct
-- name    : HypercliqueCircuits_Circuits_Supplement_TensorProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:10:42.828587+00:00
-- url     : https://prove2.me/theorems/cdc553c8-c41d-42b3-a321-8058fe43fec9
-- title:
--   Integer k-wise Boolean tensor product and its complete serialization
-- statement:
--   For $k$ Boolean tensors $A_0,\ldots,A_{k-1}$ of order $k$ and side length $n$, set
--
--   $$\operatorname{MP}_k(A)[i]=\sum_{\ell=0}^{n-1}\prod_{j=0}^{k-1} A_j[i_0,\ldots,i_{j-1},\ell,i_{j+1},\ldots,i_{k-1}].$$
--
--   Booleans are read as 0 and 1 and the sum and products take place in the natural numbers. In particular, outputs can exceed 1. The input is $n$ followed by tensor $j$ in increasing $j$ order and each tensor's entries in mixed-radix tuple order. The output contains all $n^k$ integer entries, including zero entries, in the same order. These definitions specify the full tensor computation required by Theorem 3.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, §4.2, p.25 (PDF 26), displayed definition of MP_k and Theorem 3

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Encoding

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

abbrev BooleanTensors (k n : ℕ) := Fin k → (Fin k → Fin n) → Bool

/-- The integer-valued k-wise product of order-k Boolean tensors, NOT its
Boolean support. The contracted index replaces coordinate j of tensor j.
Alman et al., §4.2, printed p.25 / PDF p.26. -/
def tensorProduct {k n : ℕ} (A : BooleanTensors k n) (i : Fin k → Fin n) : ℕ :=
  ∑ l : Fin n, ∏ j : Fin k, bit (A j (Function.update i j l))

/-- Tensor j first, then its n^k entries in mixed-radix order. -/
def tensorInput {k n : ℕ} (A : BooleanTensors k n) : List (Cell Empty) :=
  words (n :: (List.finRange k).flatMap (fun j =>
    (tuples k n).map (fun i => bit (A j i))))

/-- All n^k exact natural entries, including zeros, in the same tuple order. -/
def tensorOutput {k n : ℕ} (A : BooleanTensors k n) : List (Cell Empty) :=
  words ((tuples k n).map (tensorProduct A))

end HypercliqueCircuits.Circuits.Supplement


