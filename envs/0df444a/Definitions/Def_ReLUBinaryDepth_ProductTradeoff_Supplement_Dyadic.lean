-- Prove2me | Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Dyadic
-- name    : ReLUBinaryDepth_ProductTradeoff_Supplement_Dyadic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:44:49.933198+00:00
-- url     : https://prove2.me/theorems/7469e7aa-be82-4778-a48e-ac24b2ff094d
-- title:
--   Binary fixed-point value of a circuit output
-- statement:
--   For output bits $b_0,\dots,b_{R-1}\in\{0,1\}$ and a number $F$ of fractional bits, the value read off is
--   $$\mathrm{val}_F(b)=\frac{\sum_{r=0}^{R-1} b_r\,2^r}{2^F}.$$
--   Every such value is a nonnegative dyadic rational, and every nonnegative dyadic rational arises for suitable $R$, $F$ and $b$. This is how the circuits of Theorem 1.2 output their nonnegative dyadic rational $\widehat P(x)$.
-- source:
--   Neil Krishnan, Elchanan Mossel, Depth Lower Bounds for ReLU Networks with Binary Inputs, STOC 2027 submission #1645 (October 2026), Theorem 1.2 and the definition of dyadic rational preceding it, PDF p. 3 = printed p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf (SHA-256 35accc05b120367e3d7a527b3b55383bc4a42c205bc78904f41eea6b2668555b)

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff

noncomputable section

/-- Binary fixed-point reading of `R` output bits with `F` fractional bits:
`(∑_{r<R} b_r 2^r) / 2^F`, a nonnegative dyadic rational. -/
def dyadicValue {R : ℕ} (F : ℕ) (bits : Fin R → Bool) : ℝ :=
  (∑ r : Fin R, bit (bits r) * (2 : ℝ) ^ (r : ℕ)) / (2 : ℝ) ^ F

end
end ReLUBinaryDepth.ProductTradeoff.Supplement


