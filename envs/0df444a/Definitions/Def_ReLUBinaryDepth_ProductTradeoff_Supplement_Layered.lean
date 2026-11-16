-- Prove2me | Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Layered
-- name    : ReLUBinaryDepth_ProductTradeoff_Supplement_Layered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:43:44.934401+00:00
-- url     : https://prove2.me/theorems/717ac145-adda-4ee1-9cd1-c226ce046e91
-- title:
--   Layered ReLU networks, $B$-bit weights and Boolean computation
-- statement:
--   These predicates refine the published Boolean-input ReLU network class (hidden ReLU layers followed by one output gate, inputs $x\in\{0,1\}^n$) to the model of Section 3 of the paper.
--
--   1. **Strictly layered.** The units of hidden layer $0$ read the raw inputs. Every unit of hidden layer $k\ge 1$ has zero weight on every raw input and zero weight on every computed unit outside hidden layer $k-1$. The output gate reads only the last hidden layer, or the raw inputs when there is no hidden layer. Hidden layer $k$ occupies the positions $[o_{k-1},o_k)$ of the list of computed values, where $o_k$ is the total number of units in the first $k$ hidden layers.
--   2. **$B$-bit rational.** A real number $r$ is $B$-bit if $r=p/q$ with integers $p,q$, $q\neq 0$, $|p|<2^B$ and $|q|<2^B$.
--   3. **$B$-bit weights.** A network has $B$-bit weights if every bias, every raw-input weight, and every weight on an already computed value that a gate reads (positions below the length of the prefix it reads) is a $B$-bit rational.
--   4. **Boolean computation.** A network $N$ Boolean-computes $f:\{0,1\}^n\to\{0,1\}$ if for every $x$
--   $$\mathbf 1\!\left[N(x)>\tfrac12\right]=f(x).$$
--
--   These are the notions under which Lemma 3.1 and Theorem 3.2 are stated.
--
--   **Formalization Note** Weights stored beyond the prefix a gate reads are never used and are not constrained. Layered networks with a ReLU output gate are the narrowest reading of the paper's Section 3 networks, whose proof wires gadget layers so that each layer reads only the previous one.
-- source:
--   Neil Krishnan, Elchanan Mossel, Depth Lower Bounds for ReLU Networks with Binary Inputs, STOC 2027 submission #1645 (October 2026), §3, standing definitions, PDF p. 6 = printed p. 6; layered wiring in the proof of Theorem 3.2, pp. 7–8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf (SHA-256 35accc05b120367e3d7a527b3b55383bc4a42c205bc78904f41eea6b2668555b)

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff

noncomputable section

/-- Number of hidden units in the first `k` hidden layers: the index at which hidden layer `k`
starts in the list `N.values x`, and the length of the prefix that layer `k` reads. -/
def layerOffset {n : ℕ} (N : Network n) (k : ℕ) : ℕ :=
  ((N.layers.take k).map List.length).sum

/-- **Strictly layered** network (§3): hidden layer `0` reads the raw inputs; every gate of hidden
layer `k ≥ 1` has zero input weights and reads only the units of hidden layer `k - 1`; the output gate
reads only the last hidden layer (or the raw inputs when there is no hidden layer). -/
def IsLayered {n : ℕ} (N : Network n) : Prop :=
  (∀ (k : ℕ) (hk : k < N.layers.length), 0 < k → ∀ g ∈ N.layers[k],
      (∀ i, g.inputWeight i = 0) ∧
      ∀ j, g.previousWeight j ≠ 0 → layerOffset N (k - 1) ≤ j ∧ j < layerOffset N k) ∧
  (0 < N.layers.length →
      (∀ i, N.output.inputWeight i = 0) ∧
      ∀ j, N.output.previousWeight j ≠ 0 →
        layerOffset N (N.layers.length - 1) ≤ j ∧ j < layerOffset N N.layers.length)

/-- `r` is a rational whose numerator and denominator have absolute value less than `2^B`. -/
def IsBitRat (B : ℕ) (r : ℝ) : Prop :=
  ∃ p q : ℤ, q ≠ 0 ∧ |p| < 2 ^ B ∧ |q| < 2 ^ B ∧ r = (p : ℝ) / (q : ℝ)

/-- A gate has `B`-bit weights, given the length `m` of the prefix of earlier values it reads:
its bias, every raw-input weight and every weight on an earlier value it reads is `B`-bit. -/
def AffineGate.HasBitWeights {n : ℕ} (B m : ℕ) (g : AffineGate n) : Prop :=
  IsBitRat B g.bias ∧ (∀ i, IsBitRat B (g.inputWeight i)) ∧ ∀ j < m, IsBitRat B (g.previousWeight j)

/-- **`B`-bit weights** (§3, p. 6): every weight and bias of the network is `B`-bit. -/
def HasBitWeights {n : ℕ} (B : ℕ) (N : Network n) : Prop :=
  (∀ (k : ℕ) (hk : k < N.layers.length), ∀ g ∈ N.layers[k],
      AffineGate.HasBitWeights B (layerOffset N k) g) ∧
  AffineGate.HasBitWeights B (layerOffset N N.layers.length) N.output

/-- **Boolean computation** (§3, p. 6): `1[N(x) > 1/2] = f(x)` for every `x ∈ {0,1}^n`. -/
def BoolComputes {n : ℕ} (N : Network n) (f : Cube n → Bool) : Prop :=
  ∀ x, (1 / 2 < N.eval x ↔ f x = true)

end
end ReLUBinaryDepth.ProductTradeoff.Supplement


