-- Prove2me | Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network
-- name    : ReLUBinaryDepth_ProductTradeoff_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:05.963664+00:00
-- url     : https://prove2.me/theorems/1f575586-1d45-45e0-a27b-582cc39a8965
-- title:
--   Boolean-input real affine/ReLU circuits and rational output spans
-- statement:
--   A Boolean input is a vector $x\in\{0,1\}^n$. Each affine gate has an unrestricted real bias, one real weight per raw input, and real weights on the finite list of already computed values. Its preactivation is
--   $$b+\sum_i u_i x_i+\sum_j v_j z_j.$$
--   A network is a finite list of hidden layers followed by a single output gate. Every hidden unit applies $\operatorname{ReLU}(t)=\max(0,t)$ to its preactivation. A layer reads only raw inputs and values from strictly earlier layers. The output applies either ReLU or the identity, according to a fixed Boolean mode. Exact computation of $f$ means equality with $f(x)$ at every Boolean input. Depth counts the hidden layers and output layer; width is the maximum of their computed-unit counts, including the single output but excluding raw input terminals.
--
--   The output span is $\operatorname{span}_{\mathbb Q}\{f(x):x\in\{0,1\}^n\}$. A structural instance establishes finite dimensionality from the finite range alone. No path identity, product identity, span estimate or independence condition is stored in a network.
--
--   **Formalization Note** Empty hidden layers are allowed and counted. Gate weights beyond the length of the earlier-value list are ignored, so all accessed fan-ins are finite. The direct-input convention reads the unspecified source syntax using Lemma 2.2. Earlier-layer skip edges and an affine output broaden the competing class. These definitions are independent of the product family.
-- source:
--   Neil Krishnan, Elchanan Mossel, STOC 2027 submission #1645 (October 2026), §1.1 p. 2, Lemma 2.2 and its layer-count paragraph p. 4, Lemma 2.3 pp. 4–5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf

import Mathlib

namespace ReLUBinaryDepth.ProductTradeoff

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def relu (t : ℝ) : ℝ := max 0 t

/-- Only the finite prefix indexed by the already computed list is read. -/
structure AffineGate (n : ℕ) where
  bias : ℝ
  inputWeight : Fin n → ℝ
  previousWeight : ℕ → ℝ

def AffineGate.eval {n : ℕ} (g : AffineGate n) (x : Cube n) (v : List ℝ) : ℝ :=
  g.bias + (∑ i, g.inputWeight i * bit (x i)) +
    ∑ j : Fin v.length, g.previousWeight j.val * v[j]

/-- Hidden layers followed by one counted output gate. Inputs are not computed units.
All hidden units are ReLU gates; the final gate may be ReLU or affine. -/
structure Network (n : ℕ) where
  layers : List (List (AffineGate n))
  output : AffineGate n
  outputRelu : Bool

/-- Evaluate a whole layer from the old prefix, then append its values: no within-layer edges. -/
def Network.values {n : ℕ} (N : Network n) (x : Cube n) : List ℝ :=
  N.layers.foldl (fun v layer => v ++ layer.map (fun g => relu (g.eval x v))) []

def Network.eval {n : ℕ} (N : Network n) (x : Cube n) : ℝ :=
  let z := N.output.eval x (N.values x)
  if N.outputRelu then relu z else z

def Network.depth {n : ℕ} (N : Network n) : ℕ := N.layers.length + 1

def Network.width {n : ℕ} (N : Network n) : ℕ :=
  N.layers.foldl (fun w layer => max w layer.length) 1

def Network.Computes {n : ℕ} (N : Network n) (f : Cube n → ℝ) : Prop :=
  ∀ x, N.eval x = f x

def outputSpan {n : ℕ} (f : Cube n → ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.range f)

/-- Structural finite generation, independent of any network or dimension bound. -/
instance outputSpanFinite {n : ℕ} (f : Cube n → ℝ) : FiniteDimensional ℚ (outputSpan f) :=
  FiniteDimensional.span_of_finite ℚ (Set.finite_range f)

end
end ReLUBinaryDepth.ProductTradeoff


