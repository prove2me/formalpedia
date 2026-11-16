-- Prove2me | Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_ThresholdCircuit
-- name    : ReLUBinaryDepth_ProductTradeoff_Supplement_ThresholdCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:44:17.904864+00:00
-- url     : https://prove2.me/theorems/1e46aa9c-f15b-426b-99b1-6ffb24c7a58e
-- title:
--   Real-weighted threshold circuits
-- statement:
--   A **linear threshold gate** on $n$ Boolean inputs has a real threshold $b$, a real weight $u_i$ for each raw input $x_i$, and real weights $v_j$ on values $y_j\in\{0,1\}$ of earlier gates. It outputs
--   $$\mathbf 1\!\left[\sum_i u_i x_i+\sum_j v_j y_j\ge b\right].$$
--   A **threshold circuit** is a list of layers of such gates followed by a single output gate; each gate may read the raw inputs and any gate of a strictly earlier layer (unbounded fan-in). The circuit computes $f$ if its output equals $f(x)$ at every $x\in\{0,1\}^n$. Its **depth** is the number of layers including the output layer, and its **size** is the number of gates including the output gate.
--
--   These are the circuits of Section 3, whose gates are "arbitrary (real-weighted) linear threshold functions". Constant-depth, polynomial-size families of them define $\mathrm{TC}^0$, and depth at most $d$ defines $\mathrm{TC}^0_d$.
--
--   **Formalization Note** Every circuit given as a DAG of depth $d$ can be leveled by gate depth into this form with the same depth and number of gates, so nothing is lost by the layered presentation.
-- source:
--   Neil Krishnan, Elchanan Mossel, Depth Lower Bounds for ReLU Networks with Binary Inputs, STOC 2027 submission #1645 (October 2026), §3, PDF pp. 6–7 = printed pp. 6–7 (definition of TC⁰ and TC⁰_d, p. 6; real-weighted gates and |Cₙ|, proof of Theorem 3.2, p. 7). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf (SHA-256 35accc05b120367e3d7a527b3b55383bc4a42c205bc78904f41eea6b2668555b)

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff

noncomputable section

/-- A real-weighted linear threshold gate. Only the finite prefix of earlier gate values indexed by
the already computed list is read. -/
structure ThresholdGate (n : ℕ) where
  threshold : ℝ
  inputWeight : Fin n → ℝ
  previousWeight : ℕ → ℝ

/-- The gate outputs `1` iff its weighted sum of the raw inputs and of the earlier gate values is at
least its threshold. -/
def ThresholdGate.eval {n : ℕ} (g : ThresholdGate n) (x : Cube n) (v : List Bool) : Bool :=
  decide (g.threshold ≤ (∑ i, g.inputWeight i * bit (x i)) +
    ∑ j : Fin v.length, g.previousWeight j.val * bit v[j])

/-- A threshold circuit with arbitrary real weights and unbounded fan-in: layers of gates, each
reading raw inputs and gates of strictly earlier layers, followed by one output gate. -/
structure RealThresholdCircuit (n : ℕ) where
  layers : List (List (ThresholdGate n))
  output : ThresholdGate n

/-- Evaluate a layer from the old prefix, then append its values. -/
def RealThresholdCircuit.values {n : ℕ} (C : RealThresholdCircuit n) (x : Cube n) : List Bool :=
  C.layers.foldl (fun v layer => v ++ layer.map (fun g => g.eval x v)) []

def RealThresholdCircuit.eval {n : ℕ} (C : RealThresholdCircuit n) (x : Cube n) : Bool :=
  C.output.eval x (C.values x)

/-- Depth: the number of gate layers, counting the output gate's layer. -/
def RealThresholdCircuit.depth {n : ℕ} (C : RealThresholdCircuit n) : ℕ := C.layers.length + 1

/-- Size: the number of gates, including the output gate. -/
def RealThresholdCircuit.size {n : ℕ} (C : RealThresholdCircuit n) : ℕ :=
  (C.layers.map List.length).sum + 1

def RealThresholdCircuit.Computes {n : ℕ} (C : RealThresholdCircuit n) (f : Cube n → Bool) :
    Prop :=
  ∀ x, C.eval x = f x

end
end ReLUBinaryDepth.ProductTradeoff.Supplement


