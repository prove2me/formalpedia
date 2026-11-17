-- Prove2me | Definitions.Def_SigmoidWire_Supplement_IsDepth3Layered
-- name    : SigmoidWire_Supplement_IsDepth3Layered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:38:00.160042+00:00
-- url     : https://prove2.me/theorems/9ad8041e-cdf2-481b-8bd0-1c2b923df409
-- title:
--   Layered depth-three sigmoidal circuits of Theorems 5.10 and 5.18, and the fan-in of the bottom layer
-- statement:
--   Let $C$ be a sigmoidal circuit on $N$ inputs whose $s+d+1$ gates are listed in topological order. $C$ is a **layered depth-three circuit with $s$ bottom gates, $d$ middle gates and middle bound $W$** if
--
--   1. the **bottom layer**, gates $0,\dots,s-1$, reads only the input variables, with arbitrary real weights and biases;
--   2. the **middle layer**, gates $s,\dots,s+d-1$, reads the input variables and the bottom gates, and every weight and the bias of each middle gate lies in $[-W,W]$;
--   3. the **output gate**, gate $s+d$, reads only the middle gates, with weights in $[-W,W]$ and an arbitrary bias.
--
--   The **input fan-in** $w_j$ of a gate is the number of input variables it reads through a non-zero weight, and the **total fan-in of the bottom layer** is $w=\sum_{j<s}w_j$.
--
--   These are the circuits of the depth-three lower bounds for the generalized Andreev function: Theorem 5.10 bounds the number $s$ of bottom gates and Theorem 5.18 the total fan-in $w$.
--
--   **Formalization Note** A zero weight is an absent wire, so the output gate has fan-in at most $d$. The bottom layer's parameters and the output's bias are not bounded, as on the page; a middle gate may read input variables (p.30: "an affine function $\ell$ that collects the bias of $G$ and its wires from the (restricted) input variables").
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.10, p.24 (restated p.27) and Theorem 5.18, pp.30–31; proof of Proposition 5.17, p.30

import Mathlib
import Definitions.Def_SigmoidWire_Circuit

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **The layered depth-3 circuits of Theorems 5.10 and 5.18.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 5.10, p.24 (PDF p.26),
restated p.27 (PDF p.29), and Theorem 5.18, pp.30–31 (PDF pp.32–33): "C is a (2n)-input depth-3
sigmoidal circuit, where • the output gate is a sigmoidal gate with fan-in d and weights within
[−W, W]; • the middle layer consists of d sigmoidal gates with weights and biases within [−W, W];
• the bottom layer (i.e. closest to input variables) has s sigmoidal gates in total."

`IsDepth3Layered C s d W` says that the `C.size + 1 = s + d + 1` gates of `C` (in topological order)
are: gates `0, …, s − 1` (the **bottom layer**), which read only the inputs, with arbitrary real
weights and biases; gates `s, …, s + d − 1` (the **middle layer**), which read the inputs and the
bottom gates, every weight and the bias of each being in `[−W, W]`; and the output gate `s + d`,
which reads only the middle gates, with weights in `[−W, W]` and an arbitrary bias.

**Formalization Note.** A zero weight is an absent wire, so the output gate has fan-in at most `d`
(fan-in exactly `d` is the special case in which all its `d` weights are non-zero). The page bounds
neither the bottom layer's parameters (the proof compresses them by Lemma 5.13) nor the output's bias
(Lemma 5.14 allows any bias), and neither is bounded here. A middle gate may read input variables:
p.30 (PDF p.32), "an affine function ℓ that collects the bias of G and its wires from the
(restricted) input variables". -/
def IsDepth3Layered {N : ℕ} (C : Circuit N) (s d : ℕ) (W : ℝ) : Prop :=
  C.size = s + d ∧
  -- bottom layer: reads only the inputs
  (∀ j : Fin (C.size + 1), j.val < s → ∀ g : Fin j, C.weight j (Sum.inr g) = 0) ∧
  -- middle layer: reads inputs and bottom gates; weights and bias in [−W, W]
  (∀ j : Fin (C.size + 1), s ≤ j.val → j.val < s + d →
    (∀ g : Fin j, s ≤ g.val → C.weight j (Sum.inr g) = 0) ∧
    (∀ src : Fin N ⊕ Fin j, |C.weight j src| ≤ W) ∧ |C.bias j| ≤ W) ∧
  -- output gate: reads only middle gates; weights in [−W, W]
  (∀ i : Fin N, C.weight (Fin.last C.size) (Sum.inl i) = 0) ∧
  (∀ g : Fin (Fin.last C.size), g.val < s → C.weight (Fin.last C.size) (Sum.inr g) = 0) ∧
  (∀ src : Fin N ⊕ Fin (Fin.last C.size), |C.weight (Fin.last C.size) src| ≤ W)

open Classical in
/-- **Input fan-in of a gate**: the number of input variables it reads through a non-zero weight.
For a bottom-layer gate (which reads only inputs) this is its fan-in; Theorem 5.18 (p.31, PDF p.33)
bounds the total fan-in `w = Σ_j w_j` of the bottom layer. -/
noncomputable def inputFanIn {N : ℕ} (C : Circuit N) (j : Fin (C.size + 1)) : ℕ :=
  (Finset.univ.filter fun i : Fin N => C.weight j (Sum.inl i) ≠ 0).card

open Classical in
/-- **Total fan-in of the first `s` gates** (the bottom layer of a circuit with
`IsDepth3Layered C s d W`): `w = Σ_{j < s} w_j`, Theorem 5.18, p.31 (PDF p.33). -/
noncomputable def bottomWires {N : ℕ} (C : Circuit N) (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (C.size + 1) => j.val < s), inputFanIn C j

end SigmoidWire.Supplement


