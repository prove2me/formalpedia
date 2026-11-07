-- Prove2me | Definitions.Def_SigmoidWire_Circuit
-- name    : SigmoidWire_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:13.284488+00:00
-- url     : https://prove2.me/theorems/ef27a829-3d02-4ce2-8ad5-b3944b9f5d36
-- title:
--   $\sigma$-circuits: gates, values, wires and depth
-- statement:
--   A **$\sigma$-circuit** on $n$ inputs is a finite sequence of gates $0,1,\dots,s$ in topological order. Gate $j$ carries a real weight $w_{j,i}$ on each input $i$, a real weight $w_{j,g}$ on each earlier gate $g<j$, and a real bias $\theta_j$. For an activation $\sigma:\mathbb R\to\mathbb R$ and an input $x\in\{0,1\}^n$, the gate values are
--
--   $$
--   v_j(x)=\sigma\Bigl(\sum_i w_{j,i}x_i+\sum_{g<j}w_{j,g}v_g(x)+\theta_j\Bigr),
--   $$
--
--   and the output $C(x)$ is the value of the last gate. A **sigmoidal circuit** is the case $\sigma=\mathrm{Sigmoid}$, $\mathrm{Sigmoid}(x)=(1+e^{-x})^{-1}$.
--
--   The circuit measures are:
--
--   1. the number of **wires**, which is the number of non-zero weights over all gates (biases are not wires);
--   2. the **depth**: a gate has depth $1$ plus the largest depth of an earlier gate it reads through a non-zero weight, and the circuit's depth is that of its output gate;
--   3. "weights and biases within $[-W,W]$", meaning $|w|\le W$ and $|\theta|\le W$ for every weight and bias.
--
--   This is the model of every statement of the mission. It is not layered: a gate may read inputs and gates of any lower depth.
--
--   **Formalization Note** The argument of $\sigma$ at gate $j$ is exposed as `pre`, and at the output gate as `outPre`. A gate that the output does not read still contributes its wires to the count, but does not raise the depth.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), §3 Notation, p.14; wires §1.1, p.3

import Mathlib
import Definitions.Def_SigmoidWire_bitR

namespace SigmoidWire

/-- **σ-circuit on `n` inputs** (weights and biases only; the activation `σ` is supplied at
evaluation).

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), §3 Notation, p.14 (PDF p.16):
"a σ-circuit is a circuit with unbounded fan-in gates of form σ_{w,θ}(x) := σ(⟨w, x⟩ + θ)".

**Formalization Note.** The circuit has `size + 1 ≥ 1` gates, indexed by `Fin (size + 1)` in a
topological order. Gate `j` has a weight on every input `i : Fin n` (`Sum.inl i`) and on every
**earlier** gate `g < j` (`Sum.inr g`), and a bias `bias j`. A zero weight is an absent wire. The
output of the circuit is the last gate. Nothing forces the circuit to be layered: a gate may read
inputs and gates at any lower depth. -/
structure Circuit (n : ℕ) where
  /-- The number of gates minus one. -/
  size : ℕ
  /-- `weight j (Sum.inl i)` is the weight of input `i` in gate `j`; `weight j (Sum.inr g)` the
  weight of the earlier gate `g` in gate `j`. -/
  weight : (j : Fin (size + 1)) → (Fin n ⊕ Fin j) → ℝ
  /-- The bias of gate `j`. -/
  bias : Fin (size + 1) → ℝ

namespace Circuit

variable {n : ℕ}

/-- **Gate values.** `gateVal C σ x j = σ(Σ_i w_{j,i} x_i + Σ_{g<j} w_{j,g} · gateVal g + θ_j)`,
§3, p.14 (Li, Reichman, Williams, Wu, STOC 2027 submission). Defined by recursion on the gate index. -/
noncomputable def gateVal (C : Circuit n) (σ : ℝ → ℝ) (x : Fin n → Bool) :
    Fin (C.size + 1) → ℝ
  | j => σ ((∑ i : Fin n, C.weight j (Sum.inl i) * bitR (x i)) +
      (∑ g : Fin j, C.weight j (Sum.inr g) * gateVal C σ x ⟨g.val, lt_trans g.isLt j.isLt⟩) +
      C.bias j)
termination_by j => j.val
decreasing_by exact g.isLt

/-- **Pre-activation of gate `j`**: `⟨w_j, (x, earlier gate values)⟩ + θ_j`, so that
`gateVal C σ x j = σ (pre C σ x j)`, §3, p.14 (Li, Reichman, Williams, Wu, STOC 2027 submission). -/
noncomputable def pre (C : Circuit n) (σ : ℝ → ℝ) (x : Fin n → Bool) (j : Fin (C.size + 1)) : ℝ :=
  (∑ i : Fin n, C.weight j (Sum.inl i) * bitR (x i)) +
    (∑ g : Fin j, C.weight j (Sum.inr g) * C.gateVal σ x ⟨g.val, lt_trans g.isLt j.isLt⟩) +
    C.bias j

/-- **Output of the circuit**: the value `C(x)` of its last gate, §3, p.14 (Li, Reichman, Williams,
Wu, STOC 2027 submission). -/
noncomputable def eval (C : Circuit n) (σ : ℝ → ℝ) (x : Fin n → Bool) : ℝ :=
  C.gateVal σ x (Fin.last C.size)

/-- **Output pre-activation**: the argument of `σ` at the output gate, so that
`C.eval σ x = σ (C.outPre σ x)`. In the proof of Theorem 4.4 (p.20) this is
`Σ_i w_i σ_i(x) + ℓ(x)` (Li, Reichman, Williams, Wu, STOC 2027 submission). -/
noncomputable def outPre (C : Circuit n) (σ : ℝ → ℝ) (x : Fin n → Bool) : ℝ :=
  C.pre σ x (Fin.last C.size)

open Classical in
/-- **Number of wires**: the number of non-zero weights over all gates, inputs and earlier gates
alike. §1.1, p.3 (PDF p.5): "number of wires (i.e. non-zero parameters)" (Li, Reichman, Williams,
Wu, STOC 2027 submission).

**Formalization Note.** Biases are not wires (the count "n + n + n = O(n) wires" on p.19 counts
fan-ins only). Gates that the output does not read still contribute their wires. -/
noncomputable def wires (C : Circuit n) : ℕ :=
  ∑ j : Fin (C.size + 1), (Finset.univ.filter fun src : Fin n ⊕ Fin j => C.weight j src ≠ 0).card

open Classical in
/-- **Depth of a gate**: `1` plus the largest depth of an earlier gate it reads through a non-zero
weight (`1` if it reads inputs only). Inputs have depth `0`.

Li, Reichman, Williams, Wu, STOC 2027 submission (manuscript sha256 2d6ef7af…), §3, p.14. -/
noncomputable def gateDepth (C : Circuit n) : Fin (C.size + 1) → ℕ
  | j => (Finset.univ : Finset (Fin j)).sup (fun g =>
      if C.weight j (Sum.inr g) ≠ 0 then C.gateDepth ⟨g.val, lt_trans g.isLt j.isLt⟩ else 0) + 1
termination_by j => j.val
decreasing_by exact g.isLt

/-- **Depth of the circuit**: the depth of its output gate. "A depth-`d` circuit" is a circuit
with `C.depth ≤ d`.

Li, Reichman, Williams, Wu, STOC 2027 submission (manuscript sha256 2d6ef7af…), §3, p.14.

**Formalization Note.** Depth is measured at the output gate along non-zero weights; gates the
output does not read do not raise it. -/
noncomputable def depth (C : Circuit n) : ℕ := C.gateDepth (Fin.last C.size)

/-- **Weights and biases within `[−W, W]`**: every weight and every bias has absolute value at
most `W`. Theorem 4.4, p.19 (PDF p.21): "with weights and biases within [−W, W]" (Li, Reichman,
Williams, Wu, STOC 2027 submission). -/
def ParamsLe (C : Circuit n) (W : ℝ) : Prop :=
  (∀ (j : Fin (C.size + 1)) (src : Fin n ⊕ Fin j), |C.weight j src| ≤ W) ∧
    ∀ j : Fin (C.size + 1), |C.bias j| ≤ W

end Circuit

end SigmoidWire


