-- Prove2me | Definitions.Def_SigmoidWire_Supplement_IntWeightsLe
-- name    : SigmoidWire_Supplement_IntWeightsLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:40:42.718537+00:00
-- url     : https://prove2.me/theorems/fee1a739-a031-4092-bd31-95dcfe196881
-- title:
--   Integer weights in $[-W,W]$, biases in $(-1,1)$, output weights in $\{\pm1\}$
-- statement:
--   Conditions on the parameters of a circuit, used in §7:
--
--   1. a gate has **integer weights in $[-W,W]$** if each of its weights is an integer of absolute value at most $W$ (its bias is unconstrained);
--   2. a circuit has **all weights integers in $[-W,W]$** if every gate does;
--   3. a circuit has **biases in $(-1,1)$** if every bias lies in the open interval $(-1,1)$;
--   4. a circuit's **output gate has weights in $\{\pm1\}$** if every wire into the output gate has weight $1$ or $-1$.
--
--   These describe the small-weight sigmoidal circuits of Theorems 1.8 and 7.2 and the output gates of Theorems 1.8, 1.9 and 7.3; a threshold gate with integer weights in $\{-W,\dots,W\}$ is a MAJ gate.
--
--   **Formalization Note** A zero weight is an absent wire, so the output-weight condition allows the weight $0$.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.8, p.46; Theorem 7.2, p.48; Theorem 1.9, p.48; Theorem 7.3, p.49

import Mathlib
import Definitions.Def_SigmoidWire_Circuit

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **A gate with integer weights in `[−W, W]`**: every weight of gate `j` (on inputs and on earlier
gates) is an integer of absolute value at most `W`; its bias is unconstrained.

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), §7.1, pp.46–48
(PDF pp.48–50): "all weights are integers in [−W, W]"; a MAJ gate is a threshold gate whose weights
are "taken from {−W, …, W}". -/
def IsIntGate {n : ℕ} (C : Circuit n) (j : Fin (C.size + 1)) (W : ℕ) : Prop :=
  ∀ src : Fin n ⊕ Fin j, ∃ k : ℤ, C.weight j src = k ∧ |k| ≤ W

/-- **All weights are integers in `[−W, W]`** (Theorems 1.8 and 7.2, pp.46, 48). -/
def IntWeightsLe {n : ℕ} (C : Circuit n) (W : ℕ) : Prop :=
  ∀ j : Fin (C.size + 1), IsIntGate C j W

/-- **All biases are real numbers in `(−1, 1)`** (Theorems 1.8 and 7.2, pp.46, 48). -/
def BiasesInUnit {n : ℕ} (C : Circuit n) : Prop :=
  ∀ j : Fin (C.size + 1), C.bias j ∈ Set.Ioo (-1 : ℝ) 1

/-- **The output gate has weights in `{±1}`** (Theorems 1.8, 1.9, 7.3, pp.46, 48, 49): every wire
into the output gate has weight `1` or `−1`.

**Formalization Note.** A zero weight is an absent wire, so the condition is that each weight of the
output gate is `0` (no wire) or `±1`. The output's bias is unconstrained. -/
def OutWeightsPM1 {n : ℕ} (C : Circuit n) : Prop :=
  ∀ src : Fin n ⊕ Fin (Fin.last C.size),
    C.weight (Fin.last C.size) src = 0 ∨ |C.weight (Fin.last C.size) src| = 1

end SigmoidWire.Supplement


