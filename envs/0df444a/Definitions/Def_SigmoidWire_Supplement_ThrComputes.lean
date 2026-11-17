-- Prove2me | Definitions.Def_SigmoidWire_Supplement_ThrComputes
-- name    : SigmoidWire_Supplement_ThrComputes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:41:21.982494+00:00
-- url     : https://prove2.me/theorems/df082935-89fb-4e0c-a95d-66a5a97de87c
-- title:
--   Threshold circuits and computing a Boolean function with them
-- statement:
--   A **threshold (THR) gate** with real weights $w$ and real bias $\beta$ computes
--   $$\mathrm{THR}(x)=\mathbb I\big[\langle w,x\rangle+\beta\ge 0\big]$$
--   (a gate $\mathbb I[\langle a,x\rangle\ge b]$ is the case $\beta=-b$). A **threshold circuit** is a circuit of such gates, each reading input variables and earlier gates; it **computes** $f:\{0,1\}^n\to\{0,1\}$ if its output gate outputs $f(x)$ at every $x$.
--
--   Theorems 1.8, 7.2, 1.9 and 7.3 simulate threshold circuits by sigmoidal circuits.
--
--   **Formalization Note** A threshold circuit is a sigmoidal-circuit skeleton (the published `SigmoidWire.Circuit`) evaluated with the activation $t\mapsto\mathbb I[t\ge0]$, so it shares the size (number of gates, output included) and the depth (measured at the output along non-zero weights) of sigmoidal circuits.
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), §6.1, p.37; §7, pp.46–49

import Mathlib
import Definitions.Def_SigmoidWire_bitR
import Definitions.Def_SigmoidWire_Circuit

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **The threshold activation** `t ↦ I[t ≥ 0]`, so that a `thrAct`-circuit is a threshold
circuit: gate `j` computes `I[Σ_i w_{j,i} x_i + Σ_{g<j} w_{j,g} G_g + β_j ≥ 0]`.

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), §6.1, p.37 (PDF p.39): "linear
threshold gates (i.e. THR(x) := I[⟨w, x⟩ + β ≥ 0])"; §7, pp.46–49 (PDF pp.48–51): a gate
`I[⟨a, x⟩ ≥ b]` is the case `β = −b`. -/
noncomputable def thrAct (t : ℝ) : ℝ := if 0 ≤ t then 1 else 0

/-- **A threshold circuit computes `f`**: `C`, evaluated with threshold gates, outputs `f(x)` (as `0`
or `1`) at every `x ∈ {0,1}^n`, §7, pp.46–49 (Li, Reichman, Williams, Wu, STOC 2027 submission).

**Formalization Note.** A threshold circuit is a `SigmoidWire.Circuit` (weights and biases)
evaluated with `thrAct`; its size `C.size + 1` is its number of gates, including the output, and its
depth is `C.depth` (measured at the output along non-zero weights). -/
def ThrComputes {n : ℕ} (C : Circuit n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, C.eval thrAct x = bitR (f x)

end SigmoidWire.Supplement


