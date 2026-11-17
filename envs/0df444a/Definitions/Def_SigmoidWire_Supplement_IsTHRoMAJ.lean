-- Prove2me | Definitions.Def_SigmoidWire_Supplement_IsTHRoMAJ
-- name    : SigmoidWire_Supplement_IsTHRoMAJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:41:55.841082+00:00
-- url     : https://prove2.me/theorems/f7c6fb45-29a7-4c35-992c-2d200678f290
-- title:
--   THR ∘ MAJ$_d$ circuits with MAJ weights in $\{-W,\dots,W\}$
-- statement:
--   A threshold circuit is a **THR ∘ MAJ$_d$ circuit with MAJ weights in $\{-W,\dots,W\}$** if
--
--   1. every gate other than the output is a MAJ gate: its weights are integers in $\{-W,\dots,W\}$ and its threshold is real;
--   2. the output gate is a THR gate (real weights and threshold) that reads only gates, not input variables;
--   3. its depth is at most $d+1$ (the MAJ gates are arranged in depth at most $d$).
--
--   THR ∘ MAJ is the case $d=1$: $f(x)=\mathbb I\big[\sum_{i=1}^m\alpha_iG_i(x)\ge\theta\big]$ with each $G_i(x)=\mathbb I[\langle a_i,x\rangle\ge b_i]$, $a_i\in\{-W,\dots,W\}^n$.
--
--   These are the circuits that small-integer-weight sigmoidal circuits with no separation simulate and are simulated by (Theorems 1.8 and 7.2).
--
--   **Formalization Note** The circuit need not be layered (the proof of Theorem 7.2 assumes this without loss of generality).
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.8 and its proof, pp.46–47; Theorem 7.2 and its proof, p.48

import Mathlib
import Definitions.Def_SigmoidWire_Circuit
import Definitions.Def_SigmoidWire_Supplement_IntWeightsLe

namespace SigmoidWire.Supplement

open SigmoidWire

/-- **THR ∘ MAJ_d circuits with MAJ weights in `{−W, …, W}`** (§7.1).

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), Theorem 1.8 and its proof,
pp.46–48 (PDF pp.48–50), and Theorem 7.2 with its proof, p.48 (PDF p.50). A THR ∘ MAJ circuit
computes `f(x) = I[Σ_{i=1}^m α_i G_i(x) ≥ θ]` with real `α_i, θ`, where each `G_i(x) = I[⟨a_i, x⟩ ≥ b_i]`
is a MAJ gate with `a_i ∈ {−W, …, W}^n`; in THR ∘ MAJ_d the MAJ gates are arranged in depth at most
`d`, a gate of layer `ℓ ≥ 2` computing `I[Σ_i c_i H_i(x) ≥ b]` over earlier MAJ gates `H_i`.

`IsTHRoMAJ C d W`, for `C` evaluated with threshold gates (`thrAct`): every gate other than the
output is a MAJ gate (all its weights integers in `[−W, W]`, real threshold), the output gate (a THR
gate: real weights and threshold) reads only gates, not inputs, and the depth is at most `d + 1`.
THR ∘ MAJ is the case `d = 1`.

**Formalization Note.** The circuit need not be layered (the proof of Theorem 7.2 assumes so
"without loss of generality"). Its size is `C.size + 1`, the number of gates. -/
def IsTHRoMAJ {n : ℕ} (C : Circuit n) (d W : ℕ) : Prop :=
  (∀ j : Fin (C.size + 1), j ≠ Fin.last C.size → IsIntGate C j W) ∧
  (∀ i : Fin n, C.weight (Fin.last C.size) (Sum.inl i) = 0) ∧
  C.depth ≤ d + 1

end SigmoidWire.Supplement


