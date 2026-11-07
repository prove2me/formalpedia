-- Prove2me | Definitions.Def_ApproxGKR_E0
-- name    : ApproxGKR_E0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:01.069564+00:00
-- url     : https://prove2.me/theorems/674a1d7e-347e-4867-9dff-23417187ba15
-- title:
--   The backward error thresholds $t_{i,j}$, $E_i$ and $E_0$ of (C.13)–(C.15)
-- statement:
--   For $\Delta_0\ge0$ and $0<\alpha,\beta<1$, one backward sum-check step is $t\mapsto 7\Delta_0+h(t+\Delta_0)/\alpha$ (eq. (C.13)). The layer thresholds are defined backward from the input layer: $E_L=5\Delta_0$ and, at layer $i$,
--   $$t_{i,k_i}=(K+4)\Delta_0+\frac{K(E_{i+1}+\Delta_0)}{\beta},\qquad t_{i,j-1}=7\Delta_0+\frac{h(t_{i,j}+\Delta_0)}{\alpha}\ (j=k_i,\dots,1),\qquad E_i=t_{i,0}$$
--   (eqs. (C.14)–(C.15)). Soundness applies whenever the claimed output is off by more than $E_0$.
--
--   **Formalization Note** `scThr` iterates the sum-check step; `Eback s` is $E_{L-s}$ and `E0` is $E_0$.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.3, eq. (C.13), p.37; eqs. (C.14)–(C.15), p.38

import Mathlib
import Definitions.Def_ApproxGKR_LayeredCircuit

namespace ApproxGKR

/-- One backward sum-check step of (C.13)/(C.15): `t ↦ 7∆₀ + h(t + ∆₀)/α`. -/
noncomputable def scStep (h α Δ₀ : ℝ) (t : ℝ) : ℝ := 7 * Δ₀ + h * (t + Δ₀) / α

/-- The sum-check thresholds of eq. (C.13): starting from the terminal threshold `t_{n}`,
`n` backward steps `t_{j−1} = 7∆₀ + h(t_j + ∆₀)/α` give `t₀`.

Das, Gupta, Mondal, More (manuscript, sha256 78b2a36b…), Lemma C.3, eq. (C.13), p.37. -/
noncomputable def scThr (h α Δ₀ tn : ℝ) (n : ℕ) : ℝ := (scStep h α Δ₀)^[n] tn

/-- The backward layer thresholds of (C.14)–(C.15), indexed by the distance `s` from the input
layer: `Eback s = E_{L−s}`. `E_L = 5∆₀`; at layer `i`,
`t_{i,kᵢ} = (K + 4)∆₀ + K(E_{i+1} + ∆₀)/β`, `t_{i,j−1} = 7∆₀ + h(t_{i,j} + ∆₀)/α`, `Eᵢ = t_{i,0}`.

Das, Gupta, Mondal, More (manuscript, sha256 78b2a36b…), §C.3, eqs. (C.14)–(C.15), p.38. -/
noncomputable def Eback (C : LayeredCircuit) (K α β Δ₀ : ℝ) : ℕ → ℝ
  | 0 => 5 * Δ₀
  | s + 1 =>
      scThr (C.h : ℝ) α Δ₀ ((K + 4) * Δ₀ + K * (Eback C K α β Δ₀ s + Δ₀) / β)
        (C.ki (C.L - (s + 1)))

/-- The starting threshold `E₀` of (C.14)–(C.15) (p.38): soundness applies "whenever
`|y − C(x)| > E₀`" (p.39). -/
noncomputable def E0 (C : LayeredCircuit) (K α β Δ₀ : ℝ) : ℝ := Eback C K α β Δ₀ C.L

end ApproxGKR


