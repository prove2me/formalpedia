-- Prove2me | Definitions.Def_GravesWillems_Serial_programP
-- name    : GravesWillems_Serial_programP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:16:48.679015+00:00
-- url     : https://prove2.me/theorems/fcf228a2-0d47-453a-808e-c65c2e4ac242
-- title:
--   Program $\mathbf P^*$: service constraints (A3), feasibility, objective, the vector (A6) and the base-stock transfer
-- statement:
--   Fix a serial system with $N$ stages, lead times $T_1, \dots, T_N \in \mathbb{N}$ and a demand bound $D : \mathbb{N} \to \mathbb{R}$, where $D(\tau)$ is the maximum possible end-item demand over $\tau$ periods. Write $S_i = T_1 + \dots + T_i$ (so $S_0 = 0$).
--
--   1. **Service constraints (A3).** Base stocks $B$ satisfy (A3) if
--   $$B_1 + B_2 + \dots + B_i \ge D(T_1 + T_2 + \dots + T_i), \qquad i = 1, \dots, N.$$
--   2. **Feasibility for $\mathbf P^*$.** $B$ is feasible if it satisfies (A3) and $B_i \ge 0$ for $i = 1, \dots, N$.
--   3. **Objective of $\mathbf P^*$.** Given holding costs $h_1, \dots, h_N$, a probability space carrying a random demand path $d$, and a period $t$, the objective is
--   $$\sum_{i=1}^N h_i B_i - \sum_{i=2}^N e_{i-1}\, E[Q_i(t)], \qquad e_{i-1} = h_{i-1} - h_i,$$
--   where $Q_i(t)$ is the backlog of the recursion (A1) under base stocks $B$ and $e_i$ is the echelon holding cost.
--   4. **The vector (A6).** $B_1 = D(T_1)$ and $B_i = D(T_1 + \dots + T_i) - D(T_1 + \dots + T_{i-1})$ for $i = 2, \dots, N$.
--   5. **Transfer.** For a stage $k$ and an amount $\Delta$, the vector $B^{**}$ with $B^{**}_i = B_i$ for $i \ne k, k+1$, $B^{**}_k = B_k - \Delta$ and $B^{**}_{k+1} = B_{k+1} + \Delta$.
--
--   These are the objects of the appendix's main Result: $\mathbf P^*$ chooses base stocks that guarantee 100% service to the external customer at minimum inventory holding cost, and the Result asserts that the binding vector (A6) is optimal.
--
--   **Formalization Note** The paper writes $E[Q_i]$ without a period because demand is stationary; here the objective is evaluated at a fixed period $t \in \mathbb{Z}$, and every theorem quantifies over all $t$. The expectation is the Bochner integral $\int Q_i(t)\, d\mu$ of the pathwise backlog. Base-stock vectors are functions $\mathbb{N} \to \mathbb{R}$; only indices $1, \dots, N$ are read by the constraints and the objective. The vector (A6) is defined piecewise as printed and is $0$ outside $\{1, \dots, N\}$.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, p. 81, Appendix, Eq. (A3), program P*, Eq. (A6), and the proof of the Result (definition of B**)

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
open MeasureTheory

namespace GravesWillems.Serial

/-- The service constraints (A3) of Graves–Willems 2000 (Appendix, p. 81):
`B₁ + ⋯ + Bᵢ ≥ D(T₁ + ⋯ + Tᵢ)` for `i = 1, …, N`. -/
def ServiceConstraints (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ i ∈ Finset.Icc 1 N, D (∑ m ∈ Finset.Icc 1 i, T m) ≤ ∑ m ∈ Finset.Icc 1 i, B m

/-- Feasibility for program `P*` (Appendix, p. 81): the constraints (A3) and `Bᵢ ≥ 0` for
`i = 1, …, N`. -/
def Feasible (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (B : ℕ → ℝ) : Prop :=
  ServiceConstraints N T D B ∧ ∀ i ∈ Finset.Icc 1 N, 0 ≤ B i

/-- The objective of program `P*` (Appendix, p. 81) at period `t`:
`Σ_{i=1}^N hᵢBᵢ − Σ_{i=2}^N e_{i−1} E[Qᵢ(t)]`, with echelon holding cost `e_{i−1} = h_{i−1} − hᵢ`
and the expectation taken over the random demand path `d ω` under `μ`. -/
noncomputable def objective {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (d : Ω → ℤ → ℝ)
    (N : ℕ) (T : ℕ → ℕ) (h : ℕ → ℝ) (B : ℕ → ℝ) (t : ℤ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N, h i * B i
    - ∑ i ∈ Finset.Icc 2 N, (h (i - 1) - h i) * ∫ ω, backlog N T B (d ω) i t ∂μ

/-- The base-stock vector (A6) (Appendix, p. 81): `B₁ = D(T₁)` and
`Bᵢ = D(T₁ + ⋯ + Tᵢ) − D(T₁ + ⋯ + T_{i−1})` for `i = 2, …, N`; `0` at every other index. -/
noncomputable def a6 (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 1 then D (T 1)
  else if i ∈ Finset.Icc 2 N then
    D (∑ m ∈ Finset.Icc 1 i, T m) - D (∑ m ∈ Finset.Icc 1 (i - 1), T m)
  else 0

/-- The transfer of the proof of the Result (Appendix, p. 81): `B**ᵢ = Bᵢ` for `i ≠ k, k + 1`,
`B**_k = B_k − Δ`, `B**_{k+1} = B_{k+1} + Δ`. -/
noncomputable def transfer (B : ℕ → ℝ) (k : ℕ) (Δ : ℝ) : ℕ → ℝ :=
  Function.update (Function.update B k (B k - Δ)) (k + 1) (B (k + 1) + Δ)

end GravesWillems.Serial


