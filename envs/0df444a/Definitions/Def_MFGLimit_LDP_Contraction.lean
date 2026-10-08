-- Prove2me | Definitions.Def_MFGLimit_LDP_Contraction
-- name    : MFGLimit_LDP_Contraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:10.064408+00:00
-- url     : https://prove2.me/theorems/088871f6-e98a-4855-93e8-225eba7418c1
-- title:
--   §6.3, pp. 31–33 — P¹(ℝ^d × C^d_0) × C^{d₀}_0 with max(W₁, ‖·‖_∞), Wiener measure 𝕎, (Q̄^n, W) (6.12), the McKean–Vlasov map Φ
-- statement:
--   The objects of the contraction argument (§6.3).
--
--   $\mathbb R^d\times\mathcal C^d_0$ carries the norm $\max(|e|,\|w\|_\infty)$, and $\mathcal P^1(\mathbb R^d\times\mathcal C^d_0)\times\mathcal C^{d_0}_0$ the metric $\max(\mathcal W_1(\mathcal Q,\mathcal Q'),\|\phi-\phi'\|_\infty)$. $\mathbb W$ is the Wiener measure on $\mathcal C^d_0$. The pair
--   $$(\bar{\mathcal Q}^n,W)=\Big(\frac1n\sum_{i=1}^n\delta_{(\tilde X^i_0,B^i)},W\Big) \qquad (6.12)$$
--   is a random element of that space. For $(\mathcal Q,\phi)$ consider, on the canonical space $(e,w)$ of $\mathbb R^d\times\mathcal C^d_0$ with law $\mathcal Q$, the McKean–Vlasov equation
--   $$x_t=e+\int_0^t\tilde b(s,x_s,\mathcal Q\circ x_s^{-1})ds+\sigma w_t+\sigma_0\phi_t,\qquad t\in[0,T];$$
--   $\Phi(\mathcal Q,\phi)=(\mathcal Q\circ x_t^{-1})_{t\in[0,T]}$ is the flow of marginal laws of its solution.
--
--   **Formalization Note** The Wiener measure is characterized by its finite-dimensional distributions, those of a standard Brownian motion. The event $\{(\bar{\mathcal Q}^n,W)\in O\}$ reads the Brownian paths as elements of $\mathcal C^d_0$, $\mathcal C^{d_0}_0$ (on the null set where they are not continuous or not started at $0$ the event is empty). The paper asserts unique solvability of the McKean–Vlasov equation under Condition 6.3; the solution map is a datum `sol` satisfying the equation $\mathcal Q$-a.s. and a.e.-measurable in $(e,w)$. The common-noise paths are $d_0$-dimensional (the paper writes $\mathcal C^d_0$).
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 31–33, §6.3.1–§6.3.2, (6.12)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLimit_LDP_Model
import Definitions.Def_MFGLimit_LDP_PathSpace

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

variable {d d₀ : ℕ} {T : ℝ≥0}

/-- A point `(Q, φ)` of `P_1(ℝ^d × C^d_0) × C^{d₀}_0` (§6.3.1, p. 31): `ℝ^d × C^d_0` carries the norm
`max(|e|, ‖w‖_∞)`, `Q` lies in `P_1` of it, and `φ` is a `d₀`-dimensional path started at `0`. -/
structure QPhi (d d₀ : ℕ) (T : ℝ≥0) where
  Q : Measure (MFGLimit.Conc.E d × C0T d T)
  isP1 : MFGLimit.Conc.IsPp 1 Q
  φ : C0T d₀ T

/-- The metric `max(W_1(Q, Q'), ‖φ − φ'‖_∞)` on `P_1(ℝ^d × C^d_0) × C^{d₀}_0`. -/
noncomputable def Dqp (z z' : QPhi d d₀ T) : ℝ≥0∞ := max (Wp 1 z.Q z'.Q) ‖z.φ - z'.φ‖ₑ

/-- `𝕎` is the Wiener measure on `C^k_0`: a probability measure whose finite-dimensional
distributions (laws of `(w_{t_1}, …, w_{t_j})`, `t_i ∈ [0, T]`) are those of a standard
`k`-dimensional Brownian motion. -/
def IsWienerMeasure (k : ℕ) (T : ℝ≥0) (𝕎 : Measure (C0T k T)) : Prop :=
  IsProbabilityMeasure 𝕎 ∧
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (Z : ℝ≥0 → Ω' → Fin k → ℝ),
      IsProbabilityMeasure P' ∧ Peng1990.SMP.IsStdBrownian P' Z ∧
      ∀ (j : ℕ) (τ : Fin j → Set.Icc (0 : ℝ≥0) T),
        𝕎.map (fun (w : C0T k T) (i : Fin j) => (w : CPath k T) (τ i)) = P'.map (fun ω i => toE (Z (τ i) ω))

/-- The event `{(Q̄^n, W) ∈ O}`, `Q̄^n = (1/n) Σ_i δ_{(X₀^i, B^i)}` (6.12): the Brownian paths `B^i`
and `W` (continuous, started at `0`) read as elements of `C^d_0` and `C^{d₀}_0`. -/
def pairEvent {Ω : Type*} (W : ℝ≥0 → Ω → Fin d₀ → ℝ) (B : ℕ → ℝ≥0 → Ω → Fin d → ℝ)
    (X₀ : ℕ → Ω → MFGLimit.Conc.E d) (n : ℕ) (O : Set (QPhi d d₀ T)) : Set Ω :=
  {ω | ∃ z ∈ O, ∃ w : Fin n → C0T d T,
    (∀ i t, (w i : CPath d T) t = toE (B i.val t ω)) ∧
    (∀ t, (z.φ : CPath d₀ T) t = toE (W t ω)) ∧
    z.Q = empMeas (fun i => (X₀ i.val ω, w i))}

/-- `sol` is a solution map of the McKean–Vlasov equation of §6.3.2 (p. 33): for every
`(Q, φ) ∈ P_1(ℝ^d × C^d_0) × C^{d₀}_0`, on the canonical space `(e, w)` of `ℝ^d × C^d_0` with
the law `Q`, the path `x = sol(Q, φ)(e, w)` is a.e. measurable and solves, `Q`-a.s., for every
`t ∈ [0, T]`, `x_t = e + ∫₀ᵗ b̃(s, x_s, Q ∘ x_s^{-1}) ds + σ w_t + σ₀ φ_t`. -/
def IsMVSolutionMap (σ : Matrix (Fin d) (Fin d) ℝ) (σ₀ : Matrix (Fin d) (Fin d₀) ℝ)
    (btil : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d)
    (sol : Measure (MFGLimit.Conc.E d × C0T d T) → C0T d₀ T → MFGLimit.Conc.E d × C0T d T → CPath d T) : Prop :=
  ∀ (Q : Measure (MFGLimit.Conc.E d × C0T d T)) (φ : C0T d₀ T), MFGLimit.Conc.IsPp 1 Q →
    AEMeasurable (sol Q φ) Q ∧
      ∀ᵐ ew ∂Q, ∀ t : Set.Icc (0 : ℝ≥0) T,
        IntegrableOn (fun s : ℝ => btil s.toNNReal ((sol Q φ ew).atR s)
          (Q.map (fun ew' => (sol Q φ ew').atR s))) (Set.Icc 0 (t : ℝ)) ∧
        sol Q φ ew t = ew.1 + (∫ s in Set.Icc (0 : ℝ) t, btil s.toNNReal ((sol Q φ ew).atR s)
          (Q.map (fun ew' => (sol Q φ ew').atR s)))
          + matVec σ ((ew.2 : CPath d T) t) + matVec σ₀ ((φ : CPath d₀ T) t)

/-- `Φ(Q, φ) = (Q ∘ x_t^{-1})_{t ∈ [0, T]}`, the flow of marginal laws of the solution (p. 33). -/
noncomputable def PhiMap (sol : Measure (MFGLimit.Conc.E d × C0T d T) → C0T d₀ T → MFGLimit.Conc.E d × C0T d T → CPath d T)
    (z : QPhi d d₀ T) : Flow d T :=
  fun t => z.Q.map (fun ew => sol z.Q z.φ ew t)

end MFGLimit.LDP


