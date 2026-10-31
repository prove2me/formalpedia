-- Prove2me | Definitions.Def_IndefPOMFG_Space
-- name    : IndefPOMFG_Space
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:55.589476+00:00
-- url     : https://prove2.me/theorems/e4f7872b-cdf1-418b-80c7-8fc1904cc854
-- title:
--   Probability space, noises, filtrations and admissibility notions
-- statement:
--   A probability space $(\Omega,\mathcal F,\mathbb P)$ carries a standard Brownian motion of dimension $1+2Nd$, whose coordinates are the one-dimensional **common noise** $W^0$ and, for each agent $1\le i\le N$, the $d$-dimensional **individual noises** $W^i$ and $\bar W^i$; all $2N+1$ are independent. The full-information filtration is $\mathcal F_t=\sigma\{W^0_s,W^i_s,\bar W^i_s;\ 1\le i\le N,\ s\le t\}$.
--
--   The module provides: the diffusion coefficients of an equation of agent $i$ (a coefficient for $dW^0$, matrices for $dW^i$ and $d\bar W^i$, zero on the other agents' noises); **observation σ-algebras** $\sigma\{Z_s;\ 0\le s\le t\}$ of a process $Z$, augmented by the null sets; adaptedness on $[0,T]$; $\mathbb E[\sup_{t\le T}|u_t|^2]$ and $\mathbb E\int_0^T|u_t|^2dt$ in $[0,\infty]$; **control processes** (progressively measurable with $\mathbb E\sup_{t\le T}|u_t|^2<\infty$); the space $S^2_{\mathcal F}$; and equality $dt\otimes d\mathbb P$-a.e.
--
--   **Formalization Note** The filtration is the natural filtration of the Brownian motion (`Peng1990.SMP.brownianFiltration`), not augmented; observation σ-algebras are augmented so that they do not depend on the version of the processes generating them.
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, §2.1 p.1 (probability space), §2.3 p.5 (L²_𝓕, S²_𝓕), §3 p.6

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

set_option warn.classDefReducibility false

namespace IndefPOMFG

/-- The number of scalar Brownian coordinates of the large-population system: `1` for the common
noise `W⁰` and `d` for each of the `2N` individual noises `Wⁱ, W̄ⁱ`. -/
abbrev nK (N d : ℕ) : ℕ := 1 + (N * d + N * d)

/-- Labels of the Brownian coordinates: `inl ()` is `W⁰`, `inr (inl (i, k))` is the `k`-th
coordinate of `Wⁱ`, `inr (inr (i, k))` is the `k`-th coordinate of `W̄ⁱ`. -/
abbrev NoiseIdx (N d : ℕ) : Type := Unit ⊕ ((Fin N × Fin d) ⊕ (Fin N × Fin d))

/-- The enumeration of the labels by `Fin (nK N d)`. -/
def idxEquiv (N d : ℕ) : NoiseIdx N d ≃ Fin (nK N d) :=
  (Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1))
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans
    finSumFinEquiv

/-- The probability space of the large-population system (p.1): a probability measure `P` and a
standard Brownian motion `B` of dimension `1 + 2Nd` whose coordinates are the 1-dimensional
common noise `W⁰` and the `2N` independent `d`-dimensional individual noises `Wⁱ, W̄ⁱ`,
`1 ≤ i ≤ N` (see `W0`, `Wi`, `Wbi`). Chen–Nie–Wu, arXiv:2508.01568v1, §2.1, p.1.

**Formalization Note** One standard Brownian motion of dimension `1 + 2Nd`
(`Peng1990.SMP.IsStdBrownian`: independent real Brownian coordinates) is exactly a family of
`2N + 1` mutually independent standard Brownian motions of the stated dimensions. -/
structure Space (N d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  prob : IsProbabilityMeasure P
  B : ℝ≥0 → Ω → Fin (nK N d) → ℝ
  hB : IsStdBrownian P B

variable {N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The full-information filtration `𝓕_t = σ{Wⁱ_s, W̄ⁱ_s, W⁰_s; 1 ≤ i ≤ N, s ≤ t}` (p.1).

**Formalization Note** The natural filtration of all noises, not augmented by null sets
(`Peng1990.SMP.brownianFiltration`); adapted processes of the augmented filtration have
modifications adapted to this one, and every quantity of the paper is an expectation. -/
noncomputable def Space.filt (Sp : Space N d Ω) : Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  brownianFiltration Sp.hB

/-- The common noise `W⁰` (1-dimensional). -/
def Space.W0 (Sp : Space N d Ω) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => Sp.B t ω (idxEquiv N d (Sum.inl ()))

/-- The individual noise `Wⁱ` of agent `i` (`d`-dimensional). -/
def Space.Wi (Sp : Space N d Ω) (i : Fin N) : ℝ≥0 → Ω → Fin d → ℝ :=
  fun t ω k => Sp.B t ω (idxEquiv N d (Sum.inr (Sum.inl (i, k))))

/-- The individual noise `W̄ⁱ` of agent `i` (`d`-dimensional). -/
def Space.Wbi (Sp : Space N d Ω) (i : Fin N) : ℝ≥0 → Ω → Fin d → ℝ :=
  fun t ω k => Sp.B t ω (idxEquiv N d (Sum.inr (Sum.inr (i, k))))

/-- The diffusion coefficients of an equation of agent `i`, written against all `1 + 2Nd`
Brownian coordinates: `c0` multiplies `dW⁰`, the `k`-th column of `cW` multiplies `dWⁱ_k`, the
`k`-th column of `cWb` multiplies `dW̄ⁱ_k`, and the coordinates of the other agents carry `0`.
So `SolvesSDE … (agentDiff i c0 cW cWb)` is the equation
`… + c0 dW⁰ + cW dWⁱ + cWb dW̄ⁱ`. -/
def agentDiff {k : ℕ} (i : Fin N) (c0 : ℝ≥0 → Ω → (Fin k → ℝ) → (Fin k → ℝ))
    (cW cWb : ℝ≥0 → Ω → Matrix (Fin k) (Fin d) ℝ) :
    Fin (nK N d) → ℝ≥0 → Ω → (Fin k → ℝ) → (Fin k → ℝ) :=
  fun a s ω z =>
    match (idxEquiv N d).symm a with
    | Sum.inl _ => c0 s ω z
    | Sum.inr (Sum.inl jl) => if jl.1 = i then (fun r => cW s ω r jl.2) else 0
    | Sum.inr (Sum.inr jl) => if jl.1 = i then (fun r => cWb s ω r jl.2) else 0

/-- Diffusion coefficients of an equation driven by the common noise only: `c0 dW⁰`. -/
def w0Diff {k : ℕ} (c0 : ℝ≥0 → Ω → (Fin k → ℝ) → (Fin k → ℝ)) :
    Fin (nK N d) → ℝ≥0 → Ω → (Fin k → ℝ) → (Fin k → ℝ) :=
  fun a s ω z =>
    match (idxEquiv N d).symm a with
    | Sum.inl _ => c0 s ω z
    | Sum.inr _ => 0

/-- The σ-algebra generated by the measurable `P`-null sets. -/
def nullAug (P : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {s | MeasurableSet s ∧ P s = 0}

/-- The observation σ-algebra `σ{Z_s; 0 ≤ s ≤ t}` of a process `Z`, augmented by the `P`-null
sets (used for `𝓕^{yⁱ}`, `𝓕^y`, `𝓕^{y⁰}`, `𝓕^θ`, `𝓕^{Yⁱ}`, `𝓕^{Y^{i,0}}`, pp.6–8).

**Formalization Note** The null-set augmentation makes the observation filtrations independent
of the version of the (a.s. unique) solution processes that generate them. -/
def obsSigma {β : Type*} [MeasurableSpace β] (P : Measure Ω) (Z : ℝ≥0 → Ω → β) (t : ℝ≥0) :
    MeasurableSpace Ω :=
  (⨆ (s : ℝ≥0) (_ : s ≤ t), MeasurableSpace.comap (Z s) ‹MeasurableSpace β›) ⊔ nullAug P

/-- `u` is adapted on `[0, T]` to the family of σ-algebras `𝒢`: `u_t` is `𝒢_t`-measurable for
every `t ∈ [0, T]`. -/
def AdaptedOn {E : Type*} [TopologicalSpace E] (𝒢 : ℝ≥0 → MeasurableSpace Ω) (T : ℝ≥0)
    (u : ℝ≥0 → Ω → E) : Prop :=
  ∀ t ≤ T, StronglyMeasurable[𝒢 t] (u t)

/-- `E[sup_{0 ≤ t ≤ T} |u_t|²]`, as an element of `[0, ∞]`. -/
noncomputable def supSq {k : ℕ} (Sp : Space N d Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → Fin k → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, ⨆ t ∈ Iic T, ENNReal.ofReal (u t ω ⬝ᵥ u t ω) ∂Sp.P

/-- `E ∫₀ᵀ |u_t|² dt`, as an element of `[0, ∞]`. -/
noncomputable def intSq {k : ℕ} (Sp : Space N d Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → Fin k → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (u s.toNNReal ω ⬝ᵥ u s.toNNReal ω) ∂volume ∂Sp.P

/-- A control process in the sense of pp.6–8: `u ∈ L²_𝓕([0, T]; ℝᵐ)` (progressively measurable for
the full filtration `𝓕`) with `E[sup_{0 ≤ t ≤ T} |u_t|²] < ∞`. -/
def IsCtrl {k : ℕ} (Sp : Space N d Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  IsStronglyProgressive Sp.filt u ∧ supSq Sp T u < ⊤

/-- `S²_𝓕([0, T]; ℝᵏ)` (p.5): `𝓕`-progressive, almost surely continuous on `[0, T]`, and
`E[sup_{0 ≤ t ≤ T} |φ_t|²] < ∞`. -/
def InS2 {k : ℕ} (Sp : Space N d Ω) (T : ℝ≥0) (φ : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  IsStronglyProgressive Sp.filt φ ∧ (∀ᵐ ω ∂Sp.P, ContinuousOn (fun t => φ t ω) (Iic T)) ∧
    supSq Sp T φ < ⊤

/-- Equality `dt ⊗ dP`-almost everywhere on `[0, T] × Ω`. -/
def AEEqTP {E : Type*} (Sp : Space N d Ω) (T : ℝ≥0) (u v : ℝ≥0 → Ω → E) : Prop :=
  ∀ᵐ p ∂((volume.restrict (Icc (0 : ℝ) T)).prod Sp.P), u p.1.toNNReal p.2 = v p.1.toNNReal p.2

end IndefPOMFG


