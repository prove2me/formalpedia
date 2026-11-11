-- Prove2me | Definitions.Def_CalibratedMA_Randomized_Rounding
-- name    : CalibratedMA_Randomized_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:59.43112+00:00
-- url     : https://prove2.me/theorems/d59b98da-d24f-4b4f-8e49-b794558e8927
-- title:
--   Sections 3.2–3.4 — grid partitions, mean-preserving rounding Round_Γ, q_j, RoundErr and the lifted class A_{M,ρ}
-- statement:
--   Fix a grid increment $\rho>0$ such that $K=1/\rho$ is an integer, and let $\Lambda_\rho=\{0,\rho,2\rho,\dots,1\}=\{i/K: 0\le i\le K\}$. A **grid partition** is a sequence
--   $$\Gamma=(\gamma_0,\dots,\gamma_M),\qquad 0=\gamma_0<\gamma_1<\dots<\gamma_M=1,\qquad \gamma_j\in\Lambda_\rho;$$
--   $M$ is its number of intervals.
--
--   The **mean-preserving randomized rounding** $\mathrm{Round}_\Gamma(s)$ of $s\in[\gamma_j,\gamma_{j+1}]$, with $\Delta_j=\gamma_{j+1}-\gamma_j$, equals $\gamma_j$ with probability $(\gamma_{j+1}-s)/\Delta_j$ and $\gamma_{j+1}$ with probability $(s-\gamma_j)/\Delta_j$. For a test $h$ on the rounded values, its **lift** is $a_h(s)=\mathbb E[h(\mathrm{Round}_\Gamma(s))]$.
--
--   For the interval $I_j=(\gamma_j,\gamma_{j+1})$ and a distribution $\nu$ on $[0,1]$,
--   $$r_j(s)=\frac{(s-\gamma_j)(\gamma_{j+1}-s)}{\gamma_{j+1}-\gamma_j}\mathbf 1\{s\in I_j\},\qquad q_j(\nu,\Gamma)=\mathbb E_{S\sim\nu}[r_j(S)],$$
--   $$\mathrm{RoundErr}(\nu,\Gamma)=\sup_{h:\{\gamma_0,\dots,\gamma_M\}\to\{-1,1\}}\Big|\sum_{j=0}^{M-1}\big(h(\gamma_j)-h(\gamma_{j+1})\big)q_j(\nu,\Gamma)\Big|.$$
--
--   For an integer $M\ge1$, the **lifted test class** $\mathcal A_{M,\rho}$ consists of all lifts $a_h$, where $\Gamma=(\gamma_0,\dots,\gamma_L)$ ranges over the grid partitions with $L\le M$ intervals and $h$ over the sign-valued tests $\{\gamma_0,\dots,\gamma_L\}\to\{-1,1\}$.
--
--   These objects carry the coarsening step of the randomized upper bound: Algorithm 1 rounds its scores with $\mathrm{Round}_\Gamma$, and its online learner is run against $\mathcal A_{M,\rho}$.
--
--   **Formalization Note.** $\rho=1/K$ with $K\in\mathbb N$. A partition is a pair `(M, γ : ℕ → ℝ)` and `IsGridPartition K M γ` is the condition above. A score $s$ is first clamped to $[0,1]$ (scores are always in $[0,1]$). It is rounded on the interval with index the largest $j<M$ with $\gamma_j\le s$: at an interior partition point this gives the point mass at $s$, as either adjacent interval does in the source, and at $s=1$ it uses $j=M-1$. The probability weight is clamped to $[0,1]$, so `roundMeasure` is always a probability measure; on a grid partition the clamping changes nothing. `RoundErr` is a maximum over the finitely many sign assignments `Fin (M+1) → Bool`. `liftedClass K M` is a `Finset (ℝ → ℝ)` built from the partition-point index sets $S\subseteq\{0,\dots,K\}$ (with $0,K\in S$ and $|S|\le M+1$) and sign sets $T$ of grid indices; equal functions are counted once.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), pp. 13–14 and 17, Sections 3.2 (grid partition, Round_Γ), 3.2 (r_j, q_j, RoundErr), 3.4 (A_{M,ρ})

import Mathlib

open MeasureTheory

namespace CalibratedMA.Randomized

/-! # Sections 3.2–3.4 — grid partitions, mean-preserving rounding, rounding error, lifted tests

Lu, Noarov, Roth, *Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity*,
STOC 2027 submission #900, pp. 13–17.

The fine grid is `Λ_ρ = {0, ρ, 2ρ, …, 1}` with `1/ρ = K` a positive integer, so `ρ = 1/K`
and the grid points are `i / K`, `i = 0, …, K`.

A grid partition `Γ = (γ_0, …, γ_M)` is stored as its number of intervals `M` and the map
`γ : ℕ → ℝ` (only `γ 0, …, γ M` matter). -/

/-- `Γ = (γ_0, …, γ_M)` is a grid partition of the grid `Λ_{1/K}`:
`0 = γ_0 < γ_1 < ⋯ < γ_M = 1` and every `γ_j` is a grid point `i / K` with `0 ≤ i ≤ K`. -/
def IsGridPartition (K M : ℕ) (γ : ℕ → ℝ) : Prop :=
  γ 0 = 0 ∧ γ M = 1 ∧ (∀ j < M, γ j < γ (j + 1)) ∧
    ∀ j ≤ M, ∃ i : ℕ, i ≤ K ∧ γ j = (i : ℝ) / K

/-- Clamp a score to `[0,1]` (scores are always in `[0,1]`; this only fixes the junk values). -/
noncomputable def clamp01 (s : ℝ) : ℝ := max 0 (min 1 s)

/-- The index `j` of the partition interval `[γ_j, γ_{j+1}]` used to round `s ∈ [0,1]`:
the largest `j < M` with `γ_j ≤ s`. At an interior partition point `s = γ_j` this is `j`
(both adjacent intervals give the point mass at `s`), and at `s = 1` it is `M − 1`. -/
noncomputable def roundIndex (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) : ℕ :=
  ((Finset.range M).filter (fun j => γ j ≤ clamp01 s)).sup id

/-- The probability `(s − γ_j)/Δ_j` that `Round_Γ(s)` equals the right endpoint `γ_{j+1}`
(clamped to `[0,1]`, which changes nothing on a grid partition). -/
noncomputable def roundWeight (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) : ℝ :=
  let j := roundIndex M γ s
  max 0 (min 1 ((clamp01 s - γ j) / (γ (j + 1) - γ j)))

/-- The law of `Round_Γ(s)`: `γ_j` with probability `(γ_{j+1} − s)/Δ_j` and `γ_{j+1}` with
probability `(s − γ_j)/Δ_j`, for `s ∈ [γ_j, γ_{j+1}]`. Always a probability measure. -/
noncomputable def roundMeasure (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) : Measure ℝ :=
  let j := roundIndex M γ s
  let w := roundWeight M γ s
  ENNReal.ofReal (1 - w) • Measure.dirac (γ j) + ENNReal.ofReal w • Measure.dirac (γ (j + 1))

/-- The lift `a_h(s) = E[h(Round_Γ(s))]` of a test `h` on the rounded value. -/
noncomputable def liftTest (M : ℕ) (γ : ℕ → ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ p, h p ∂(roundMeasure M γ s)

/-- `r_j(s) = (s − γ_j)(γ_{j+1} − s)/(γ_{j+1} − γ_j) · 1{s ∈ (γ_j, γ_{j+1})}`. -/
noncomputable def rj (γ : ℕ → ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  if γ j < s ∧ s < γ (j + 1) then (s - γ j) * (γ (j + 1) - s) / (γ (j + 1) - γ j) else 0

/-- `q_j(ν, Γ) = E_{S∼ν}[r_j(S)]`. -/
noncomputable def qj (ν : Measure ℝ) (γ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∫ s, rj γ j s ∂ν

/-- The value `h(γ_j) ∈ {−1, 1}` of a sign assignment `σ` on the partition points
`γ_0, …, γ_M` (`true ↦ 1`, `false ↦ −1`). -/
def signVal {M : ℕ} (σ : Fin (M + 1) → Bool) (j : ℕ) : ℝ :=
  if hj : j < M + 1 then (if σ ⟨j, hj⟩ then 1 else -1) else 0

/-- `RoundErr(ν, Γ) = sup_{h : {γ_0,…,γ_M} → {−1,1}} |Σ_{j=0}^{M−1} (h(γ_j) − h(γ_{j+1})) q_j(ν, Γ)|`
(a maximum over the finitely many sign assignments). -/
noncomputable def RoundErr (ν : Measure ℝ) (M : ℕ) (γ : ℕ → ℝ) : ℝ :=
  ⨆ σ : Fin (M + 1) → Bool,
    |∑ j ∈ Finset.range M, (signVal σ j - signVal σ (j + 1)) * qj ν γ j|

/-- The grid partition with partition-point index set `S ⊆ {0, …, K}` (containing `0` and `K`):
`L = |S| − 1` intervals, `γ_j = i_j / K` where `i_0 < ⋯ < i_L` enumerate `S`. -/
noncomputable def partitionOfIndexSet (K : ℕ) (S : Finset ℕ) : ℕ × (ℕ → ℝ) :=
  (S.card - 1, fun j => ((S.sort (· ≤ ·)).getD j K : ℝ) / K)

open Classical in
/-- The sign-valued test on prediction values determined by a set `T` of grid indices:
`+1` at the grid points `i / K`, `i ∈ T`, and `−1` elsewhere. -/
noncomputable def signTest (K : ℕ) (T : Finset ℕ) (p : ℝ) : ℝ :=
  if ∃ i ∈ T, p = (i : ℝ) / K then 1 else -1

open Classical in
/-- The lifted test class `A_{M,ρ}` with `ρ = 1/K` (Section 3.4): all lifts
`a_h(s) = E[h(Round_Γ(s))]` over grid partitions `Γ` with `L ≤ M` intervals and points in
`Λ_ρ`, and sign-valued tests `h` on the partition points. As a `Finset` of functions,
repeated functions are counted once. -/
noncomputable def liftedClass (K M : ℕ) : Finset (ℝ → ℝ) :=
  let parts := (Finset.range (K + 1)).powerset.filter
    (fun S => 0 ∈ S ∧ K ∈ S ∧ S.card ≤ M + 1)
  (parts ×ˢ (Finset.range (K + 1)).powerset).image
    (fun ST => liftTest (partitionOfIndexSet K ST.1).1 (partitionOfIndexSet K ST.1).2
      (signTest K ST.2))

end CalibratedMA.Randomized


