-- Prove2me | Definitions.Def_LiqPremiaEq_IsHp
-- name    : LiqPremiaEq_IsHp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:07.58155+00:00
-- url     : https://prove2.me/theorems/9dab7d63-fb23-4db9-a6e3-f64d4f47b0d3
-- title:
--   The spaces $\mathbb H^p$ and $\mathcal S^p$ of processes on $[0,T]$
-- statement:
--   For $p\ge1$, $\mathbb H^p(\mathbb R^{m\times n})$ is the set of progressively measurable processes $X=(X_t)_{t\in[0,T]}$ with
--
--   $$\mathbb E\Big[\Big(\int_0^T\|X_t\|^2\,dt\Big)^{p/2}\Big]<\infty,$$
--
--   with $\|\cdot\|$ the Frobenius norm, and $\mathcal S^p(\mathbb R^m)$ is the set of progressively measurable processes with continuous paths such that $\sup_{0\le t\le T}\|X_t\|\in L^p$.
--
--   The forward-backward system of Lemma 4.2 is posed in these spaces, and admissible trading rates are the elements of $\mathbb H^4(\mathbb R^K)$.
--
--   **Formalization Note** Processes are indexed by $\mathbb R_{\ge0}$ and progressive measurability is asked of the process stopped at $T$; moments are lower Lebesgue integrals in $[0,\infty]$, so no junk values occur. Matrix-valued processes are read through their entries (`IsHpMat`). In $\mathcal S^p$ path continuity on $[0,T]$ is required almost surely.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Notation, p.3

import Mathlib
import Definitions.Def_LiqPremiaEq_opNorm

open MeasureTheory
open scoped NNReal ENNReal

namespace LiqPremiaEq

/-- The space `Hᵖ(ℝ^ι)` on `[0, T]`: `X` is progressively measurable on `[0, T]` and
`E[(∫₀ᵀ ‖X_t‖² dt)^{p/2}] < ∞`, with `‖·‖` the Frobenius (Euclidean) norm.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Notation, p.3.

**Formalization Note** Processes are indexed by `ℝ≥0`; only `[0, T]` matters, so progressive
measurability is asked of the process stopped at `T`, `t ↦ X (min t T)`. The integrals are lower
Lebesgue integrals in `ℝ≥0∞` (no junk values); `‖X_t‖²` is `∑ᵢ (X_t)ᵢ²`, and the time integral is
over `[0, T] ⊂ ℝ`, as in `Peng1990.SMP.L2F`. -/
def IsHp {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (p : ℝ)
    (X : ℝ≥0 → Ω → ι → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 (fun t ω => X (min t T) ω) ∧
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (∑ i, X s.toNNReal ω i ^ 2)) ^ (p / 2) ∂P < ⊤

/-- The space `Hᵖ(ℝ^{m×n})` of matrix-valued processes: the entries, read as a vector indexed
by `m × n`, form an `Hᵖ` process (the Frobenius norm of a matrix is the Euclidean norm of its
entries).
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Notation, p.3. -/
def IsHpMat {Ω : Type*} [mΩ : MeasurableSpace Ω] {m n : Type*} [Fintype m] [Fintype n]
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (p : ℝ)
    (X : ℝ≥0 → Ω → Matrix m n ℝ) : Prop :=
  IsHp 𝓕 P T p (fun t ω (q : m × n) => X t ω q.1 q.2)

/-- The space `Sᵖ(ℝ^ι)` on `[0, T]`: `X` is progressively measurable, has continuous paths on
`[0, T]`, and `sup_{0 ≤ t ≤ T} ‖X_t‖ ∈ Lᵖ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Notation, p.3.

**Formalization Note** Progressive measurability is asked of the process stopped at `T`; path
continuity on `[0, T]` is required for every `ω`, as printed ("with continuous
paths"); the moment is a lower Lebesgue integral of
the `ℝ≥0∞`-valued supremum of the Frobenius norm. -/
def IsSp {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (p : ℝ)
    (X : ℝ≥0 → Ω → ι → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 (fun t ω => X (min t T) ω) ∧
    (∀ ω, ContinuousOn (fun t => X t ω) (Set.Iic T)) ∧
    ∫⁻ ω, (⨆ t ∈ Set.Iic T, ENNReal.ofReal (frobVec (X t ω))) ^ p ∂P < ⊤

end LiqPremiaEq


