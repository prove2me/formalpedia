-- Prove2me | Definitions.Def_HighUncertHT_Game_Setting
-- name    : HighUncertHT_Game_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:33:36.158247+00:00
-- url     : https://prove2.me/theorems/77698b3a-7f70-4050-8286-32a598593dc8
-- title:
--   §2.1–§2.1.3, pp. 5–9 — uncertainty classes, moments, Assumptions 1–2, labelling (14), h¹µ¹ = 1
-- statement:
--   This file fixes the data of the multitype D/G/1 scheduling game of Atar, Castiel and Shadmi and its standing assumptions.
--
--   There are $L\ge 1$ job types. For a probability measure $\pi$ on $\mathbb R_+=[0,\infty)$ (a job-size distribution) write
--   $$
--   \xi^\pi=\int x\,\pi(dx),\qquad q^\pi=\tfrac12(\sigma^\pi)^2=\tfrac12\int (x-\xi^\pi)^2\,\pi(dx)
--   $$
--   for its mean and half variance. For the $n$-th system, type $\ell$ and a first-order service rate $\mu^\ell>0$, the **prelimit drift** of $\pi$ is $b^{\pi\ell n}=n^{1/2}(\xi^\pi-1/\mu^\ell)$, and the **prelimit drift–variance set** of a class $\Pi^{\ell n}$ is
--   $$
--   K^{\ell n}=\{(b^{\pi\ell n},q^\pi):\pi\in\Pi^{\ell n}\}\subset\mathbb R^2 .
--   $$
--
--   A **setting** consists of:
--
--   1. rates $\mu^\ell>0$ and holding costs $h^\ell>0$, $\ell=1,\dots,L$;
--   2. for each $n$ and $\ell$ an **uncertainty class** $\Pi^{\ell n}$: a nonempty set of probability measures on $\mathbb R_+$, closed for the topology of weak convergence;
--   3. (Assumption 1.1) $\sup_{n,\ell}\sup_{\pi\in\Pi^{\ell n}}\int x^4\,\pi(dx)<\infty$;
--   4. (Assumption 1.2) compact sets $K^\ell\subset\mathbb R\times(0,\infty)$ with $K^{\ell n}\to K^\ell$ in the Hausdorff distance as $n\to\infty$;
--   5. (Assumption 2, heavy traffic) $\sum_\ell (\mu^\ell)^{-1}=1$;
--   6. (labelling (14)) $h^1\mu^1\le h^2\mu^2\le\dots\le h^L\mu^L$, and the normalization $h^1\mu^1=1$.
--
--   These are the standing assumptions of the paper; every statement of the mission is made for an arbitrary setting.
--
--   **Formalization Note** Types are `Fin L`, 0-based: the paper's type $\ell$ is index $\ell-1$, and type 1 (the lowest-priority type) is `S.first`. A distribution is a `ProbabilityMeasure ℝ` with $\pi((-\infty,0))=0$; its topology is weak convergence (closedness there is equivalent to closedness in the space of measures on $\mathbb R_+$). The paper's systems are indexed by $n\ge1$; the class at index $0$ is not a paper object but is required to satisfy the same conditions (extend by $\Pi^{\ell0}:=\Pi^{\ell1}$), so that sequences of controls indexed by $\mathbb N$ exist. The fourth-moment bound is a lower Lebesgue integral, so it cannot hold by a junk value; it makes every mean and variance finite. The Hausdorff distance is the extended one (`hausdorffEDist`), so empty or unbounded sets are at distance $\infty$; the product metric on $\mathbb R^2$ is the max metric, equivalent to the Euclidean one.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, pp. 5–9, §2.1.2 (uncertainty classes), §2.1.3 (ξ^π, σ^π, q^π, Assumptions 1 and 2, labelling (14), normalization h¹µ¹ = 1)

import Mathlib

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-!
Atar, Castiel, Shadmi, *Scheduling in the High Uncertainty Heavy Traffic Regime*,
arXiv:2204.05733v1, §2.1.2–§2.1.3, pp. 6–9: job-size distributions, their moments, the prelimit
drift/variance sets `K^{ℓn}`, and the standing assumptions (Assumptions 1–2, labelling (14),
normalization `h¹μ¹ = 1`).

Types are `Fin L`, 0-based: the paper's type `ℓ` is index `ℓ - 1`; the paper's type 1 is index `0`.
A job-size distribution (a member of the paper's `𝒫`, the probability measures on `ℝ₊`) is a
`ProbabilityMeasure ℝ` giving mass `0` to `(-∞, 0)`; its topology is the topology of weak
convergence.
-/

/-- The mean `ξ^π = ∫ x π(dx)` of a job-size distribution (p. 8). Only evaluated on members of an
uncertainty class, which have a finite fourth moment, hence a finite mean. -/
noncomputable def mean (π : ProbabilityMeasure ℝ) : ℝ :=
  ∫ x, x ∂(π : Measure ℝ)

/-- The half variance `q^π = ½ (σ^π)²`, `(σ^π)² = ∫ (x - ξ^π)² π(dx)` (p. 8). -/
noncomputable def halfVar (π : ProbabilityMeasure ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x, (x - mean π) ^ 2 ∂(π : Measure ℝ)

/-- The prelimit drift `b^{πℓn} = n^{1/2} (ξ^π - 1/μ^ℓ)` of Assumption 1.2 (p. 8), for the type
whose first-order mean service time is `1/μℓ`. -/
noncomputable def drift (π : ProbabilityMeasure ℝ) (μℓ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt n * (mean π - 1 / μℓ)

/-- The set `K^{ℓn} = {(b^{πℓn}, q^π) : π ∈ Π^{ℓn}} ⊂ ℝ²` of Assumption 1.2 (p. 8), for an
uncertainty class `Πℓn` and the rate `μℓ`. -/
def prelimitSet (cl : Set (ProbabilityMeasure ℝ)) (μℓ : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  {p | ∃ π ∈ cl, p = (drift π μℓ n, halfVar π)}

/-- The data of the paper's model and its standing assumptions (pp. 6–9).

* `μ ℓ > 0`: the first-order service rates; `h ℓ > 0`: the holding costs (cost (4)).
* `cls n ℓ`: the uncertainty class `Π^{ℓn}` of type `ℓ` in the `n`-th system, a nonempty closed
  set of probability measures on `ℝ₊` (p. 6). The paper's systems are indexed by `n ≥ 1`; the
  class at index `n = 0` is not a paper object, it is only required to satisfy the same
  conditions (any model of the paper extends by `Π^{ℓ0} := Π^{ℓ1}`), so that sequences of
  controls indexed by `ℕ` exist.
* `moment4`: Assumption 1.1, `sup_{n,ℓ} sup_{π ∈ Π^{ℓn}} ∫ x⁴ π(dx) < ∞`.
* `K ℓ`: the compact sets `K^ℓ ⊂ ℝ × (0, ∞)` of Assumption 1.2, with `K^{ℓn} → K^ℓ` in the
  Hausdorff distance (`hausdorffEDist`; the product metric on `ℝ × ℝ` is the max metric, which is
  equivalent to the Euclidean one, so the convergence is the same).
* `heavy`: Assumption 2, `∑_ℓ (μ^ℓ)⁻¹ = 1`.
* `label`: the labelling (14), `h¹μ¹ ≤ h²μ² ≤ ⋯ ≤ h^Lμ^L`.
* `normalize`: `h¹μ¹ = 1` (p. 9, "we may and will assume"). -/
structure Setting (L : ℕ) where
  one_le_L : 1 ≤ L
  μ : Fin L → ℝ
  μ_pos : ∀ ℓ, 0 < μ ℓ
  h : Fin L → ℝ
  h_pos : ∀ ℓ, 0 < h ℓ
  cls : ℕ → Fin L → Set (ProbabilityMeasure ℝ)
  cls_nonempty : ∀ n ℓ, (cls n ℓ).Nonempty
  cls_closed : ∀ n ℓ, IsClosed (cls n ℓ)
  cls_support : ∀ n ℓ, ∀ π ∈ cls n ℓ, (π : Measure ℝ) (Set.Iio 0) = 0
  moment4 : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
    ∀ n ℓ, ∀ π ∈ cls n ℓ, ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(π : Measure ℝ) ≤ M
  K : Fin L → Set (ℝ × ℝ)
  K_compact : ∀ ℓ, IsCompact (K ℓ)
  K_subset : ∀ ℓ, K ℓ ⊆ Set.univ ×ˢ Set.Ioi 0
  hausdorff : ∀ ℓ, Tendsto (fun n => Metric.hausdorffEDist (prelimitSet (cls n ℓ) (μ ℓ) n) (K ℓ))
    atTop (𝓝 0)
  heavy : ∑ ℓ, (μ ℓ)⁻¹ = 1
  label : Monotone (fun ℓ => h ℓ * μ ℓ)
  normalize : h ⟨0, one_le_L⟩ * μ ⟨0, one_le_L⟩ = 1

namespace Setting

variable {L : ℕ}

/-- The paper's type 1 (Lean index `0`), the lowest-priority type. -/
def first (S : Setting L) : Fin L := ⟨0, S.one_le_L⟩

/-- `K^{ℓn}` of the model `S`. -/
def Kn (S : Setting L) (n : ℕ) (ℓ : Fin L) : Set (ℝ × ℝ) :=
  prelimitSet (S.cls n ℓ) (S.μ ℓ) n

end Setting

end HighUncertHT.Game


