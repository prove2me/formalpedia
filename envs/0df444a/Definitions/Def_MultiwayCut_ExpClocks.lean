-- Prove2me | Definitions.Def_MultiwayCut_ExpClocks
-- name    : MultiwayCut_ExpClocks
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:03.497186+00:00
-- url     : https://prove2.me/theorems/a598c3dd-8814-40ff-ac08-64fa860f20e6
-- title:
--   The exponential clocks algorithm (Algorithm 1) and its separation probability
-- statement:
--   **Algorithm 1 (Exponential Clocks)** (§2.2, p.3). Choose i.i.d. random variables $Z_1,\dots,Z_k\sim\exp(1)$, one per terminal, and assign every point $\mathbf u\in\Delta_k$ to
--   $$\arg\min\{Z_i/u_i : i=1,\dots,k\},$$
--   where $Z_i/0=+\infty$, so a coordinate with $u_i=0$ never wins.
--
--   The **separation probability** $\mathrm{sep}_{\exp}(\mathbf u,\mathbf v)$ is the probability that $\mathbf u$ and $\mathbf v$ are assigned to different terminals. It is the exponential-clocks half of Algorithm 3.
--
--   **Formalization Note** The argmin is taken over the support $\{i:u_i>0\}$, comparing $Z_i/u_i\le Z_j/u_j$ as $Z_iu_j\le Z_ju_i$; ties (probability $0$) go to the least index, and the label $0$ is a default never used for points of $\Delta_k$ with positive clocks. The law of $(Z_1,\dots,Z_k)$ is `Measure.pi` of $k$ copies of Mathlib's `ProbabilityTheory.expMeasure 1`, and the separation probability is the measure of the event $\{Z : \text{labels differ}\}$ (an outer measure, so no measurability side condition), as a real number.
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, §2.2, p.3, Algorithm 1

import Mathlib

open MeasureTheory

namespace MultiwayCut

/-- **Exponential clocks labeling** (Algorithm 1, step 2), Buchbinder, Schwartz & Weizman,
*Simplex Transformations and the Multiway Cut Problem*, manuscript of Nov. 1, 2016, §2.2, p.3:
given the clocks `Z = (Z₁, …, Z_k)`, the point `u ∈ Δ_k` is assigned to
`argmin { Zᵢ / uᵢ : i = 1, …, k }`.

**Formalization Note.** Coordinates are `Fin k`, 0-based. In the paper `Zᵢ / 0 = +∞`, so a
coordinate with `uᵢ = 0` never wins; Lean's `x / 0 = 0` would make it win, so the argmin is
taken over the support `{i | 0 < uᵢ}` and `Zᵢ / uᵢ ≤ Z_j / u_j` is cross-multiplied as
`Zᵢ · u_j ≤ Z_j · uᵢ`. Ties (a null event for i.i.d. exponential clocks) go to the least index.
If no index qualifies (impossible for `u ∈ Δ_k` and positive clocks) the label is `0`. -/
noncomputable def expClock {k : ℕ} [NeZero k] (Z u : Fin k → ℝ) : Fin k :=
  let S : Finset (Fin k) :=
    Finset.univ.filter fun i => 0 < u i ∧ ∀ j, 0 < u j → Z i * u j ≤ Z j * u i
  if h : S.Nonempty then S.min' h else 0

/-- **Law of the clocks** (Algorithm 1, step 1), manuscript of Nov. 1, 2016, p.3: i.i.d.
`Zᵢ ∼ exp(1)`, `i = 1, …, k`, i.e. the product of `k` copies of Mathlib's exponential
distribution `ProbabilityTheory.expMeasure 1`. -/
noncomputable def clockLaw (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ : Fin k => ProbabilityTheory.expMeasure 1

/-- **Separation probability of the exponential clocks algorithm** (§2.2, p.3): the
probability that `u` and `v` are assigned to different terminals by Algorithm 1.

**Formalization Note.** The probability of the event is the measure of the set
`{Z | expClock Z u ≠ expClock Z v}` (an outer measure, so no measurability side condition is
needed and the value is never a junk `0`), converted to a real number. -/
noncomputable def sepExp {k : ℕ} [NeZero k] (u v : Fin k → ℝ) : ℝ :=
  (clockLaw k {Z | expClock Z u ≠ expClock Z v}).toReal

end MultiwayCut


