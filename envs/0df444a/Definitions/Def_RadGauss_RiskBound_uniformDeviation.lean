-- Prove2me | Definitions.Def_RadGauss_RiskBound_uniformDeviation
-- name    : RadGauss_RiskBound_uniformDeviation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:01:34.540218+00:00
-- url     : https://prove2.me/theorems/8220ce20-a47e-436f-891b-c927bd804029
-- title:
--   Empirical mean $\hat{\mathbf E}_n h$ and the uniform deviation $\sup_{h\in G}(\mathbf Eh-\hat{\mathbf E}_nh)$
-- statement:
--   Let $P$ be a measure on a measurable space $\mathcal Z$, let $n \ge 1$, let $z = (z_1, \dots, z_n) \in \mathcal Z^n$ be a sample, and let $G$ be a class of functions $\mathcal Z \to \mathbb R$.
--
--   1. The **empirical mean** of $h : \mathcal Z \to \mathbb R$ on the sample is $\hat{\mathbf E}_n h = \frac1n \sum_{i=1}^n h(z_i)$.
--   2. The **uniform deviation** of $G$ on the sample is
--   $$\sup_{h \in G}\left(\mathbf E h - \hat{\mathbf E}_n h\right), \qquad \mathbf E h = \int h \, dP .$$
--   3. For a second ("ghost") sample $z' = (z'_1, \dots, z'_n)$, the **double-sample deviation** is
--   $$\sup_{h \in G}\left(\frac1n\sum_{i=1}^n h(z'_i) - \hat{\mathbf E}_n h\right).$$
--
--   The uniform deviation is the random variable whose concentration and expectation are controlled in the proof of Theorem 8; the double-sample deviation is the quantity the symmetrization argument integrates.
--
--   **Formalization Note** Both suprema are real suprema over the members of $G$. They are genuine suprema when $G$ is nonempty and the family is bounded above, which holds for the bounded classes used in this mission; for an empty class Lean returns $0$. The factor $1/n$ is read as $0$ when $n = 0$, so every statement using these objects assumes $n \ge 1$ where it matters.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 466 (PDF p. 4), definition of the empirical mean; pp. 467–468 (PDF pp. 5–6), proof of Theorem 8

import Mathlib

open MeasureTheory

namespace RadGauss.RiskBound

/-- The empirical mean `Ê_n h = (1/n) Σ_{i=1}^n h(z_i)` of `h` on the sample `z = (z_1, …, z_n)`
(p. 466). -/
noncomputable def empMean {Z : Type*} {n : ℕ} (z : Fin n → Z) (h : Z → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, h (z i)

/-- The uniform deviation `sup_{h ∈ G} (E h − Ê_n h)` of a class `G` at the sample `z`
(proof of Theorem 8, p. 467), with `E h = ∫ h dP`. A real supremum over the subtype `G`;
it is a genuine supremum when `G` is nonempty and the family is bounded above. -/
noncomputable def supDev {Z : Type*} [MeasurableSpace Z] (P : Measure Z) (n : ℕ)
    (G : Set (Z → ℝ)) (z : Fin n → Z) : ℝ :=
  ⨆ h : G, ((∫ w, (h : Z → ℝ) w ∂P) - empMean z (h : Z → ℝ))

/-- The double-sample uniform deviation `sup_{h ∈ G} ((1/n) Σ_i h(z'_i) − Ê_n h)` between a ghost
sample `z'` and the sample `z` (proof of Theorem 8, p. 468, second line of the last display). -/
noncomputable def doubleSupDev {Z : Type*} (n : ℕ) (G : Set (Z → ℝ))
    (z z' : Fin n → Z) : ℝ :=
  ⨆ h : G, (empMean z' (h : Z → ℝ) - empMean z (h : Z → ℝ))

end RadGauss.RiskBound


