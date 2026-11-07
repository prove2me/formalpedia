-- Prove2me | Definitions.Def_SteinerNav_annularCandidates
-- name    : SteinerNav_annularCandidates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:35.702414+00:00
-- url     : https://prove2.me/theorems/1e11a007-279b-40b6-bece-1a543a21c107
-- title:
--   The sampling radius $\varepsilon=1-1/\alpha^2$, nonempty annuli, and the annular candidate neighbors of Corollary 4.2
-- statement:
--   Let $P\subset\mathbb R^d$ with $|P|\ge2$, minimum distance $\sigma$ and $L=1+\lfloor\log_2\Delta\rfloor$, and let $s$ be a source.
--
--   1. For $\alpha>1$, $\varepsilon=1-1/\alpha^2$; at $\alpha=1+1/d$ this is $(2d+1)/(d+1)^2$.
--   2. The annulus with index $i$ around $s$ has inner radius $2^i\sigma$ and outer radius $2^{i+1}\sigma$; it is **nonempty** if some target $t\in P\setminus\{s\}$ satisfies $2^i\sigma\le\|s-t\|\le 2^{i+1}\sigma$.
--   3. Given unit vectors $u_{i,j}$, $i<L$, $j<K$, the **candidate neighbors** of $s$ are the points
--   $$s+2^i\sigma\sqrt{2\varepsilon}\,u_{i,j},\qquad j<K,\ i<L\text{ with annulus } i \text{ nonempty}.$$
--
--   Each candidate is the sampled point of Lemma 4.1 with $r_0=2^i\sigma$. The law of a uniformly random unit vector is the published `RegretBandits.Nonlinear.uniformSphere`, the normalized surface measure on the unit sphere; this module also records that it is a finite measure, so that products of it can be formed.
--
--   **Formalization Note** The annuli are closed. The page assigns a target on a shared boundary to one of its annuli; here it makes both annuli nonempty, which can only add candidates and keeps the count at most $KL$.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), §4.1, p.7 (ε, the annuli, Lemma 4.1's sampled point, Corollary 4.2)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_SteinerNav_aspectRatio

namespace SteinerNav

open MeasureTheory RegretBandits.Nonlinear

/-- The law `RegretBandits.Nonlinear.uniformSphere d` has total mass at most one, in every
dimension (it is `σ(univ)⁻¹ • σ`); products of it (`Measure.pi`) use this instance. For `d ≥ 1`
it is a probability measure (checked in this mission's verification file). -/
instance instIsFiniteMeasureUniformSphere (d : ℕ) : IsFiniteMeasure (uniformSphere d) :=
  ⟨by
    simp only [uniformSphere, Measure.smul_apply, smul_eq_mul]
    exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) ENNReal.one_lt_top⟩

/-- `ε = 1 − 1/α²` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §4.1, p.7). At `α = 1 + 1/d` this is `(2d + 1)/(d + 1)²`. -/
noncomputable def samplingEps (α : ℝ) : ℝ :=
  1 - 1 / α ^ 2

/-- The annulus with index `i` around `s` is nonempty: some target of `P \ {s}` has distance from `s`
between the inner radius `2^i σ` and the outer radius `2^(i+1) σ` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §4.1, p.7).

**Formalization Note** The annuli are closed. The page assigns a target on a shared boundary to one
of its annuli; here it makes both nonempty. -/
def AnnulusNonempty {d : ℕ} (P : Finset (Pt d)) (s : Pt d) (i : ℕ) : Prop :=
  ∃ t ∈ P, t ≠ s ∧ (2 : ℝ) ^ i * minDist P ≤ dist s t ∧ dist s t ≤ (2 : ℝ) ^ (i + 1) * minDist P

open scoped Classical in
/-- The candidate neighbors of Corollary 4.2 for the source `s`, given unit vectors `u i j`: the
points `s + r₀ √(2ε) u i j` with `r₀ = 2^i σ`, over `j < K` and over those `i < L` whose annulus is
nonempty (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 4.1 and Corollary 4.2, p.7). -/
noncomputable def annularCandidates {d : ℕ} (α : ℝ) (P : Finset (Pt d)) (s : Pt d) (K L : ℕ)
    (u : Fin L × Fin K → Pt d) : Finset (Pt d) :=
  (Finset.univ.filter fun ij : Fin L × Fin K => AnnulusNonempty P s (ij.1 : ℕ)).image fun ij =>
    s + ((2 : ℝ) ^ (ij.1 : ℕ) * minDist P * Real.sqrt (2 * samplingEps α)) • u ij

end SteinerNav


