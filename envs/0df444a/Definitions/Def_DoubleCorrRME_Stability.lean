-- Prove2me | Definitions.Def_DoubleCorrRME_Stability
-- name    : DoubleCorrRME_Stability
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:01.46834+00:00
-- url     : https://prove2.me/theorems/e5fbf59e-c4e2-4d02-9eb0-94b0cd26fe38
-- title:
--   Stability (Definition 3.6) and the truncated batch means $z^{\mathrm{tr}}_i$
-- statement:
--   **Stability** (Definition 3.6). Let $\varepsilon\in(0,\tfrac12)$, $\Delta>0$, $\mu\in\mathbb R^d$ and $\Sigma_0\succeq0$. A finite multiset $S$ is $(\varepsilon,\Delta)$-stable with respect to $(\mu,\Sigma_0)$ if for every $S'\subseteq S$ with $|S'|\ge(1-\varepsilon)|S|$,
--
--   $$\|\mu_{S'}-\mu\|_2\le\Delta\qquad\text{and}\qquad\|M_{S'}(\mu)-\Sigma_0\|_2\le\frac{\Delta^2}{\varepsilon},$$
--
--   where $\|\cdot\|_2$ is the spectral norm.
--
--   **Truncation** (§2.3). Given clean data $z$, an index set $\mathcal I\subseteq[N]\times[n]$ and $\mu$, set $z^{\mathrm{tr}}_{i,j}=z_{i,j}$ if $(i,j)\in\mathcal I$ and $z^{\mathrm{tr}}_{i,j}=\mu$ otherwise; the truncated batch means are $z^{\mathrm{tr}}_i=\frac1n\sum_j z^{\mathrm{tr}}_{i,j}$ and their average is $\bar z^{\mathrm{tr}}=\frac1N\sum_i z^{\mathrm{tr}}_i$.
--
--   Stability is the property both reference sets of the paper satisfy, and the truncated batch means are the second reference's points.
--
--   **Formalization Note** Sub-multisets are index subsets and are required to be nonempty (automatic when $S\neq\emptyset$ and $\varepsilon<\tfrac12$). The parameter ranges are hypotheses of the statements that use stability. The spectral norm is the published `HighDimProb.QuadraticForms.opNorm`.
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Definition 3.6, p.18 (PDF p.19); §2.3, p.8 (PDF p.9), eq. (1)

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model

namespace DoubleCorrRME

/-!
# Stability (Definition 3.6) and the truncated batch means

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…): Definition 3.6, p.18
(PDF p.19); the truncation `z^tr_{i,j}`, the truncated batch means `z^tr_i` and their average
`z̄^tr`, §2.3, p.8 (PDF p.9) and (1).

**Formalization Note.**
* The matrix norm `‖·‖₂` is the spectral (operator) norm, the published
  `HighDimProb.QuadraticForms.opNorm` (`‖toEuclideanCLM A‖`).
* A multiset `S = {z_k : k ∈ I}` is a family `z` with an index set `I` (see `Def_DoubleCorrRME_Model`).
  The sub-multisets `S′ ⊆ S` of Definition 3.6 are the index subsets `S′ ⊆ I`. They are required to
  be nonempty, so that `µ_{S′}` is defined: when `I ≠ ∅` and `ε < 1/2` the size bound
  `|S′| ≥ (1 − ε)|I|` already forces this, and when `I = ∅` the paper's `µ_S` is undefined.
* The parameter ranges `ε ∈ (0, 1/2)`, `∆ > 0`, `Σ₀ ⪰ 0` of Definition 3.6 are hypotheses of the
  statements that use `IsStable`, not part of the predicate.
* `z^tr` depends on the clean data `z`, the index set `ℐ` and the mean `µ`, all explicit arguments.
-/

/-- Definition 3.6. The multiset `{z_k : k ∈ I}` is `(ε, ∆)`-stable with respect to `(µ, Σ₀)`: for
every nonempty `S′ ⊆ I` with `|S′| ≥ (1 − ε)|I|`, `‖µ_{S′} − µ‖₂ ≤ ∆` and
`‖M_{S′}(µ) − Σ₀‖₂ ≤ ∆²/ε`. -/
def IsStable {ι : Type*} {d : ℕ} (z : ι → Vec d) (I : Finset ι) (ε Δ : ℝ) (μ : Vec d)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ S' ⊆ I, S'.Nonempty → (1 - ε) * (I.card : ℝ) ≤ S'.card →
    ‖meanOn z S' - μ‖ ≤ Δ ∧
      HighDimProb.QuadraticForms.opNorm (momentOn z S' μ - S₀) ≤ Δ ^ 2 / ε

open Classical in
/-- The truncation (§2.3, p.8): `z^tr_{i,j} := z_{i,j}` if `(i, j) ∈ ℐ`, and `µ` otherwise. -/
noncomputable def ztr {N n d : ℕ} (z : Fin N → Fin n → Vec d) (I : Finset (Fin N × Fin n))
    (μ : Vec d) : Fin N → Fin n → Vec d :=
  fun i j => if (i, j) ∈ I then z i j else μ

/-- The truncated batch mean `z^tr_i := (1/n) ∑_j z^tr_{i,j}` (§2.3, p.8). -/
noncomputable def ztrBatch {N n d : ℕ} (z : Fin N → Fin n → Vec d) (I : Finset (Fin N × Fin n))
    (μ : Vec d) : Fin N → Vec d :=
  fun i => ((n : ℝ))⁻¹ • ∑ j, ztr z I μ i j

/-- The average truncated batch mean `z̄^tr := (1/N) ∑_i z^tr_i` of (1). -/
noncomputable def ztrMean {N n d : ℕ} (z : Fin N → Fin n → Vec d) (I : Finset (Fin N × Fin n))
    (μ : Vec d) : Vec d :=
  ((N : ℝ))⁻¹ • ∑ i, ztrBatch z I μ i

end DoubleCorrRME


