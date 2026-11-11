-- Prove2me | Definitions.Def_IllCondRegMem_IsPrunedOn
-- name    : IllCondRegMem_IsPrunedOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:43.008221+00:00
-- url     : https://prove2.me/theorems/606391c6-4e8a-4724-8754-34d357708d77
-- title:
--   Definition 4 — $(d_0,\delta_{\max})$-pruned distributions on $G^\perp$
-- statement:
--   Let $D$ be a distribution on subspaces of $\mathbb R^d$ and $G\subseteq\mathbb R^d$ a subspace. $D$ is **$(d_0,\delta_{\max})$-pruned on $G^\perp$** if
--   $$
--   \mathbb P_{E\sim D}\{\|P_Ew\|<\delta\}\le\delta^{d_0}\qquad\text{for all } w\in S^{d-1}\cap G^\perp,\ \delta\in(0,\delta_{\max}].
--   $$
--   No direction perpendicular to $G$ is nearly orthogonal to $E$ with much larger probability than for a uniformly random subspace. The pruning procedure maintains this property of the learner's posterior on the hidden subspace, and the masking lemma (Lemma 5) uses it.
--
--   **Formalization Note** The distribution is the law of a random subspace $E$ on a measure space $(\Omega,\mathbb P)$; $S^{d-1}$ is the unit sphere.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Definition 4, eq. (3), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat

open MeasureTheory

namespace IllCondRegMem

/-- **Pruned distribution** (Definition 4).
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Definition 4,
p.8, eq. (3): "A distribution D on subspaces of ℝ^d is (d₀, δ_max)-pruned on G⊥ if
P_{E∼D}{‖P_E w‖ < δ} ≤ δ^{d₀} for all w ∈ S^{d−1} ∩ G⊥, δ ∈ (0, δ_max]."

`IsPrunedOn P E G d₀ δmax` says that the law of the random subspace `E` under `P` is
`(d₀, δ_max)`-pruned on `G⊥`.

**Formalization Note.** A distribution on subspaces is represented as the law of a random
subspace `E : Ω → Submodule ℝ (Vec d)` on a measure space `(Ω, P)`; `P_E w` is
`(E ω).starProjection w`, and `S^{d−1}` is the unit sphere `‖w‖ = 1`. -/
def IsPrunedOn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (E : Ω → Submodule ℝ (Vec d)) (G : Submodule ℝ (Vec d)) (d₀ : ℕ) (δmax : ℝ) : Prop :=
  ∀ w : Vec d, ‖w‖ = 1 → w ∈ Gᗮ → ∀ δ : ℝ, 0 < δ → δ ≤ δmax →
    P {ω | ‖(E ω).starProjection w‖ < δ} ≤ ENNReal.ofReal (δ ^ d₀)

end IllCondRegMem


