-- Prove2me | Definitions.Def_ConstDepthUnitary_sampShift
-- name    : ConstDepthUnitary_sampShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:47.755072+00:00
-- url     : https://prove2.me/theorems/beb6c126-90b2-4923-9827-4b2a164687f7
-- title:
--   Sampling to the grid
-- statement:
--   For $\psi:\mathbb R^N\to\mathbb C$ and $m\in\mathbb Z^N$, the shifted sampling
--   $$\mathrm{Samp}^{(m)}_{\Lambda^N}|\psi\rangle=\sum_{w\in[K]^N}\psi(\alpha(w)+2Lm)\,|w\rangle\qquad\text{(Eq. (61))},$$
--   with $\mathrm{Samp}_{\Lambda^N}$ the case $m=0$ (Eq. (60)), and the wrapped sampling
--   $$\mathrm{WSamp}_{\Lambda^N}|\psi\rangle=\sum_{m\in\mathbb Z^N}(-1)^{\sum_j m_j}\,\mathrm{Samp}^{(m)}_{\Lambda^N}|\psi\rangle\qquad\text{(Eq. (62))}.$$
--   `l2Norm` is the Euclidean norm of a vector on a finite index set.
--
--   **Formalization Note** Vectors on the grid are functions $[K]^N\to\mathbb C$. An infinite sum of a non-summable family is $0$ in Lean, so the statements using `wSamp` carry summability in their conclusions.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.2.3, Eqs. (60)–(62), p.27

import Mathlib
import Definitions.Def_ConstDepthUnitary_alpha
import Definitions.Def_ConstDepthUnitary_latticePt

namespace ConstDepthUnitary

/-- The grid point `α(w)` as a point of `ℝ^N`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.1.1, p.23. -/
noncomputable def gridPt {N : ℕ} (K : ℕ) (w : Fin N → Fin K) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (alphaVec K w)

/-- The shifted sampling `Samp^{(m)}_{Λ^N} |ψ⟩ = Σ_w ψ(α(w) + 2L m) |w⟩`, Eq. (61), p.27, as a function
of `w`. The case `m = 0` is `Samp_{Λ^N}`, Eq. (60). -/
noncomputable def sampShift {N : ℕ} (K : ℕ) (m : Fin N → ℤ) (ψ : EuclideanSpace ℝ (Fin N) → ℂ)
    (w : Fin N → Fin K) : ℂ :=
  ψ (gridPt K w + (2 * gridL K) • latticePt m)

/-- The wrapped sampling `WSamp_{Λ^N} |ψ⟩ = Σ_{m ∈ ℤ^N} (−1)^{Σ_j m_j} Samp^{(m)}_{Λ^N} |ψ⟩`, Eq. (62), p.27,
as a function of `w`.

**Formalization Note** `∑'` is `0` on a non-summable family; the statements using it carry summability in
their conclusions. -/
noncomputable def wSamp {N : ℕ} (K : ℕ) (ψ : EuclideanSpace ℝ (Fin N) → ℂ) (w : Fin N → Fin K) : ℂ :=
  ∑' m : Fin N → ℤ, (-1 : ℂ) ^ (∑ j, m j) * sampShift K m ψ w

/-- The Euclidean norm of a vector indexed by a finite type. -/
noncomputable def l2Norm {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖

end ConstDepthUnitary


