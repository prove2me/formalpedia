-- Prove2me | Definitions.Def_DiffCtrlRobust_diffusionMatrix
-- name    : DiffCtrlRobust_diffusionMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:42.552391+00:00
-- url     : https://prove2.me/theorems/4aaf6534-f90e-4a2f-816b-f6f8fcbfeb5e
-- title:
--   The matrix $a=\frac12\sigma\sigma^{\mathsf T}$
-- statement:
--   For a diffusion matrix $\sigma:\mathbb R^d\to\mathbb R^{d\times d}$, the matrix $a(x)$ has entries
--
--   $$
--   a^{ij}(x)=\frac12\sum_{k=1}^d \sigma_{ik}(x)\,\sigma_{jk}(x),
--   $$
--
--   that is, $a=\frac12\sigma\sigma^{\mathsf T}$. It appears in the nondegeneracy condition (A3) and in the second-order part of the generator.
--
--   **Formalization Note** A $d\times d$ matrix is an element of the Euclidean space over $\mathrm{Fin}\,d\times\mathrm{Fin}\,d$ (`EthierKurtz.SDEDiffusion d`), so its norm is $\|\sigma\|=\sqrt{\mathrm{Tr}(\sigma\sigma^{\mathsf T})}$.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.6, (A3)

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The matrix `a := ½ σ σᵀ` of (A3) (arXiv:2205.05894v2, §2, p.6).

**Formalization Note.** A d × d matrix is an element of `EthierKurtz.SDEDiffusion d`, a Euclidean
space over `Fin d × Fin d`, so `‖σ x‖` is the paper's `√Tr(σσᵀ)`. -/
noncomputable def diffusionMatrix {d : ℕ} (σ : SDEState d → SDEDiffusion d) (x : SDEState d)
    (i j : Fin d) : ℝ :=
  (1 / 2) * ∑ k, σ x (i, k) * σ x (j, k)

end DiffCtrlRobust


