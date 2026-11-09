-- Prove2me | Definitions.Def_MWCSherali_Zreg
-- name    : MWCSherali_Zreg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:09.283526+00:00
-- url     : https://prove2.me/theorems/3d732fdc-349f-4597-ae30-de38b20570eb
-- title:
--   The central region $Z$
-- statement:
--   $$Z=\{t\in\Delta_4\mid \forall\ell\in[4],\ t_\ell\le\alpha\ \text{and}\ \forall i\neq j\in[4],\ t_i+t_j\ge\beta\},$$
--
--   the part of $\Delta_4$ outside the corners $K_a=\{t_a\ge\alpha\}$ and the tubes. Its boundary consists of four corner hexagons, four sink hexagons $Z\cap\Gamma_a$ and six tube rectangles.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.31

import Mathlib

namespace MWCSherali

/-- **The central region `Z`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.31:
"`Z = {t ∈ Δ₄ | ∀ ℓ ∈ [4], t_ℓ ≤ α and ∀ i ≠ j ∈ [4], t_i + t_j ≥ β}`."

**Formalization Note.** `Δ₄ = stdSimplex ℝ (Fin 4)`; indices are 0-based. -/
def Zreg (α β : ℝ) : Set (Fin 4 → ℝ) :=
  {t | t ∈ stdSimplex ℝ (Fin 4) ∧ (∀ l, t l ≤ α) ∧ ∀ i j, i ≠ j → β ≤ t i + t j}

end MWCSherali


