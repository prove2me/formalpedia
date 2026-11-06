-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_f
-- name    : GradSuffice_Thm8Data_f
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:13.44508+00:00
-- url     : https://prove2.me/theorems/4998d221-5f91-4284-a79e-9560290dc6b3
-- title:
--   The noisy hard function $f$ of Theorem 8
-- statement:
--   For a noise realization $Z$,
--   $$f_k(w)=\max\Big\{\max_{t\le D}\Big(\frac1{16}\eta_{t,k}\cdot y_k(w)+b_{t,k}+Z_{t,k}\Big),\ H_k(y_k(w))\Big\}\cdot s^{k-1},\qquad f(w):=\max_{1\le k\le\kappa}f_k(w).$$
--
--   **Formalization Note** 0-based copies: the factor $s^{k-1}$ is $s^k$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_affinePiece
import Definitions.Def_GradSuffice_Thm8Data_barrier
import Definitions.Def_GradSuffice_thm8S

namespace GradSuffice

/-- **The noisy hard function `f`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19:
`f_k(w) = max{max_{t≤D} ((1/16) η_{t,k} · y_k(w) + b_{t,k} + Z_{t,k}), H_k(y_k(w))} · s^{k−1}` and
`f(w) := max_{1≤k≤κ} f_k(w)`, for a realization `Z` of the noise.

**Formalization Note.** 0-based copies: the factor `s^{k−1}` is `s ^ k`. The maxima are real `⨆`
over the nonempty finite types `Fin κ` and `Fin D` (`κ ≥ 1` wherever a copy index exists,
`D ≥ 1` by `IsValid`). -/
noncomputable def Thm8Data.f {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (Z : c.NoiseIdx → ℝ) (w : X) : ℝ :=
  ⨆ k : Fin c.κ,
    max (⨆ t : Fin c.D, c.affinePiece t k Z w) (c.barrier k Z w) * thm8S c.θ ^ (k : ℕ)

end GradSuffice


