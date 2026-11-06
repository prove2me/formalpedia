-- Prove2me | Definitions.Def_AnytimeAdaVR_coefCgamma
-- name    : AnytimeAdaVR_coefCgamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:45.741268+00:00
-- url     : https://prove2.me/theorems/a929c090-190a-4393-957c-781d5a8a96b0
-- title:
--   Path coefficient $C_\gamma(\Lambda)$
-- statement:
--   For $\gamma\in\{1/4,1/3\}$,
--   $$
--   C_\gamma(\Lambda)=12\sqrt{A_\Lambda V_\Lambda}+16\sqrt2\,9^\gamma\,(4+E_\Lambda)\,A_\Lambda .
--   $$
--   The S coefficient is $S=C_{1/4}(L)$ and the M coefficient is $M=C_{1/3}(\bar L)$. These are deterministic quantities and are never inputs to the algorithm.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. G.1, eq. (63), p.30

import Mathlib
import Definitions.Def_AnytimeAdaVR_coefA
import Definitions.Def_AnytimeAdaVR_coefV

namespace AnytimeAdaVR

/-- **The path coefficient `C_γ(Λ) = 12√(A_Λ V_Λ) + 16√2·9^γ·(4 + E_Λ)·A_Λ`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. G.1, p.30,
eq. (63), `γ ∈ {1/4, 1/3}`; the S coefficient is `S = C_{1/4}(L)` and the M coefficient is
`M = C_{1/3}(L̄)`.

**Formalization Note.** `9^γ` is `Real.rpow`. The function is defined for every real `γ`; the
paper uses only `γ = 1/4, 1/3`. -/
noncomputable def coefCgamma (γ Δf L σ Λ : ℝ) : ℝ :=
  12 * Real.sqrt (coefA Δf L σ Λ * coefV Δf L σ Λ) +
    16 * Real.sqrt 2 * (9 : ℝ) ^ γ * (4 + coefE σ Λ) * coefA Δf L σ Λ

end AnytimeAdaVR


