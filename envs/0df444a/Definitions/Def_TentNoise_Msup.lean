-- Prove2me | Definitions.Def_TentNoise_Msup
-- name    : TentNoise_Msup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:39.017138+00:00
-- url     : https://prove2.me/theorems/48595515-8080-492c-8d5d-7698d38cd0c4
-- title:
--   The density supremum $M_\sigma=\sup_{a,y\in[0,1]}h_\sigma(a,y)$
-- statement:
--   The **density supremum** of the reflected Gaussian kernel is
--
--   $$
--   M_\sigma:=\sup_{a,y\in[0,1]}h_\sigma(a,y),
--   $$
--
--   where $h_\sigma$ is the reflected heat kernel density. It bounds the density of every time marginal of the noised fitted chain (Lemma A.6), uniformly in time.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, so it is never a default value; it is $\infty$ exactly when $h_\sigma$ is unbounded on $[0,1]^2$.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.5, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_TentNoise_reflHeatDensity

open scoped ENNReal

namespace TentNoise

/-- `M_σ := sup_{a, y ∈ [0,1]} h_σ(a, y)`, the supremum of the reflected Gaussian kernel density
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.5, p.18).

**Formalization Note** The supremum is taken in `[0, ∞]`, so it is never a default value: it is
`∞` exactly when the density is unbounded on `[0,1]²`. -/
noncomputable def Msup (σ : ℝ) : ℝ≥0∞ :=
  ⨆ a ∈ Set.Icc (0 : ℝ) 1, ⨆ y ∈ Set.Icc (0 : ℝ) 1, reflHeatDensity σ a y

end TentNoise


