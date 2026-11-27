-- Prove2me | Definitions.Def_FreeOrderEPTAS_Supplement_kappa
-- name    : FreeOrderEPTAS_Supplement_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:37:06.449631+00:00
-- url     : https://prove2.me/theorems/42bef367-d7b2-56e3-9c18-bbd7792ab18b
-- title:
--   Weitzman's index $\kappa_i$
-- statement:
--   For a box with cost $c_i>0$, **Weitzman's index** $\kappa_i$ is the unique real number with
--   $$\mathbb E[(X_i-\kappa_i)^+]=c_i,$$
--   and $\kappa_i=\infty$ when $c_i=0$.
--
--   The map $k\mapsto\mathbb E[(X_i-k)^+]$ is continuous and non-increasing, tends to $\infty$ as $k\to-\infty$ and to $0$ as $k\to\infty$, and is strictly decreasing wherever it is positive, so the solution exists and is unique for every integrable law; it is negative exactly when $c_i>\mathbb E[X_i]$.
--
--   **Formalization Note** The value lies in `WithTop ℝ` ($\top$ for $c_i=0$); for $c_i>0$ it is defined as $\inf\{k:\mathbb E[(X_i-k)^+]\le c_i\}$, which is the solution.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, proof of Theorem 6.1 and footnote 1, p.31

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_PandoraInstance

open MeasureTheory

namespace FreeOrderEPTAS.Supplement

/-- Weitzman's index (arXiv:2007.13121v3, proof of Theorem 6.1, p.31, and footnote 1): `κ_i` is the
unique solution of `E[(X_i − κ_i)^+] = c_i`, and `κ_i = ∞` when `c_i = 0`.

**Formalization Note.** The value lies in `WithTop ℝ`, with `⊤` for `c_i = 0`. For `c_i > 0` it is
`sInf {k | E[(X_i − k)^+] ≤ c_i}`. The map `k ↦ E[(X_i − k)^+]` is continuous, non-increasing, tends
to `∞` as `k → −∞` and to `0` as `k → ∞`, and is strictly decreasing where it is positive, so this
set is `[κ_i, ∞)` for the unique solution `κ_i`, for every integrable law (no continuity of the law,
assumed in footnote 1 for the proof only, is used). `κ_i < 0` exactly when `c_i > E[X_i]`. -/
noncomputable def kappa {n : ℕ} (P : PandoraInstance n) (i : Fin n) : WithTop ℝ :=
  if P.c i = 0 then ⊤
  else ((sInf {k : ℝ | ∫ x, max (x - k) 0 ∂(P.X.μ i) ≤ P.c i} : ℝ) : WithTop ℝ)

end FreeOrderEPTAS.Supplement


