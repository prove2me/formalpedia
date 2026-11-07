-- Prove2me | Definitions.Def_GrothendieckLB_IsLimitingMixed
-- name    : GrothendieckLB_IsLimitingMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:34.28819+00:00
-- url     : https://prove2.me/theorems/45d05624-d903-4725-9677-9cef360fda87
-- title:
--   Limiting mixed correlation function
-- statement:
--   $H$ is a **limiting mixed correlation function** if it is a coefficientwise limit of averaged correlation functions of mixed rounding schemes, possibly in increasing dimensions: there are mixed schemes $\mu_N$ in dimensions $d_N$ with $[t^n]H_{\mu_N}\to[t^n]H$ as $N\to\infty$ for every $n$.
--
--   **Formalization Note** The dimension $d_N$ is free for each $N$, and convergence is required for every coefficient index $n$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 10.1, p.42

import Mathlib
import Definitions.Def_GrothendieckLB_MixedScheme_avgCorr
import Definitions.Def_GrothendieckLB_taylorCoeff
open Filter Topology

namespace GrothendieckLB

/-- `H` is a limiting mixed correlation function: a coefficientwise limit of averaged correlation
functions of mixed rounding schemes, possibly in increasing dimensions (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 10.1, p.42).

**Formalization Note** The dimension `d N` is free for each `N`, and every Taylor coefficient of the
averaged functions converges to the corresponding Taylor coefficient of `H`. -/
def IsLimitingMixed (H : ℝ → ℝ) : Prop :=
  ∃ (d : ℕ → ℕ) (S : ∀ N, MixedScheme (d N)), ∀ n : ℕ,
    Tendsto (fun N => taylorCoeff n (S N).avgCorr) atTop (𝓝 (taylorCoeff n H))

end GrothendieckLB


