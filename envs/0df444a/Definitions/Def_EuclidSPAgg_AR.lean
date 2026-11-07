-- Prove2me | Definitions.Def_EuclidSPAgg_AR
-- name    : EuclidSPAgg_AR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:03.146664+00:00
-- url     : https://prove2.me/theorems/88fd781b-4903-49ea-bf87-7aaa24fbe93d
-- title:
--   Approximation ratio $\mathrm{AR}(f)$
-- statement:
--   The **approximation ratio** of a mechanism $f:E^n\to E$ is
--   $$
--   \mathrm{AR}(f)=\sup_{x\in E^n}\frac{\mathrm{SC}(x,f(x))}{\mathrm{OPT}(x)},
--   $$
--   with the quotient equal to $1$ if both costs vanish and $+\infty$ if only the denominator vanishes. Finite ratio gives $\mathrm{SC}(x,f(x))\le\mathrm{AR}(f)\,\mathrm{OPT}(x)$ at every profile.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, so $\mathrm{AR}(f)=\infty$ is allowed. The paper defines the ratio for $n\ge2$; the Lean definition is total in $n$, and every statement using it assumes $n\ge2$.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_ratioAt
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The approximation ratio `AR(f) = sup_{x ∈ Eⁿ} SC(x, f(x)) / OPT(x)` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9
(PDF p.11)).

**Formalization Note** The supremum is taken in `ℝ≥0∞`, so `AR f = ⊤` is the paper's infinite
ratio. The paper defines AR for `n ≥ 2`; the definition here is total in `n`, and every statement
using it assumes `n ≥ 2`. -/
noncomputable def AR {n d : ℕ} (f : Mech n d) : ENNReal :=
  ⨆ x : Fin n → E d, ratioAt f x

end EuclidSPAgg


