-- Prove2me | Definitions.Def_GevreyGibbsSep_Ncl
-- name    : GevreyGibbsSep_Ncl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:43:39.773893+00:00
-- url     : https://prove2.me/theorems/f5adc00d-a432-487e-8a11-d7353dec47b6
-- title:
--   Definition 3 — classical query complexity $N_{\mathrm{cl}}(\mathcal P,\varepsilon)$
-- statement:
--   The **classical query complexity** of sampling $\mathcal P$ with the order-$k$ oracle is
--   $$N_{\mathrm{cl}}(\mathcal P,\varepsilon)=\inf_A N_A(\mathcal P,\varepsilon),\qquad \inf\emptyset=+\infty,$$
--   the infimum over all sampling algorithms of Definition B.3.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition 3, Eq. (11), p.7

import Mathlib
import Definitions.Def_GevreyGibbsSep_oracle
import Definitions.Def_GevreyGibbsSep_SamplingAlg
import Definitions.Def_GevreyGibbsSep_queryCount

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- Definition 3, Eq. (11), arXiv:2608.24527 (sha256 d4fd40eb…), p.7: the classical query
complexity `N_cl(P, ε) = inf_A N_A(P, ε)` (`inf ∅ = +∞`) with oracle order `k`. -/
noncomputable def Ncl (d : ℕ) (k : ℕ∞) (P : Set ((Fin d → ℝ) → ℝ)) (ε : ℝ) : ℕ∞ :=
  ⨅ A : SamplingAlg d, queryCount A k P ε

end GevreyGibbsSep


