-- Prove2me | Definitions.Def_UnionVolEst_alponaRun
-- name    : UnionVolEst_alponaRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:45.796721+00:00
-- url     : https://prove2.me/theorems/f87a2401-bde3-44dc-a07a-c6371376a318
-- title:
--   A run of Alpona (Algorithm 1) or Alpona-modified (Algorithm 2)
-- statement:
--   A run of **Alpona** sets $\mathrm{threshold}=\lceil (576/\varepsilon^2)\log(16M/\delta)\rceil$, $p=1$, $X=\emptyset$ (lines 1–3) and processes the bodies $K_1,\dots,K_M$ in order with the for loop of lines 6–15. **Alpona-modified** (Algorithm 2) is identical except that the halving loop also requires $p\ge 1/F_0$ (line 10). The run returns its final state, or none if some halving loop never terminates.
--
--   Line 4 fixes the oracle parameters $\kappa=\varepsilon/32$, $\delta_v=\delta/(4M)$, $\eta=\varepsilon/32$, $\beta=\varepsilon/(32M)$; they enter through the oracle model, not the run.
--
--   **Formalization Note** Bodies are processed in the order of `Fin M`; the run is driven by the random variables of the oracle model (or by a fixed vector of volume answers, as in the analysis of Claims 14–20). $(r,R)$ are oracle arguments only and are not modelled.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, Algorithm 1, p.15 (PDF p.17); §5.2, Algorithm 2, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_UnionVolEst_threshold
import Definitions.Def_UnionVolEst_AlponaState
import Definitions.Def_UnionVolEst_bodyStep

namespace UnionVolEst

/-- A run of Algorithm 1, Alpona (`guard = none`), or Algorithm 2, Alpona-modified
(`guard = some F₀`) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.3, printed p.15, PDF p.17; §5.2, printed p.19, PDF p.21), driven by
the volume answers `V i ω`, the uniform numbers `U i ω`, the sample streams `Z i j ω` and the
coins `C i r j ω`: `threshold = ⌈(576/ε²) log(16M/δ)⌉` (line 1), `p = 1` (line 2), `X = ∅`
(line 3), then lines 6–15 (`bodyStep`) for the bodies in order. The final state, or `none` if
some while loop never terminates.

**Formalization Note** Bodies are processed in the order `0, …, M − 1` of `Fin M` (the page's
`1, …, M`). Line 4's parameters `κ = ε/32`, `δ_v = δ/(4M)`, `η = ε/32`, `β = ε/(32M)` are the
oracle parameters; they enter through the hypotheses on `V`, `Z` (`OracleModel`), not the run.
The geometric parameters `(r, R)` are passed only to the oracles and are not modelled. For the
analysis of Claims 14–20 the run is also applied to a fixed vector of answers
(`V i ω = Ṽ i`). -/
noncomputable def alponaRun {n M : ℕ} {Ω : Type*} (guard : Option ℝ)
    (K : Fin M → Set (EuclideanSpace ℝ (Fin n))) (ε δ : ℝ) (V U : Fin M → Ω → ℝ)
    (Z : Fin M → ℕ → Ω → EuclideanSpace ℝ (Fin n)) (C : Fin M → ℕ → ℕ → Ω → Bool) (ω : Ω) :
    Option (AlponaState n) :=
  (List.finRange M).foldl
    (fun st i => st.bind (bodyStep K (threshold ε δ M) guard i (V i ω) (U i ω)
      (fun j => Z i j ω) (fun r j => C i r j ω)))
    (some ⟨[], 0, 0, 0⟩)

end UnionVolEst


