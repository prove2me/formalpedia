-- Prove2me | Definitions.Def_LocalDOvS_SUS_finalChoice
-- name    : LocalDOvS_SUS_finalChoice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:29.632878+00:00
-- url     : https://prove2.me/theorems/05602bd8-306a-451d-aeef-8e82ed4486ce
-- title:
--   Final comparison of the algorithm
-- statement:
--   When at most two active points remain and each has at least $n_{\mathrm{fin}}$ outputs (it keeps any extra outputs from the last test), the algorithm returns the active point with the smaller empirical mean of all its outputs; a tie is broken by an arbitrary rule that sees only the outputs observed so far.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Algorithm 2, lines 22–23, p.16

import Mathlib
import Definitions.Def_LocalDOvS_SUS_actSet
import Definitions.Def_LocalDOvS_SUS_sampleMean
import Definitions.Def_LocalDOvS_SUS_nFin

open scoped NNReal

namespace LocalDOvS.SUS

open Classical in
/-- The solution returned by the corrected shrinking uniform sampling algorithm once the
active set has at most two points and each of them has `max(cnt x, n_fin)` outputs
(Zhang–Zheng–Lavaei, arXiv:2012.02427v2, Algorithm 2, lines 22–23, p.16: "Return the point in
`S` with minimal empirical mean"), the empirical mean using all of these outputs. A tie between
the two points is broken by `tie st' D'` (`true`: the smaller point), an arbitrary rule using
only the outputs seen so far.

**Formalization Note.** Line 22 asks for half-widths `< ε/4` (`nFin`); a point that already has more
outputs (it took part in the last test at size `≥ 3`) keeps them, hence `max`. Only the first
two points of `S` are compared: the algorithm reaches this step only with `|S| ≤ 2`. -/
noncomputable def finalChoice (N : ℕ) (σ : ℝ≥0) (ε δ : ℝ)
    (tie : SUSState → (ℕ → ℕ → ℝ) → Bool) (D : ℕ → ℕ → ℝ) (st : SUSState) : ℕ :=
  let c : ℕ → ℕ := fun x => max (st.cnt x) (nFin N σ ε δ)
  let st' : SUSState := { st with cnt := fun x => if x ∈ actSet st then c x else st.cnt x }
  let D' : ℕ → ℕ → ℝ := fun x j => if j < st'.cnt x then D x j else 0
  let m : ℕ → ℝ := fun j => sampleMean D (st.x0 + j * st.s) (c (st.x0 + j * st.s))
  if st.M ≤ 1 then st.x0
  else if m 0 < m 1 then st.x0
  else if m 1 < m 0 then st.x0 + st.s
  else if tie st' D' then st.x0 else st.x0 + st.s

end LocalDOvS.SUS


