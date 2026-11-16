-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OracleStrategy_count
-- name    : GeomDRSub_Supplement_OracleStrategy_count
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:40:03.794036+00:00
-- url     : https://prove2.me/theorems/b5e110bd-ddd7-4705-9e7c-f41dcc530064
-- title:
--   Number of calls of a given kind among the first $	au$ calls
-- statement:
--   For a selector $\mathrm{sel}$ on calls, this is the number of indices $k<\tau$ for which $\mathrm{sel}(c_k)$ holds. With $\mathrm{sel}$ = "is an objective query" it counts objective queries, and with $\mathrm{sel}$ = "is a projection call" it counts projections. These are the call counts bounded in (129) and (213).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, (129), p.33, and (213), p.52

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy_call

namespace GeomDRSub.Supplement

/-- **Number of calls of a given kind among the first `τ` calls.** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, (129), p.33 and
(213), p.52: "calls to each oracle", "the total number of objective queries and projections".
`A.count d x ans ω sel τ` is the number of `k < τ` whose call `c` satisfies `sel c = true`. With
`sel = Sum.isLeft` it counts objective queries; with `sel = fun c => c.elim (fun _ => false)
Sum.isLeft` it counts projection calls. -/
noncomputable def OracleStrategy.count {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (A : OracleStrategy Ω m) (d : ℕ) (x : Fin m → ℝ) (ans : ℕ → OCall d → OResp d) (ω : Ω)
    (sel : OCall d → Bool) (τ : ℕ) : ℕ :=
  ((Finset.range τ).filter (fun k => sel (A.call d x ans ω k) = true)).card

end GeomDRSub.Supplement


