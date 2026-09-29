-- Prove2me | Definitions.Def_HighDimProb_DvoretzkyMilman_ExpSup
-- name    : HighDimProb_DvoretzkyMilman_ExpSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:12:10.640513+00:00
-- url     : https://prove2.me/theorems/bf810fe8-d9bc-4b52-9e3f-4c8e6cfad978
-- title:
--   The expected supremum $E \sup_{i\in\mathrm{Idx}} Y_i$ of a family of random variables
-- statement:
--   This is the **expected supremum** of a family of real random variables indexed by an
--   arbitrary set, the finite-marginal convention the whole book uses (footnote 3 to Section 7.2,
--   p. 160) whenever the supremum of an infinite family is not obviously measurable. It underlies
--   the Gaussian width definition this mission's goal is stated in terms of.
--
--   Fix a probability space $(\Omega,\mathcal F,P)$ and a family $(Y_i)_{i\in\mathrm{Idx}}$ of
--   real random variables. Then
--   $$
--   E\sup_{i\in\mathrm{Idx}} Y_i \;:=\; \sup_{S\subseteq\mathrm{Idx}\text{ finite, nonempty}} E\max_{i\in S} Y_i.
--   $$
--
--   **Formalization Note** Valued in `EReal`, not `ℝ`, for the same reason as this convention's
--   other copies elsewhere in the series: a real-valued supremum would silently default to the
--   junk value $0$ when the family of finite marginals is unbounded above. This chunk's own copy
--   (`07-chaining`'s and `08-matrix-deviation`'s copies are still drafts, so not imported, per
--   `CAPTAIN_BRIEF.md` Addendum 2 rule 5).
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 160, footnote 3 to Section 7.2

import Mathlib

open MeasureTheory

namespace HighDimProb.DvoretzkyMilman

/-- The **expected supremum** `E sup_{i∈Idx} Y i` of a family `(Y i)_{i∈Idx}` of real random
variables on a probability space `(Ω, P)`, understood through the family's finite-dimensional
marginals, exactly as Vershynin's own footnote 3 to Section 7.2 (p. 160, PDF p. 168) sets the
convention for the whole book. This chunk's own copy of the same convention already built (under
the names `processESup`/`expSup`) for `07-chaining`/`08-matrix-deviation`: those chunks' own
copies are still-draft definitions, so per `CAPTAIN_BRIEF.md` Addendum 2 rule 5 this chapter
redefines its own copy here rather than importing either. -/
noncomputable def expSup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {Idx : Type}
    (Y : Idx → Ω → ℝ) : EReal :=
  ⨆ (S : {s : Finset Idx // s.Nonempty}), ((∫ ω, S.1.sup' S.2 (fun i => Y i ω) ∂P : ℝ) : EReal)

end HighDimProb.DvoretzkyMilman


