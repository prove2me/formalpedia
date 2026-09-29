-- Prove2me | Definitions.Def_HighDimProb_Deviations_ExpSup
-- name    : HighDimProb_Deviations_ExpSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:05:55.748106+00:00
-- url     : https://prove2.me/theorems/1317c31a-ce17-4270-a639-c1be52ed8e4b
-- title:
--   The expected supremum $E \sup_{i\in\mathrm{Idx}} Y_i$ of a family of random variables
-- statement:
--   This is the **expected supremum** of a family of real random variables indexed by an
--   arbitrary set, the finite-marginal convention the whole book uses (footnote 3 to Section 7.2,
--   p. 160) whenever the supremum of an infinite family is not obviously measurable. It underlies
--   both the goal theorem's left-hand side and the Gaussian width/complexity definitions this
--   mission reuses.
--
--   Fix a probability space $(\Omega,\mathcal F,P)$ and a family $(Y_i)_{i\in\mathrm{Idx}}$ of
--   real random variables. Then
--   $$
--   E\sup_{i\in\mathrm{Idx}} Y_i \;:=\; \sup_{S\subseteq\mathrm{Idx}\text{ finite, nonempty}} E\max_{i\in S} Y_i.
--   $$
--
--   **Formalization Note** Valued in `EReal`, not `ℝ`, for the same reason as `07-chaining`'s
--   `processESup`: a real-valued supremum would silently default to the junk value $0$ when the
--   family of finite marginals is unbounded above. This chunk's own copy (that chunk's is still a
--   draft, so not imported, per `CAPTAIN_BRIEF.md` Addendum 2 rule 5), generalized to an arbitrary
--   index type rather than a single fixed one.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 160, footnote 3 to Section 7.2; used throughout Chapter 9

import Mathlib

open MeasureTheory

namespace HighDimProb.Deviations

/-- The **expected supremum** `E sup_{i∈Idx} Y i` of a family `(Y i)_{i∈Idx}` of real random
variables on a probability space `(Ω, P)`, understood through the family's finite-dimensional
marginals, exactly as Vershynin's own footnote 3 to Section 7.2 (p. 160, PDF p. 168) sets the
convention for the whole book:

`E sup_{i∈Idx} Y i := sup { E max_{i∈S} Y i : S ⊆ Idx finite and nonempty }`.

Valued in `EReal`, not `ℝ`: a real-valued `sSup` would silently default to the junk value `0`
whenever the underlying set of finite marginals is unbounded above, making a comparison against
it vacuous. This chunk's own copy of the same convention already built (under the name
`processESup`) for `07-chaining`: that chunk's own copy is a still-draft definition (not in
`missions/README.md`'s published list), so per `CAPTAIN_BRIEF.md` Addendum 2 rule 5 this chapter
redefines its own copy here rather than importing it, generalized to an arbitrary index type
`Idx` (used both for a subset `T ⊂ ℝⁿ` and, via `Fin m`, for other finite families) rather than
`07-chaining`'s single index type `T`. -/
noncomputable def expSup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {Idx : Type}
    (Y : Idx → Ω → ℝ) : EReal :=
  ⨆ (S : {s : Finset Idx // s.Nonempty}), ((∫ ω, S.1.sup' S.2 (fun i => Y i ω) ∂P : ℝ) : EReal)

end HighDimProb.Deviations


