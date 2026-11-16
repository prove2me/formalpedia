-- Prove2me | Definitions.Def_SketchAttr_LOO_Supplement_Adaptive
-- name    : SketchAttr_LOO_Supplement_Adaptive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:49:22.060198+00:00
-- url     : https://prove2.me/theorems/525072c2-e897-4dfd-a1f0-adbb87188d88
-- title:
--   Unrestricted randomized adaptive query procedures
-- statement:
--   A procedure with worst-case budget $q$ consists of an arbitrary seed space, measurable query functions, and a measurable terminal output function. At round $t$, the next query depends on the seed and all $t$ previous answers. The output depends on the seed and the completed transcript:
--
--   $$Q_t=Q_t(s,a_0,\ldots,a_{t-1}),\qquad \widehat L=H(s,a_0,\ldots,a_{q-1}).$$
--
--   The unknown matrix is accessible only through the oracle that generates the answers. There is no restriction on computation between queries. Earlier stopping is represented by padding to the worst-case budget and ignoring the extra answers. The seed law is supplied separately, independently of the unknown input. This reusable interface is independent of the particular matrix and higher-derivative oracles.
-- source:
--   Chris Liaw, Aranyak Mehta, Grigoris Velegkas, Felix Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (October 2026), PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2, Section 5.3, p. 19, and Appendix C, p. 29

import Mathlib

open MeasureTheory

namespace SketchAttr.LOO.Supplement

/-- Unrestricted measurable adaptive q-query procedures. Neither the query
functions nor the terminal output receive the unknown oracle parameter.
A stopping procedure is padded with unused queries to its worst-case budget. -/
structure AdaptiveProcedure (Seed Query Answer Output : Type*)
    [MeasurableSpace Seed] [MeasurableSpace Query]
    [MeasurableSpace Answer] [MeasurableSpace Output] (q : ℕ) where
  query : (t : ℕ) → Seed → (Fin t → Answer) → Query
  output : Seed → (Fin q → Answer) → Output
  query_measurable : ∀ t, Measurable (Function.uncurry (query t))
  output_measurable : Measurable (Function.uncurry output)

/-- The history consists of exactly t previous answers, in chronological order.
The seed is fixed through the entire run. -/
noncomputable def adaptiveHistory {Seed Query Answer Output : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Query]
    [MeasurableSpace Answer] [MeasurableSpace Output] {q : ℕ}
    (P : AdaptiveProcedure Seed Query Answer Output q)
    (oracle : Query → Answer) (seed : Seed) : (t : ℕ) → Fin t → Answer
  | 0 => Fin.elim0
  | t + 1 =>
    let h := adaptiveHistory P oracle seed t
    Fin.snoc h (oracle (P.query t seed h))

noncomputable def adaptiveOutput {Seed Query Answer Output : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Query]
    [MeasurableSpace Answer] [MeasurableSpace Output] {q : ℕ}
    (P : AdaptiveProcedure Seed Query Answer Output q)
    (oracle : Query → Answer) (seed : Seed) : Output :=
  P.output seed (adaptiveHistory P oracle seed q)

end SketchAttr.LOO.Supplement


