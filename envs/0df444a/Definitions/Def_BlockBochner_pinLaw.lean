-- Prove2me | Definitions.Def_BlockBochner_pinLaw
-- name    : BlockBochner_pinLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:26.761635+00:00
-- url     : https://prove2.me/theorems/a2e012af-23d4-4369-aeeb-5e6ef5da93ae
-- title:
--   Law of the pinned spins $X_{V\setminus R}$
-- statement:
--   For $R\subseteq V$, the law of the pinned spins is the image of $\mu$ under $x\mapsto(x_v)_{v\notin R}$. Statements about pinnings $\tau$ of $V\setminus R$ hold for almost every $\tau$ with respect to this law.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.15

import Mathlib

open MeasureTheory

namespace BlockBochner

/-- **Law of the pinned spins `X_{V∖R}`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.2, p.15: "all statements about pinnings are
implicitly taken to mean to hold a.e. with respect to the law of the pinned spins."

**Formalization Note** The image of `µ` under `x ↦ (x_v)_{v ∉ R}`. -/
noncomputable def pinLaw {V : Type*} {S : V → Type*} [∀ v, MeasurableSpace (S v)]
    (μ : Measure (∀ v, S v)) (R : Finset V) : Measure (∀ v : {v // v ∉ R}, S v) :=
  μ.map (fun x (v : {v // v ∉ R}) => x v)

end BlockBochner


