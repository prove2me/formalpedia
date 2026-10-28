-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
-- name    : CountingMatroid_Analysis_RelativeObservationBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:02:15.167033+00:00
-- url     : https://prove2.me/theorems/c651faa0-4754-44e8-8e9f-7f29dbb4e2d5
-- title:
--   Multiplicative relative-estimate predicate
-- statement:
--   For arbitrary rational numbers $\eta,\mu,\widehat\mu$, define
--   $$\operatorname{RelativeEstimate}(\eta,\mu,\widehat\mu)\ \Longleftrightarrow\ (1-\eta)\mu\le\widehat\mu\le(1+\eta)\mu.$$
--   Here $\eta$ is the intended tolerance, $\mu$ the reference mean, and $\widehat\mu$ the estimate. Positivity of the mean or bounds on the tolerance are not built into the definition.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RelativeObservationBounds.lean#L8-L11

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: Multiplicative error of an empirical mean around its positive
stationary mean. TEXLINE: main.tex:1241-1255 -/
def RelativeEstimate (η mean estimate : ℚ) : Prop :=
  (1 - η) * mean ≤ estimate ∧ estimate ≤ (1 + η) * mean





end CountingMatroid.Analysis.RelativeObservationBounds

end


