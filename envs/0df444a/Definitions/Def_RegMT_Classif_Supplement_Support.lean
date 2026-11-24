-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_Support
-- name    : RegMT_Classif_Supplement_Support
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:23:16.094107+00:00
-- url     : https://prove2.me/theorems/f0fdbe0b-c663-49fe-8d27-9c11228d9ada
-- title:
--   Extended support function
-- statement:
--   For a subset $Z$ of a real normed vector space and a continuous linear functional $v$, define
--   $$S_Z(v)=\sup_{z\in Z}v(z)\in[-\infty,+\infty].$$
--   The empty-set value is $-\infty$; an unbounded-above image has value $+\infty$. This is the primal-set support function used in (5), (17) and Lemma A.2. It differs in carrier from the published InfHorizonVP support function, which takes a set of dual vectors and evaluates at a primal vector.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p.4, §1.1, support function

import Mathlib

open scoped ENNReal

noncomputable section

namespace RegMT.Classif.Supplement

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- §1.1 p.4: primal-set support function, with infinite values retained. -/
def support (Z : Set V) (v : V →L[ℝ] ℝ) : EReal :=
  ⨆ z ∈ Z, (v z : EReal)

end RegMT.Classif.Supplement


