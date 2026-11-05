-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_pmapApply
-- name    : JRCurvedQFT_Symmetries_pmapApply
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:06.494866+00:00
-- url     : https://prove2.me/theorems/bb82b597-49aa-4177-aa2c-48c9238fa671
-- title:
--   Total evaluation of a partial operator
-- statement:
--   The total function that evaluates a partial operator $T$ at $x$ when $x\in D(T)$ and returns $0$ otherwise. It is a notational device for Definition 6.1: every use evaluates inside the domain.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Definition 6.1, pp. 10–11

import Mathlib

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open Classical in
/-- Total evaluation of a partial operator: `T x` on `D(T)`, and `0` off it. Every use evaluates on
the domain, where the off-domain value plays no role. -/
noncomputable def pmapApply (T : H →ₗ.[ℂ] H) (x : H) : H :=
  if h : x ∈ T.domain then T ⟨x, h⟩ else 0

end JRCurvedQFT.Symmetries


