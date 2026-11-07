-- Prove2me | Definitions.Def_LaconicBarrier_KWiseIndep
-- name    : LaconicBarrier_KWiseIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:23.283191+00:00
-- url     : https://prove2.me/theorems/1e68faa3-849f-4169-a155-4fd8abdc8c38
-- title:
--   $k$-wise independent random variables
-- statement:
--   Random variables $X_1, \dots, X_v$ on a probability space are **$k$-wise independent** if every subcollection of at most $k$ of them is mutually independent.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.3, p.28

import Mathlib

namespace LaconicBarrier

open MeasureTheory ProbabilityTheory

/-- Random variables `X₁, …, X_v` are **`k`-wise independent** (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), §4.3, p.28: "if every subcollection of at most `k`
variables is mutually independent"). -/
def KWiseIndep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {v : ℕ} (X : Fin v → Ω → ℝ)
    (k : ℕ) : Prop :=
  ∀ S : Finset (Fin v), S.card ≤ k → iIndepFun (fun i : S => X i) μ

end LaconicBarrier


