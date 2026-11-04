-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
-- name    : Submission_ThreeSumApsp_Util_Asymptotics_UpperBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:04:14.274531+00:00
-- url     : https://prove2.me/theorems/d2faa205-7b21-4e5c-913b-c6103e9d46fa
-- title:
--   Upper Bounds
-- statement:
--   Definitions and structural lemmas for Upper Bounds, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/UpperBounds.lean

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
set_option autoImplicit false
section
open Filter Asymptotics
namespace ThreeSumApsp
def UpperBigOPow (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop, f n ≤ C * (n : ℝ) ^ a
def UpperPowPolylog (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ (C : ℝ) (e : ℕ), ∀ᶠ n : ℕ in Filter.atTop, f n ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)
def UpperPowLittleO (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ᶠ n : ℕ in Filter.atTop, f n ≤ (n : ℝ) ^ (a + ε n)
variable {f f' g : ℕ → ℝ} {a b : ℝ}
namespace UpperBigOPow
end UpperBigOPow
namespace UpperPowPolylog
end UpperPowPolylog
namespace UpperPowLittleO
end UpperPowLittleO
end ThreeSumApsp


