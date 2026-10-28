-- Prove2me | Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions
-- name    : D1Bound5_PellConvergentCompleteness_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:23:47.088782+00:00
-- url     : https://prove2.me/theorems/82a1b1ec-0a2e-4a68-96ca-007246f49f07
-- title:
--   Pell Convergent Completeness
-- statement:
--   Integral numerator and denominator before rational normalization. The recursion follows the real complete quotients; below we prove that these integers are already relatively prime and positive. The named objects in this bundle include `pellConvergentPair`.
-- source:
--   D1Bound5/PellConvergentCompleteness.lean, lines 10-17, SHA-256 c43074daa228222fbe1ca798070304a8be11d05710c382ec9a9e73d7799c8266. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

section
namespace D1Bound5

/-- Integral numerator and denominator before rational normalization. The
recursion follows the real complete quotients; below we prove that these
integers are already relatively prime and positive. -/
noncomputable def pellConvergentPair (x : ℝ) : ℕ → ℤ × ℤ
  | 0 => (⌊x⌋, 1)
  | n+1 =>
      let t := pellConvergentPair (Int.fract x)⁻¹ n
      (⌊x⌋ * t.1 + t.2, t.1)





















end D1Bound5
end


