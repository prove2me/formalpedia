-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighHeightWindow
-- name    : TaoFivePrimes_RHHighHeightWindow
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T09:43:26.179876+00:00
-- url     : https://prove2.me/theorems/a6c2f1c0-ebca-49a2-a918-19add088bc69
-- title:
--   TaoFivePrimes_RHHighHeightWindow
-- statement:
--   Transparent critical-line normalization, closed strip-window zero set, and proposed 128-unit test interval [3289999872,3290000000]. No numerical accuracy, zero count or RH assertion.
-- source:
--   Direct normalization and Mathlib completed-zeta functional equation, with conjugation proved via the Mellin kernel. Kernel conjugation follows the ordinary proof in the accepted xi/theta work of sometik179 (c9908072-d99a-4431-aad8-a72c6352619a; repaired accepted pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a), with theta/Mellin attribution to Gabewhigham. Exponential normalization is used in Platt-style high-height batch methods.

/- High-height certificate interfaces. The surrounding xi/theta project credits
sometik179 and Gabewhigham. Normalization follows Platt's batch method.
These are ordinary mathematical definitions, with no accuracy or RH assertion. -/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Set.Card
set_option autoImplicit false
namespace RHHighHeight
noncomputable def critical (t : ℝ) : ℂ := 1/2 + (t:ℂ)*Complex.I
noncomputable def normalizedComplex (t : ℝ) : ℂ :=
  (Real.exp (Real.pi*t/4):ℂ)*completedRiemannZeta (critical t)
noncomputable def normalized (t : ℝ) : ℝ := (normalizedComplex t).re
noncomputable def windowZeros (a b : ℝ) : Set ℂ :=
  {s | riemannZeta s=0 ∧ 0<s.re ∧ s.re<1 ∧ a≤s.im ∧ s.im≤b}
end RHHighHeight
noncomputable def TaoFivePrimes_RHHighHeightWindow : ℝ × ℝ :=
  (3289999872,3290000000)


