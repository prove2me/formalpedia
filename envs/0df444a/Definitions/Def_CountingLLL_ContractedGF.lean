-- Prove2me | Definitions.Def_CountingLLL_ContractedGF
-- name    : CountingLLL_ContractedGF
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:30:22.556705+00:00
-- url     : https://prove2.me/theorems/f628ff2e-6b89-4588-9d3a-51f67c2c672e
-- title:
--   Generating function of contracted-walk upward moves
-- statement:
--   For the absorbed contracted walk, count the upward moves before the first hit of zero and define their probability generating function $G_\theta(z)=\mathbb E[z^K]$ for a walk started at level one. A nonabsorbing path receives the default count zero; the separately proved absorption result makes this convention null when $\theta<1/3$.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk

set_option autoImplicit false

/-! The stopped upward-step count and its generating function for the absorbed
contracted walk of #442 Lemma 6.5. The fallback value on a nonabsorbing path is
zero; for θ < 1/3 that event is null by the absorption theorem. -/
namespace CountingLLL.ContractedWalk

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable def stopTime (ω : Tape) (start : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, level ω start t = 0 then Nat.find h else 0

noncomputable def upwardCount (ω : Tape) (start : ℕ) : ℕ := by
  classical
  exact ∑ t ∈ Finset.range (stopTime ω start), if level ω start t ≠ 0 ∧ ω t = true then 1 else 0

/-- The probability generating function of upward moves before the walk from one hits zero. -/
noncomputable def generatingFunction (θ : ℝ) (z : ℝ) : ℝ :=
  ∫ ω, z ^ upwardCount ω 1 ∂tapeLaw (ENNReal.ofReal θ)

end CountingLLL.ContractedWalk


