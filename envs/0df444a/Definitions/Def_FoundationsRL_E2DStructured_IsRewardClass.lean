-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
-- name    : FoundationsRL_E2DStructured_IsRewardClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:46.300994+00:00
-- url     : https://prove2.me/theorems/d1c90abd-6d33-457b-915f-9ec9c30a8866
-- title:
--   Reward function classes with measurable members and maximizers
-- statement:
--   A function class $\mathcal F\subseteq\{f:\Pi\to\mathbb R\}$ (Assumption 5) is a **reward class** when each $f\in\mathcal F$ is measurable and has a maximizer $\pi_f$.
--
--   This records the conditions under which the expressions of §4.2 are meaningful: $\mathbb E_{\pi\sim p}$ of $f$ for $p\in\Delta(\Pi)$, and $f(\pi_f)$.
--
--   **Formalization Note** No range condition is imposed, because Assumption 5 imposes none. Measurability is the standing convention of the notes.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Assumption 5, p. 57; §4.2, p. 65

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- A class `F ⊆ {f : Π → ℝ}` of mean-reward functions (Assumption 5, p. 57) for which the notation
of §4.2 makes sense: every `f ∈ F` is measurable and has a maximizer `π_f` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65).

**Formalization Note.** Measurability is the field's standing convention, needed for `E_{π∼p}` to
mean anything. The maximizer is what `π_f = arg max_π f(π)` presupposes. No range condition is
imposed: Assumption 5 allows every real-valued function. -/
def IsRewardClass {D : Type*} [MeasurableSpace D] (F : Set (D → ℝ)) : Prop :=
  ∀ f ∈ F, Measurable f ∧ ∃ π₀, ∀ π, f π ≤ f π₀

end FoundationsRL.E2DStructured


