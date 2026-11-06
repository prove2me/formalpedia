-- Prove2me | Definitions.Def_BorelRobustMDP_Bb
-- name    : BorelRobustMDP_Bb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:17.785497+00:00
-- url     : https://prove2.me/theorems/0907787b-4b31-41f2-a99d-528b768e06e8
-- title:
--   The function spaces $\mathbb B_b$ and $\mathbb B$
-- statement:
--   For the bounding function $b$, $\mathbb B_b$ is the set of measurable $v:E\to\mathbb R$ with $|v(x)|\le\lambda b(x)$ for all $x$, for some $\lambda\ge0$, and $\mathbb B$ is the set of lower semicontinuous $v\in\mathbb B_b$.
--
--   $\mathbb B$ is the set of possible value functions under Markov policies.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, p.7 and p.9

import Mathlib

namespace BorelRobustMDP

universe u

variable {E : Type u} [MeasurableSpace E] [TopologicalSpace E]

/-- `𝔹_b = {v : E → ℝ | v measurable with λ ∈ ℝ₊ s.t. |v(x)| ≤ λ b(x) for all x ∈ E}` (Bäuerle &
Glauner, arXiv:2007.13103v1, p.7). -/
def Bb (b : E → ℝ) : Set (E → ℝ) :=
  {v | Measurable v ∧ ∃ l : ℝ, 0 ≤ l ∧ ∀ x, |v x| ≤ l * b x}

/-- `𝔹 = {v ∈ 𝔹_b : v lower semicontinuous}` (Bäuerle & Glauner, arXiv:2007.13103v1, p.9). -/
def BB (b : E → ℝ) : Set (E → ℝ) :=
  {v | v ∈ Bb b ∧ LowerSemicontinuous v}

end BorelRobustMDP


