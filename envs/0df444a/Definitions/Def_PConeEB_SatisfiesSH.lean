-- Prove2me | Definitions.Def_PConeEB_SatisfiesSH
-- name    : PConeEB_SatisfiesSH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:27.232227+00:00
-- url     : https://prove2.me/theorems/c20ac284-7f10-4d10-b541-480bcdec5a0b
-- title:
--   Partial sub-homogeneity (SH)
-- statement:
--   A function $\mathfrak g$ satisfies the **partial sub-homogeneity** condition (SH) if there is $S>0$ such that $s\in[0,S]$ and $\hat\tau\ge1$ together imply
--   $$
--   \mathfrak g(\hat\tau s)\le\hat\tau\,\mathfrak g(s).
--   $$
--   Every concave $\mathfrak g$ with $\mathfrak g(0)=0$ satisfies it.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (SH), p.11

import Mathlib

namespace PConeEB

/-- The partial sub-homogeneity (SH): there is `S > 0` such that `s ∈ [0, S]` and `τ ≥ 1` imply
`g(τ s) ≤ τ g(s)`. Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (SH), p.11. -/
def SatisfiesSH (g : ℝ → ℝ) : Prop :=
  ∃ S : ℝ, 0 < S ∧ ∀ s ∈ Set.Icc 0 S, ∀ τ : ℝ, 1 ≤ τ → g (τ * s) ≤ τ * g s

end PConeEB


