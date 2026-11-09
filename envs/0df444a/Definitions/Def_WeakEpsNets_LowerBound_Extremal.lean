-- Prove2me | Definitions.Def_WeakEpsNets_LowerBound_Extremal
-- name    : WeakEpsNets_LowerBound_Extremal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:54.89457+00:00
-- url     : https://prove2.me/theorems/eedb3b83-cd6d-4af9-9daa-2dab58f138df
-- title:
--   Minimum weak-net size and its worst-case supremum
-- statement:
--   For a finite nonempty $P\subset\mathbb R^d$ and $r\ge1$, define
--   $$f_d(P,r)=\min\{|X|:X\text{ is a finite weak }1/r\text{-net of }P\},\qquad f_d(r)=\sup_{P\text{ finite, nonempty}} f_d(P,r).$$
--   The minimum is attained: $P$ itself is a finite weak net. The definitions use extended natural numbers, so an empty collection of candidate nets has infimum $+\infty$, and an unbounded family of minima has supremum $+\infty$.
--
--   This supplies the source's extremal function without a real supremum's default on unbounded sets. The comparison in the goal embeds these values into the extended nonnegative reals, preserving infinity. The raw-input extension outside $P\ne\varnothing$, $r\ge1$ is not an assertion of the source.
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), §1, p. 2, lines 42–45; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Nets

noncomputable section

namespace WeakEpsNets.LowerBound

/-- Minimum finite weak-net cardinality, source p. 2. Empty feasible set gives infinity.
For nonempty P and r ≥ 1 the candidate X=P makes this a finite attained minimum. -/
def weakNetNumber {d : ℕ} (P : Finset (Fin d → ℝ)) (r : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ X : Finset (Fin d → ℝ), (X.card : ℕ∞) = n ∧ IsWeakNet P r X}

/-- Worst-case minimum over precisely the finite nonempty point sets, source p. 2.
An unbounded collection gives infinity, rather than a real supremum's default zero. -/
def f (d : ℕ) (r : ℝ) : ℕ∞ :=
  ⨆ P : {P : Finset (Fin d → ℝ) // P.Nonempty}, weakNetNumber P.val r

end WeakEpsNets.LowerBound


