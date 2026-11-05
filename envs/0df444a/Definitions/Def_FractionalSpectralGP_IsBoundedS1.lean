-- Prove2me | Definitions.Def_FractionalSpectralGP_IsBoundedS1
-- name    : FractionalSpectralGP_IsBoundedS1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:39.063681+00:00
-- url     : https://prove2.me/theorems/1e13c3c0-0351-4234-b411-d7c7b1d7d5b9
-- title:
--   Bounded subsets of $S_1$
-- statement:
--   A set $B$ of formal series is **bounded in $S_1$** if $B\subset S_1$ and, for every $k$, $\sup_{g\in B}|||g|||_k<\infty$.
--
--   These are the sets on which uniform convergence defines the strong topology of $S_{-1}$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, p.11

import Mathlib
import Definitions.Def_FractionalSpectralGP_MemS1
import Definitions.Def_FractionalSpectralGP_s1Norm

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- A bounded subset of the Kondratiev space `S₁` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, §4, p.11): a set of elements
of `S₁` that is bounded in every norm `|||·|||_k`. This is boundedness in the projective limit
topology of `S₁ = ⋂_k 𝓗_k`. -/
def IsBoundedS1 (B : Set ((ℕ →₀ ℕ) → ℂ)) : Prop :=
  (∀ g ∈ B, MemS1 g) ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ g ∈ B, s1Norm k g ≤ C

end FractionalSpectralGP


