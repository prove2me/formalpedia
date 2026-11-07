-- Prove2me | Definitions.Def_FourColorLinear_greedyPotential
-- name    : FourColorLinear_greedyPotential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:02.756536+00:00
-- url     : https://prove2.me/theorems/76293541-75ab-4341-8f59-9ab6196dae14
-- title:
--   The conditional expectation (1) in the greedy choice of swaps
-- statement:
--   Fix rings with a preferred swap on each chain they intersect. Given a set of decided chains and their decisions, a ring is **live** if it has the chosen pairing and all decided chains intersecting it agree with its wishes. The potential is the conditional expected number of survivors,
--   $$\sum_{R_i\text{ live}}2^{-u_i},$$
--   where $u_i$ is the number of undecided chains intersecting $R_i$. This is display (1) of the paper; the derandomization makes decisions that never decrease it.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), Proof of Lemma 4, (1), p.7

import Mathlib

namespace FourColorLinear

variable {ι χ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq χ]

open Classical in
/-- The rings still live in the greedy choice of arXiv:2610.39753 (held version, sha256 4dce39c5…),
Proof of Lemma 4, p.7: "Only the rings that get their color combination stay alive"; "A ring Ri only
stays live as long as all decided swaps were as it wanted them." `Dec` is the set of decided chains,
`val` the decisions, `τ i` the chains intersecting ring `i`, `σ i` the swaps it wants, `alive₀`
the rings with the chosen pairing. -/
noncomputable def liveRings (alive₀ : Finset ι) (τ : ι → Finset χ) (σ : ι → χ → Bool)
    (Dec : Finset χ) (val : χ → Bool) : Finset ι :=
  alive₀.filter fun i => ∀ x ∈ τ i ∩ Dec, val x = σ i x

/-- The conditional expectation (1) of arXiv:2610.39753, p.7: "conditioned on decisions made, the
expected number of survivors is Σ_{Ri is still live} 2^{−ui}, where ui is the number of undecided
chains intersecting Ri". -/
noncomputable def greedyPotential (alive₀ : Finset ι) (τ : ι → Finset χ) (σ : ι → χ → Bool)
    (Dec : Finset χ) (val : χ → Bool) : ℚ :=
  ∑ i ∈ liveRings alive₀ τ σ Dec val, (1 / 2 : ℚ) ^ (τ i \ Dec).card

end FourColorLinear


