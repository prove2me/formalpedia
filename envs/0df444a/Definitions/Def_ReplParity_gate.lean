-- Prove2me | Definitions.Def_ReplParity_gate
-- name    : ReplParity_gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:49.746894+00:00
-- url     : https://prove2.me/theorems/3daab6ed-196a-4f4f-8923-0450e64b0365
-- title:
--   The replicable gate (proof of Lemma 3.3)
-- statement:
--   Fix a subspace $V$ and $0<q,\eta<1$. The gate uses $N_g=\lceil512/(q\eta^2)\rceil$ samples. Let $\hat p$ be the fraction of these samples outside $V$, and let $B$ be the least power of two with $B\ge16/\eta$. The seed is a uniform $J\in\{0,\dots,B-1\}$ shared by all runs, and the gate continues exactly when
--   $$\hat p\ \ge\ \theta=\frac q2+\frac{q\,(J+1/2)}{4B},$$
--   and skips otherwise. The thresholds lie on a grid of spacing $q/(4B)$ inside $[q/2,3q/4]$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Lemma 3.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

/-- `N_g = ⌈512/(qη²)⌉`, the sample size of the gate (Lemma 3.3, p.17). -/
noncomputable def gateN (q η : ℝ) : ℕ := ⌈512 / (q * η ^ 2)⌉₊

/-- Every real number is at most some power of two. -/
theorem exists_le_two_pow (x : ℝ) : ∃ k : ℕ, x ≤ 2 ^ k :=
  let ⟨k, hk⟩ := pow_unbounded_of_one_lt x one_lt_two
  ⟨k, hk.le⟩

open Classical in
/-- `B`, the least power of two with `B ≥ 16/η` (proof of Lemma 3.3, p.17). -/
noncomputable def gateB (η : ℝ) : ℕ := 2 ^ Nat.find (exists_le_two_pow (16 / η))

/-- The threshold `θ = q/2 + q(J + 1/2)/(4B)` for the seed value `J` (proof of Lemma 3.3, p.17). -/
noncomputable def gateTheta (q η : ℝ) (J : ℕ) : ℝ := q / 2 + q * (J + 1 / 2) / (4 * gateB η)

open Classical in
/-- **The replicable gate (proof of Lemma 3.3).** Shen, Zhong, *Replicable Parity Learning: Cubic
Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), proof of Lemma 3.3, p.17 (PDF p.19): "Let p̂ be the fraction of the N_g samples outside
V, and let B be the least power of two with B ≥ 16/η. The test draws a shared uniform
J ∈ {0, . . . , B − 1} and continues exactly when p̂ ≥ θ = q/2 + q(J + 1/2)/(4B)".

`gate q η V S J = true` means "continue" and `false` means "skip"; `S` is the block of `N_g`
samples and `J ∈ Fin B` the seed. -/
noncomputable def gate {n : ℕ} (q η : ℝ) (V : Subsp n) (S : Fin (gateN q η) → Vec n)
    (J : Fin (gateB η)) : Bool :=
  decide (gateTheta q η J ≤ ((Finset.univ.filter (fun i => S i ∉ V)).card : ℝ) / gateN q η)

end ReplParity


