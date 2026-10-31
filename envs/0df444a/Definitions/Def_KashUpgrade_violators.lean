-- Prove2me | Definitions.Def_KashUpgrade_violators
-- name    : KashUpgrade_violators
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:46.524256+00:00
-- url     : https://prove2.me/theorems/de71296c-8439-4795-ba81-7d3500cb79e9
-- title:
--   The set $S$ of OptimalLumping
-- statement:
--   The set of out-of-order indices in OptimalLumping:
--   $$
--   S=\{k:\exists k'\ \text{s.t.}\ 1\le k<k'\le n\wedge\gamma^j_{j+k}>\gamma^j_{j+k'}\}.
--   $$
--   The same set is used in Lemma 3 with the first-order thresholds in place of $\gamma$.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19; Lemma 3, p.18

import Mathlib

namespace KashUpgrade

/-- **The set `S` of Algorithm 1.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Algorithm 1, p.19:
`S ← {k : ∃ k' s.t. 1 ≤ k < k' ≤ n ∧ γ_{j+k} > γ_{j+k'}}`. -/
noncomputable def violators (j n : ℕ) (γ : ℕ → ℝ) : Finset ℕ :=
  open Classical in
  (Finset.Icc 1 n).filter fun k => ∃ k', k < k' ∧ k' ≤ n ∧ γ (j + k') < γ (j + k)

end KashUpgrade


