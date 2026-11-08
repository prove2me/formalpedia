-- Prove2me | Definitions.Def_HardcoreSlices_pairingNbr
-- name    : HardcoreSlices_pairingNbr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:00.68738+00:00
-- url     : https://prove2.me/theorems/d21f2e30-1eac-4e12-bbd7-41005eb4c914
-- title:
--   The bipartite pairing model
-- statement:
--   In the **bipartite pairing model** on sides of size $m$, a uniformly random perfect matching pairs the stubs $X\times[\Delta]$ with the stubs $Y\times[\Delta]$. Then $N_\pi(\tau)$ is the set of $y$ with a stub matched to a stub of a vertex of $\tau$. The module defines this set, the probability and expectation under the uniform matching, and the variance proxy
--   $$v=\frac14\cdot\frac1{1-\bigl(1-\frac{\Delta-1}{\Delta|Y|}\bigr)^2}$$
--   from the display on p.14.
--
--   **Formalization Note** A perfect matching of the stubs is a permutation of `Fin m × Fin Δ`, and probabilities count permutations.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Definition 2.2, p.10; display on p.14

import Mathlib

open Classical

namespace HardcoreSlices

/-- The neighbourhood `N_π(τ)` in the bipartite pairing model. Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), Definition 2.2, p.10.

A perfect matching between the stubs `X × [∆]` and `Y × [∆]` is a permutation `π` of `Fin m × Fin Δ`, with `π (x, i) = (y, j)`
when `(x, i)` and `(y, j)` are matched. -/
def pairingNbr {m Δ : ℕ} (π : Equiv.Perm (Fin m × Fin Δ)) (τ : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun y => ∃ x ∈ τ, ∃ i j, π (x, i) = (y, j))

/-- The probability of an event under the uniform perfect matching of the stubs (step 2 of Definition 2.2, p.10). -/
noncomputable def pairingProb {m Δ : ℕ} (P : Equiv.Perm (Fin m × Fin Δ) → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card (Equiv.Perm (Fin m × Fin Δ)) : ℝ)

/-- `E|N(τ)|` under the uniform perfect matching of the stubs. -/
noncomputable def pairingMeanNbr {m Δ : ℕ} (τ : Finset (Fin m)) : ℝ :=
  (∑ π : Equiv.Perm (Fin m × Fin Δ), ((pairingNbr π τ).card : ℝ)) /
    (Fintype.card (Equiv.Perm (Fin m × Fin Δ)) : ℝ)

/-- The explicit variance proxy of the display on p.14: `(1/4) · 1 / (1 − (1 − (∆−1)/(∆|Y|))²)`. -/
noncomputable def pairingVariance (m Δ : ℕ) : ℝ :=
  (1 / 4) * (1 / (1 - (1 - ((Δ : ℝ) - 1) / ((Δ : ℝ) * m)) ^ 2))

end HardcoreSlices


