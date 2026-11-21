-- Prove2me | Definitions.Def_mcorr_misiurewicz
-- name    : mcorr_misiurewicz
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T23:20:03.41928+00:00
-- url     : https://prove2.me/theorems/f8bcd242-5e5b-4dbe-b3a6-0dfa2e5daa59
-- title:
--   Misiurewicz points, repelling cycles, and the Julia set of a correspondence
-- statement:
--   A sequence is strictly preperiodic if it is eventually periodic but not periodic. A parameter $a$ is Misiurewicz (`IsMisiurewicz`) if the critical point $0$ has a unique bounded forward orbit under $\mathbf{f}_a$ and that orbit is strictly preperiodic (Definition 1.2). A cycle of period $n$ is an $n$-periodic forward orbit; its multiplier (`cycleMultiplier`) is the product of the branch derivatives $\frac{p}{q}z_i^{p-1}/(z_{i+1}-c)^{q-1}$ along one period (implicit differentiation and the chain rule), and it is repelling (`IsRepellingCycle`) if it avoids $0$ and the multiplier has norm $>1$. The Julia set $J_c$ (`juliaSet`) is the closure of the union of all repelling cycles (Definition 2.1). `IsMisiurewiczOrbitData` bundles the canonical orbit-and-branch data of a Misiurewicz parameter: the unique bounded orbit, preperiod $\ell\ge1$ and minimal period $n$, the univalent branches along it, and the associated repelling cycle.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Definition 1.2, Section 2.1, Definition 2.1, Section 3 (eq. 3.4), Remark 3.1.

import Mathlib
import Definitions.Def_mcorr_family

open Set Filter Topology Finset

namespace MultibrotCorr

/-- A sequence is strictly preperiodic: eventually periodic but not periodic
(paper, Definition 1.2 and Section 1.4). -/
def IsStrictlyPreperiodic (z : ℕ → ℂ) : Prop :=
  (∃ ℓ n : ℕ, 0 < n ∧ ∀ i ≥ ℓ, z (i + n) = z i) ∧
  ¬ (∃ n : ℕ, 0 < n ∧ ∀ i, z (i + n) = z i)

/-- A Misiurewicz point: the critical point 0 has a unique bounded forward orbit, and that orbit
is strictly preperiodic (paper, Definition 1.2). -/
def IsMisiurewicz (e : UnicriticalExponent) (a : ℂ) : Prop :=
  ∃ z, IsForwardOrbit e a 0 z ∧ (∃ R, ∀ i, ‖z i‖ ≤ R) ∧ IsStrictlyPreperiodic z ∧
    ∀ w, IsForwardOrbit e a 0 w → (∃ R, ∀ i, ‖w i‖ ≤ R) → w = z

/-- A cycle of period n: an n-periodic forward orbit (paper, Section 2.1). -/
def IsCycle (e : UnicriticalExponent) (c : ℂ) (n : ℕ) (z : ℕ → ℂ) : Prop :=
  0 < n ∧ (∀ i, z (i + n) = z i) ∧ ∀ i, z (i + 1) ∈ unicriticalCorr e.p e.q c (z i)

/-- The derivative at zprev of the univalent branch of f_c sending zprev to znext, by implicit
differentiation of (w-c)^q = z^p: (p/q) zprev^(p-1) / (znext-c)^(q-1). -/
noncomputable def branchDerivFactor (e : UnicriticalExponent) (c zprev znext : ℂ) : ℂ :=
  (e.p : ℂ) / (e.q : ℂ) * zprev ^ (e.p - 1) / (znext - c) ^ (e.q - 1)

/-- The multiplier of a period-n cycle: the derivative at the base point of the composition of
the univalent branches along one period, equal by the chain rule to the product of the branch
derivatives (paper, Section 2.1). -/
noncomputable def cycleMultiplier (e : UnicriticalExponent) (c : ℂ) (n : ℕ) (z : ℕ → ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, branchDerivFactor e c (z i) (z (i + 1))

/-- A repelling cycle: a cycle avoiding the critical point 0 whose multiplier has norm > 1
(paper, Section 2.1; critical cycles are super-attracting by convention, never repelling). -/
def IsRepellingCycle (e : UnicriticalExponent) (c : ℂ) (n : ℕ) (z : ℕ → ℂ) : Prop :=
  IsCycle e c n z ∧ (∀ i, z i ≠ 0) ∧ 1 < ‖cycleMultiplier e c n z‖

/-- The Julia set J_c: the closure of the union of all repelling cycles (paper, Definition 2.1). -/
def juliaSet (e : UnicriticalExponent) (c : ℂ) : Set ℂ :=
  closure {w | ∃ (n : ℕ) (z : ℕ → ℂ), IsRepellingCycle e c n z ∧ ∃ i, z i = w}

/-- The canonical orbit-and-branch data attached to a Misiurewicz parameter a (paper, Section 3,
eq. (3.4), Remark 3.1): the unique bounded orbit of 0, its preperiod l and period n, the univalent
branches along it, and the associated repelling cycle. The orbit starts at z 0 = a. -/
def IsMisiurewiczOrbitData (e : UnicriticalExponent) (a : ℂ)
    (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) : Prop :=
  1 ≤ ℓ ∧ 0 < n ∧ z 0 = a ∧
  (∀ j, z (j + 1) ∈ unicriticalCorr e.p e.q a (z j)) ∧
  (∀ j, z j ≠ 0) ∧
  (∀ j, IsOpen (U j) ∧ z j ∈ U j ∧ IsUnivalentBranch e 0 (U j) (φ j) ∧
    φ j (z j) + a = z (j + 1)) ∧
  IsForwardOrbit e a 0 (zeroOrbit z) ∧
  (∃ R, ∀ j, ‖zeroOrbit z j‖ ≤ R) ∧
  (∀ w, IsForwardOrbit e a 0 w → (∃ R, ∀ j, ‖w j‖ ≤ R) → w = zeroOrbit z) ∧
  IsStrictlyPreperiodic (zeroOrbit z) ∧
  (∀ j ≥ ℓ, z (j + n) = z j) ∧ (∀ j ≥ ℓ, φ (j + n) = φ j) ∧
  (∀ j < ℓ, ∀ k ≥ ℓ, z j ≠ z k) ∧
  (∀ m, 0 < m → m < n → ∃ i ≥ ℓ, z (i + m) ≠ z i) ∧
  IsRepellingCycle e a n (fun j => z (ℓ + j))

end MultibrotCorr


