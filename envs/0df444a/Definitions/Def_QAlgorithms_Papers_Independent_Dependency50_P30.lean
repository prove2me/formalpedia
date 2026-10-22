-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P30
-- name    : QAlgorithms_Papers_Independent_Dependency50_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T22:50:45.978386+00:00
-- url     : https://prove2.me/theorems/d47f9282-81e8-4b86-83bc-a2c49eb9d110
-- title:
--   Definitions for Energy-constrained two-way assisted private and quantum capacities of quantum channels
-- statement:
--   The objects that formalizations building on *Energy-constrained two-way assisted private and quantum capacities of quantum channels* (arXiv:1801.08102) are stated in. Every numbered result of this paper itself was deferred, so it has no mission of its own; its definitions are published for the papers that import them.
--
--   - `thermalEntropyBits`: Bosonic thermal entropy in bits, arXiv:1801.08102v3, PDF p.8, (63). The physical domain is `x >= 0`. The total real formula uses `0 log 0 = 0`; its values at negative inputs have no physical interpretation here.
--   - `pureAmplifierRateBound`: The scalar right-hand side of (172), arXiv:1801.08102v3, PDF p.19. This definition retains gain greater than one and nonnegative input photon number. It does not assert the operational capacity inequality of (172).
--   - `PureLossBroadcastParameters`: Physical transmissivity parameters for the vacuum pure-loss broadcast network, arXiv:1801.08102v3, PDF pp.26-27, before Theorem 13. The residual environmental transmissivity is one minus the sum. Zero receiver transmissivities and zero loss are allowed. This is parameter data, not a definition of the quantum channel.
--   - `pureLossBroadcastRateBound`: Scalar right-hand side of (251), arXiv:1801.08102v3, PDF p.27. The complement is taken among all receivers. The theorem concerns nonempty selected sets; the formula also gives zero for the empty set. No assertion about an operational rate region is built into this definition.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Papers.Independent.Dependency50.P30

import Mathlib

/-!
# Energy-constrained two-way assisted capacities (arXiv:1801.08102v3)

Paper-local scalar definitions only. All 27 planned result nodes are explicitly
deferred in this unit's HARD.md and GAPS.json. In particular, the formulas below
are not definitions of operational capacities or squashed entanglement.
The required trace-class, tensor, entropy, instrument, and Gaussian interfaces
have not been implemented. No finite-dimensional substitute is asserted.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P30

open scoped NNReal

/-- Bosonic thermal entropy in bits, arXiv:1801.08102v3, PDF p.8, (63).
The physical domain is `x >= 0`. The total real formula uses `0 log 0 = 0`;
its values at negative inputs have no physical interpretation here. -/
def thermalEntropyBits (x : ℝ) : ℝ :=
  (1 + x) * Real.logb 2 (1 + x) - x * Real.logb 2 x

/-- The scalar right-hand side of (172), arXiv:1801.08102v3, PDF p.19.
This definition retains gain greater than one and nonnegative input photon number.
It does not assert the operational capacity inequality of (172). -/
def pureAmplifierRateBound (gain : {G : ℝ // 1 < G}) (photonNumber : ℝ≥0) : ℝ :=
  thermalEntropyBits ((photonNumber : ℝ) * (gain.val + 1) / 2 + (gain.val - 1) / 2) -
    thermalEntropyBits (((photonNumber : ℝ) + 1) * (gain.val - 1) / 2)

/-- Physical transmissivity parameters for the vacuum pure-loss broadcast network,
arXiv:1801.08102v3, PDF pp.26-27, before Theorem 13. The residual environmental
transmissivity is one minus the sum. Zero receiver transmissivities and zero loss
are allowed. This is parameter data, not a definition of the quantum channel. -/
structure PureLossBroadcastParameters (m : ℕ) where
  transmissivity : Fin m → ℝ≥0
  total_le_one : (∑ i, transmissivity i) ≤ 1

/-- Scalar right-hand side of (251), arXiv:1801.08102v3, PDF p.27.
The complement is taken among all receivers. The theorem concerns nonempty
selected sets; the formula also gives zero for the empty set.
No assertion about an operational rate region is built into this definition. -/
def pureLossBroadcastRateBound {m : ℕ} (parameters : PureLossBroadcastParameters m)
    (selected : Finset (Fin m)) (photonNumber : ℝ≥0) : ℝ :=
  let selectedTransmission : ℝ := ∑ i ∈ selected, (parameters.transmissivity i : ℝ)
  let otherTransmission : ℝ :=
    ∑ i ∈ Finset.univ \ selected, (parameters.transmissivity i : ℝ)
  thermalEntropyBits ((photonNumber : ℝ) *
      (1 + selectedTransmission - otherTransmission) / 2) -
    thermalEntropyBits ((photonNumber : ℝ) *
      (1 - selectedTransmission - otherTransmission) / 2)

/-- Vacuum entropy: the zero term in (63) is interpreted by continuity. -/
example : thermalEntropyBits 0 = 0 := by
  simp [thermalEntropyBits]

/-- At zero input energy the two arguments in (172) coincide. -/
example (gain : {G : ℝ // 1 < G}) : pureAmplifierRateBound gain 0 = 0 := by
  simp [pureAmplifierRateBound]

/-- The parameter space admits the empty receiver list; result nodes require a
nonempty selected set, so no capacity theorem is asserted for this case. -/
example : PureLossBroadcastParameters 0 :=
  ⟨Fin.elim0, by simp⟩

/-- The finite-energy expression (251) vanishes at zero input energy. -/
example {m : ℕ} (parameters : PureLossBroadcastParameters m)
    (selected : Finset (Fin m)) :
    pureLossBroadcastRateBound parameters selected 0 = 0 := by
  simp [pureLossBroadcastRateBound]

/-- Selecting no receivers gives identical entropy arguments in (251). -/
example {m : ℕ} (parameters : PureLossBroadcastParameters m) (photonNumber : ℝ≥0) :
    pureLossBroadcastRateBound parameters ∅ photonNumber = 0 := by
  simp [pureLossBroadcastRateBound]

end QAlgorithms.Papers.Independent.Dependency50.P30


