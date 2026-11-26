-- Prove2me | Definitions.Def_Eden_ExteriorLimits
-- name    : Eden_ExteriorLimits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:31:55.286051+00:00
-- url     : https://prove2.me/theorems/591e91f8-d7bf-57be-8f80-a00d85e0fd17
-- title:
--   Exterior Limits
-- statement:
--   Definitions and structural lemmas for Exterior Limits, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorLimits.lean

import Definitions.Def_Eden_ExteriorGeometry
import Definitions.Def_Eden_LogarithmicSums
import Definitions.Def_Eden_FactorLimits
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_exteriorInitialCoordinates_ne_zero
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
namespace Eden
def exteriorRate (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) : ℝ :=
  ∑ i : Fin k, factorExponents c p (Set.powersetCard.ofFinEmbEquiv.symm s i)
def exteriorSupport (k : ℕ) (p : PhaseSpace) (v : ExteriorSpace k) : Finset (ExteriorIndex k) :=
  Finset.univ.filter (fun s => exteriorInitialCoordinates k p v s ≠ 0)
theorem exteriorSupport_nonempty {k : ℕ} (p : PhaseSpace) {v : ExteriorSpace k} (hv : v ≠ 0) :
    (exteriorSupport k p v).Nonempty := by
  classical
  have h := exteriorInitialCoordinates_ne_zero p hv
  by_contra hn
  apply h
  ext s
  have hnot : ¬s ∈ exteriorSupport k p v := fun hs => hn ⟨s, hs⟩
  simpa [exteriorSupport] using hnot
end Eden


