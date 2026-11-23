-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:36.505342+00:00
-- url     : https://prove2.me/theorems/ae360cec-4f36-45c8-8620-755032ea2faa
-- title:
--   Dens GSDvr
-- statement:
--   Definitions and structural lemmas for Dens GSDvr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/DensGSDvr.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
section Dvr
variable (F : Type) [Field F] [ValuativeRel F]
def resF (x : F) : 𝓀[F] := if h : x ∈ 𝒪[F] then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0
def liftF (c : 𝓀[F]) : F := ((IsLocalRing.residue_surjective c).choose : 𝒪[F])
def SatF {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) : Prop :=
  ∀ u : Fin n → F, (∀ k, u k ∈ 𝒪[F]) → (∃ c : ι → F, ∑ i, c i • X i = u) →
    ∃ c : ι → F, (∀ i, c i ∈ 𝒪[F]) ∧ ∑ i, c i • X i = u
def redM {ι : Type} {n : ℕ} (X : ι → Fin n → F) : ι → Fin n → 𝓀[F] := fun i k => resF F (X i k)
variable {F}
end Dvr
end PI.UnitaryGroupMassFormula.CntFormula


