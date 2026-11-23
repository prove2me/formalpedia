-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:34.878404+00:00
-- url     : https://prove2.me/theorems/4c404138-2832-48bb-aa5c-0ab93fcb3905
-- title:
--   Lattice Finitely Generated
-- statement:
--   Definitions and structural lemmas for Lattice Finitely Generated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/LatticeFinitelyGenerated.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
section ConjP
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def starO (K : Type) [Field K] [NumberField K] [StarRing K] : 𝓞 K ≃+* 𝓞 K :=
  RingOfIntegers.mapRingEquiv (starRingAut : K ≃+* K)
lemma starO_coe (a : 𝓞 K) : ((starO K a : 𝓞 K) : K) = star (a : K) := rfl
lemma starO_starO (a : 𝓞 K) : starO K (starO K a) = a := by
  apply RingOfIntegers.ext
  rw [starO_coe, starO_coe, star_star]
def conjW (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (starO K)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro hb
    apply w.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : starO K x ∈ w.asIdeal.comap (starO K) := by
      show starO K (starO K x) ∈ w.asIdeal
      rwa [starO_starO]
    rw [hb, Ideal.mem_bot] at h1
    rw [Ideal.mem_bot]
    have h2 := congrArg (starO K) h1
    rwa [starO_starO, map_zero] at h2
end ConjP
section Norm
variable {K : Type} [Field K] [NumberField K]
end Norm
section abelian₂
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end abelian₂
section Idx
open Formalism.HermitianLatticesTheory
variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']
end Idx
section Add
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Add
section Gam
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def combo {d : ℕ} (y : Fin d → V) : (Fin d → K) →ₗ[K] V where
  toFun c := ∑ i, c i • y i
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
    smul_smul]
end Gam
end PI.DvRows


