-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:46.032694+00:00
-- url     : https://prove2.me/theorems/a5f6a501-607a-45c0-9474-ccbaa2c551af
-- title:
--   Is Heat Th H
-- statement:
--   Definitions and structural lemmas for Is Heat Th H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.ExpSum
section General
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}
end General
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
theorem expo_eq (x : Matrix (Fin n) (Fin N) E) (Z : CF Ψ N N) (z z' : CF Ψ n N) :
    expo Ψ x Z z z' = ∑ τ : Ψ, ∑ k, (∑ a, ∑ b, τ.1 (x k a) * (Z τ a b * conj (τ.1 (x k b))) +
      ∑ a, τ.1 (x k a) * z τ k a + ∑ a, z' τ k a * conj (τ.1 (x k a))) := by
  simp only [expo, dotProduct, mulVec, Finset.mul_sum]
noncomputable def form (x : Matrix (Fin n) (Fin N) E) :
    (CF Ψ N N × CF Ψ n N × CF Ψ n N) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => 2 * π * I * expo Ψ x p.1 p.2.1 p.2.2
      map_add' := fun p q => by
        simp only [expo_eq, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        simp only [expo_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        · congr 1
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => by ring
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring }
open Classical in

noncomputable def dir {m : ℕ} (τ : Ψ) (k : Fin m) (a : Fin N) : CF Ψ m N :=
  fun σ i j => if σ = τ then if i = k then if j = a then 1 else 0 else 0 else 0
end GlobalTheory.SW.ExpSum


