-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
-- name    : GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:08.008843+00:00
-- url     : https://prove2.me/theorems/f508f444-36b8-5268-8633-9330c253d2af
-- title:
--   Local Herbrand
-- statement:
--   Definitions and structural lemmas for Local Herbrand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_Global_valued_adicCompletionRingHomOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
namespace GroundTheory.Global
section ChangeOfGroup
variable {k H G V W : Type*} [CommRing k] [Group H] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ' : Representation k H V} {ρ : Representation k G W}
theorem cycSubOne_mulEquiv (e : H →* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (τ : H) (x : V) : f (cycSubOne ρ' τ x) = cycSubOne ρ (e τ) (f x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, hf]
variable [Fintype H] [Fintype G]
theorem cycNorm_mulEquiv (e : H ≃* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (x : V) : f (cycNorm ρ' x) = cycNorm ρ (f x) := by
  rw [cycNorm_apply, cycNorm_apply, map_sum]
  simp_rw [hf]
  exact Fintype.sum_equiv e.toEquiv _ _ fun _ ↦ rfl
def cycTateZeroEquivOfMulEquiv (e : H ≃* G) (f : V ≃+ W) (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x))
    (τ : H) : CycTateZero ρ' τ ≃+ CycTateZero ρ (e τ) :=
  kerModRangeCongr f (cycSubOne_mulEquiv e.toMonoidHom f hf τ) (cycNorm_mulEquiv e f hf)
def cycTateNegOneEquivOfMulEquiv (e : H ≃* G) (f : V ≃+ W)
    (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x)) (τ : H) :
    CycTateNegOne ρ' τ ≃+ CycTateNegOne ρ (e τ) :=
  kerModRangeCongr f (cycNorm_mulEquiv e f hf) (cycSubOne_mulEquiv e.toMonoidHom f hf τ)
end ChangeOfGroup
section DecompositionAction
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
instance decompositionMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletion L) where
  smul σ x := adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x
  one_smul x := by
    change adicCompletionRingHomOf w 1 _ x = RingHom.id _ x
    congr 1
    exact ringHom_ext_adicCompletion w (continuous_adicCompletionRingHomOf _ _) continuous_id
      fun y ↦ by rw [adicCompletionRingHomOf_algebraMap]; rfl
  mul_smul σ τ x := by
    change adicCompletionRingHomOf w (σ * τ).1 (smul_asIdeal_of_mem_stabilizer w (σ * τ)) x =
      ((adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
        (adicCompletionRingHomOf w τ.1 (smul_asIdeal_of_mem_stabilizer w τ))) x
    congr 1
    exact ringHom_ext_adicCompletion w (continuous_adicCompletionRingHomOf _ _)
      ((continuous_adicCompletionRingHomOf σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
        (continuous_adicCompletionRingHomOf τ.1 (smul_asIdeal_of_mem_stabilizer w τ)))
      fun y ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap, adicCompletionRingHomOf_algebraMap]
        rfl
  smul_zero σ := map_zero _
  smul_add σ := map_add _
  smul_one σ := map_one _
  smul_mul σ := map_mul _
variable {w}
theorem valued_decomposition_smul (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletion L) : Valued.v (σ • x) = Valued.v x :=
  valued_adicCompletionRingHomOf _ _ x
variable (w)
instance decompositionMulSemiringActionIntegers :
    MulSemiringAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L) where
  smul σ x := ⟨σ • (x : w.adicCompletion L), by
    rw [mem_adicCompletionIntegers, valued_decomposition_smul]
    exact x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : w.adicCompletion L))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : w.adicCompletion L))
  smul_zero σ := Subtype.ext (smul_zero σ)
  smul_add σ x y := Subtype.ext (smul_add σ (x : w.adicCompletion L) y)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (MulSemiringAction.smul_mul σ (x : w.adicCompletion L) y)
instance decompositionUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletion L)ˣ :=
  Units.mulDistribMulActionRight
instance decompositionIntegerUnitsAction :
    MulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ :=
  Units.mulDistribMulActionRight
variable {w}
end DecompositionAction
section Units
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
end Units
section UnitsCard
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
def adicCompletionIntegersEquivInteger :
    w.adicCompletionIntegers L ≃+* 𝒪[w.adicCompletion L] where
  toFun x := ⟨x, (mem_valuationInteger_iff w (x : w.adicCompletion L)).2 x.2⟩
  invFun y := ⟨y, (mem_valuationInteger_iff w (y : w.adicCompletion L)).1 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
def integerUnitsAddEquiv :
    Additive (w.adicCompletionIntegers L)ˣ ≃+ Additive 𝒪[w.adicCompletion L]ˣ :=
  MulEquiv.toAdditive (Units.mapEquiv (adicCompletionIntegersEquivInteger w).toMulEquiv)
variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
end UnitsCard
section Unramified
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
end Unramified
end GroundTheory.Global


